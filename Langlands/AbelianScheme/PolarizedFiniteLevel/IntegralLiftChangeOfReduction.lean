import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.PrimitivePolarizationTransport
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Integral polarized lifting under an isomorphism of reduction bases -/

universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

variable {S T Q : Scheme.{u}} (b : T ⟶ S) (c : Q ⟶ T) (q : Q ⟶ S) (h : c ≫ b = q)

private def directSuccessiveIso : baseChange q ≅ baseChange b ⋙ baseChange c :=
  eqToIso (congrArg baseChange h.symm) ≪≫ baseChangeCompNatIso b c

/-- Pullback by an isomorphism of schemes is an equivalence of the categories
of actual abelian schemes. -/
def baseChangeEquivalence (i : Q ≅ T) : AbelianScheme T ≌ AbelianScheme Q :=
  CategoryTheory.Equivalence.mk (baseChange i.hom) (baseChange i.inv)
    ((directSuccessiveIso i.hom i.inv (𝟙 T) i.inv_hom_id).symm ≪≫ baseChangeIdNatIso).symm
    ((directSuccessiveIso i.inv i.hom (𝟙 Q) i.hom_inv_id).symm ≪≫ baseChangeIdNatIso)

variable (P : Prerequisites.{u})

private lemma transportMap_trans {X Y Z : AbelianScheme Q} (a : X ≅ Y) (d : Y ≅ Z)
    (X' : DualWitness X) (Y' : DualWitness Y) (Z' : DualWitness Z) (l : Z ⟶ Z'.dual P) :
    DualWitness.transportMap P (a ≪≫ d) X' Z' l =
      DualWitness.transportMap P a X' Y' (DualWitness.transportMap P d Y' Z' l) := by
  simp only [DualWitness.transportMap, Iso.trans_hom, Category.assoc, X'.map_comp P Y' Z']

private lemma pullbackMap_transport {X Y : AbelianScheme T} (e : X ≅ Y)
    (U : DualWitness X) (V : DualWitness Y) (U' : DualWitness ((baseChange c).obj X))
    (V' : DualWitness ((baseChange c).obj Y)) (l : Y ⟶ V.dual P) :
    U.pullbackMap P c U' (DualWitness.transportMap P e U V l) =
      DualWitness.transportMap P ((baseChange c).mapIso e) U' V' (V.pullbackMap P c V' l) := by
  simp only [DualWitness.pullbackMap, DualWitness.transportMap, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [U.baseChangeIso_naturality P V c U' V']

private lemma pullbackMap_comp_of_eq {X : AbelianScheme S} (U : DualWitness X)
    (V : DualWitness ((baseChange b).obj X)) (D : DualWitness ((baseChange q).obj X))
    (W : DualWitness ((baseChange c).obj ((baseChange b).obj X))) (l : X ⟶ U.dual P) :
    U.pullbackMap P q D l =
      DualWitness.transportMap P ((directSuccessiveIso b c q h).app X) D W
        (V.pullbackMap P c W (U.pullbackMap P b V l)) := by
  subst q
  exact U.pullbackMap_comp P b c V D W l

variable {q} {c}

/-- Integral lifts over the quotient presentation of a reduction give the
same marked lifting equations over any isomorphic presentation. -/
theorem integral_lift_equations_change_reduction (i : Q ≅ T) (h : i.hom ≫ b = q)
    (B : AbelianScheme S) (Y : AbelianScheme T)
    (eQ : (baseChange q).obj B ≅ (baseChange i.hom).obj Y)
    (U : DualWitness B) (VQ : DualWitness ((baseChange q).obj B)) (VY : DualWitness Y)
    (l : B ⟶ U.dual P) (lY : Y ⟶ VY.dual P)
    (hl : U.pullbackMap P q VQ l =
      DualWitness.transportMap P eQ VQ (VY.pullback P i.hom)
        (VY.pullbackMap P i.hom (VY.pullback P i.hom) lY))
    {κ : Type v} (f : κ → (B ⟶ B)) (g : κ → (Y ⟶ Y))
    (hf : ∀ j, (baseChange q).map (f j) ≫ eQ.hom = eQ.hom ≫ (baseChange i.hom).map (g j)) :
    ∃ e : (baseChange b).obj B ≅ Y,
      U.pullbackMap P b (U.pullback P b) l =
        DualWitness.transportMap P e (U.pullback P b) VY lY ∧
      ∀ j, (baseChange b).map (f j) ≫ e.hom = e.hom ≫ g j := by
  let F := baseChange i.hom
  let E := baseChangeEquivalence i
  let : F.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  let N := directSuccessiveIso b i.hom q h
  let G := baseChange b
  let k := (N.app B).symm ≪≫ eQ
  let e := F.preimageIso k
  have he : F.mapIso e = k := by
    apply Iso.ext
    exact F.map_preimage k.hom
  have hk : eQ = N.app B ≪≫ F.mapIso e := by
    rw [he]
    simp only [k, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  refine ⟨e, ?_, ?_⟩
  · let V := U.pullback P b
    let W := V.pullback P i.hom
    let WY := VY.pullback P i.hom
    let v := U.pullbackMap P b V l
    have hh : V.pullbackMap P i.hom W v =
        DualWitness.transportMap P (F.mapIso e) W WY (VY.pullbackMap P i.hom WY lY) := by
      have hcomp := pullbackMap_comp_of_eq b i.hom q h P U V VQ W l
      change U.pullbackMap P q VQ l =
        DualWitness.transportMap P (N.app B) VQ W (V.pullbackMap P i.hom W v) at hcomp
      have hu := hcomp.symm.trans hl
      rw [hk, transportMap_trans P (N.app B) (F.mapIso e) VQ W WY] at hu
      exact (DualWitness.transportAddEquiv P (N.app B) VQ W).injective hu
    have heq := hh.trans (pullbackMap_transport i.hom P e V VY W WY lY).symm
    apply F.map_injective
    apply (cancel_mono (V.baseChangeIso P i.hom W).hom).mp
    exact heq
  · intro j
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    have eh : F.map e.hom = (N.app B).inv ≫ eQ.hom := congrArg Iso.hom he
    rw [eh, ← Category.assoc]
    change ((G ⋙ F).map (f j) ≫ N.inv.app B) ≫ eQ.hom =
      (N.inv.app B ≫ eQ.hom) ≫ F.map (g j)
    rw [N.inv.naturality, Category.assoc, hf, Category.assoc]

/-- The spectrum of a surjective target is isomorphic to the spectrum
of the source modulo the actual kernel. -/
def quotientPresentationIso {R' R : Type u} [CommRing R'] [CommRing R]
    (φ : R' →+* R) (hφ : Function.Surjective φ) :
    Spec (CommRingCat.of (R' ⧸ RingHom.ker φ)) ≅ Spec (CommRingCat.of R) :=
  Scheme.Spec.mapIso (φ.quotientKerEquivOfSurjective hφ).symm.toCommRingCatIso.op

/-- The quotient presentation identifies both actual reduction maps. -/
theorem quotientPresentationIso_comp {R' R : Type u} [CommRing R'] [CommRing R]
    (φ : R' →+* R) (hφ : Function.Surjective φ) :
    (quotientPresentationIso φ hφ).hom ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))) := by
  change Spec.map (CommRingCat.ofHom (φ.quotientKerEquivOfSurjective hφ).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (RingHom.quotientKerEquivOfSurjective_symm_comp hφ)

end Langlands.AbelianScheme.PolarizedFiniteLevel
