/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.FiniteStructureUnitQuotientSystem
import WeilConjectures.AlgebraicGeometry.GrothendieckExistence
import WeilConjectures.AlgebraicGeometry.ThickeningSystemComparisonTransport

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Lift the unit of finite structure sheaves

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-unit-lift-existence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- Naturality of the explicit adjoint in the source module. -/
private theorem finiteStructureAdjoint_precomp
    {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S)
    {F G : X.Modules} (w : F ⟶ G)
    (a : (tensorPullback j).obj G ⟶ (pushforward p).obj
      (SheafOfModules.unit Y.ringCatSheaf)) :
    finiteStructureAdjoint j p F ((tensorPullback j).map w ≫ a) =
      w ≫ finiteStructureAdjoint j p G a := by
  simp only [finiteStructureAdjoint, Functor.map_comp, Category.assoc]
  have hn := (Classical.choose (exists_tensorPullbackAdjunction j)).unit.naturality w
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- Adjunction and invertible pushforward composition detect reduced morphisms. -/
private theorem finiteStructureAdjoint_injective
    {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S) (G : X.Modules) :
    Function.Injective (finiteStructureAdjoint j p G) := by
  intro a b h
  apply ((Classical.choose (exists_tensorPullbackAdjunction j)).homEquiv _ _).injective
  simp only [finiteStructureAdjoint, ← Category.assoc] at h
  have h' := (cancel_mono
    ((pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf))).mp h
  simpa only [Adjunction.homEquiv_unit] using h'

/-- Changing a natural comparison leaves the underlying compatible family unchanged. -/
private theorem compatible_family_change
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅ tensorPullback (j n))
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (v : ∀ n, (tensorPullback (j n)).obj G ⟶ (tensorPullback (j n)).obj F)
    (hv : ∀ n, (d n).hom.app G ≫ v n =
      (tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F) :
    ∀ n, (c n).hom.app G ≫ v n =
      (tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F := by
  obtain ⟨e, he⟩ := compatible_family_comparison_equiv (i := i) j hj c d
    (⟨F, hF⟩ : CoherentModules X) (⟨G, hG⟩ : CoherentModules X)
  have h := (e ⟨v, hv⟩).property
  change ∀ n, (c n).hom.app G ≫ (e ⟨v, hv⟩).val n =
    (tensorPullback (i n)).map ((e ⟨v, hv⟩).val (n + 1)) ≫ (c n).hom.app F at h
  rw [he ⟨v, hv⟩] at h
  exact h

/-- Existence part of the unit lift through a proper supporting quotient.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, expanded using 088E, 088F
and 0CYS.

Proof: Since X is finite type over the Noetherian affine base, X is Noetherian.
Proper support and coherence give a coherent ideal sheaf J annihilating G, with
V(J) proper over A (0CYS). Put Q = O_X/J. This is coherent with proper support.
The image of J in O_Xn annihilates j_n^*G, hence also p_n,* O_Yn through psi_n.
Applying this annihilation to the section 1 shows that the structure map
O_Xn to p_n,* O_Yn kills J. It therefore factors through j_n^*Q. Transport
this map through psi_n inverse to obtain u_n : j_n^*Q to j_n^*G.
The cartesian base-change map preserves units. The given transition equation
for psi and the canonical composition comparison thus make the u_n compatible.
Full faithfulness of completion on coherent modules with proper support (088E,
088F) lifts this family to u : Q to G. Define eta as O_X to Q followed by u.
Its reductions are exactly the structure maps. Adjunction and pushforward
composition give the stated scalar formula, including the formula for r = 1.
Let L be the module endomorphism of G given by left multiplication by eta(1).
After tensor pullback to X_n and conjugation by psi_n, multiplicativity hmu
identifies L with multiplication by 1 on p_n,* O_Yn, hence with its identity.
Equality of these maps is checked locally on pure tensors, which generate the
pullback tensor product. Faithfulness of completion on G gives L = identity;
evaluating on sections proves the left-unit law. This uses proper support of
Q and G, never properness of O_X. If G is zero (including an empty scheme),
the quotient and all maps above are zero, and both asserted equations hold.
(blueprint: lem-weil-pbc-finite-structure-unit-lift-existence). -/
theorem finite_structure_unit_lift_existence
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom)
    (μ : G ⊗ G ⟶ G)
    (hcomm : ∀ (U : X.Opens) (x y : Γ(G, U)),
      μ.app U (tmulSection x y) = μ.app U (tmulSection y x))
    (hμ : ∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
          fun x ↦ (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
        ∀ (x y : Γ(G, U)),
          a (μ.app U (tmulSection x y)) = a x * a y) :
    ∃ η : SheafOfModules.unit X.ringCatSheaf ⟶ G,
      (∀ (U : X.Opens) (x : Γ(G, U)),
        μ.app U (tmulSection ((η.val.app (op U)).hom (1 : Γ(X, U))) x) = x) ∧
      (∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          ((η.val.app (op U)).hom r) =
          (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))).app U r) := by
  classical
  obtain ⟨Q, hQ, hproperQ, q, v, hv, hq⟩ :=
    finite_structure_unit_quotient_system A I X f i hi hp c hc Yn fnY gn hcart hw
      G hG hproper ψ hψ
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let d : ∀ n : ℕ, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅
      tensorPullback (j n) := fun n ↦
    (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (j (n + 1)))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n))
  have hj : ∀ n, IsClosedImmersion (j n) := by
    intro n
    dsimp only [j]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1))))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hvd := compatible_family_change (i := i) j hj d c G Q hG hQ v hv
  obtain ⟨w, hw, _⟩ :=
    (grothendieck_existence_fullyFaithful A I f i hi hp d)
      G Q hG hQ hproper hproperQ v hvd
  let η : SheafOfModules.unit X.ringCatSheaf ⟶ G := q ≫ w
  have hη : ∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
      (finiteStructureAdjoint (j n) (fnY n) G (ψ n).hom).app U ((η.val.app (op U)).hom r) =
        (fnY n ≫ j n).app U r := by
    intro n U r
    have hn := finiteStructureAdjoint_precomp (j n) (fnY n) w (ψ n).hom
    rw [hw n] at hn
    have hs := congrArg (fun z ↦ z.app U ((q.val.app (op U)).hom r)) hn
    change (finiteStructureAdjoint (j n) (fnY n) G (ψ n).hom).app U
      (w.app U ((q.val.app (op U)).hom r)) = _
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply] using hs.symm.trans (hq n U r)
  let eta : (𝟙_ X.Modules) ⟶ G := η
  let L : G ⟶ G := (ρ_ G).inv ≫ (G ◁ eta) ≫ μ
  have hL : ∀ (U : X.Opens) (x : Γ(G, U)),
      L.app U x = μ.app U (tmulSection ((η.val.app (op U)).hom (1 : Γ(X, U))) x) := by
    intro U x
    simp only [L, Hom.comp_app, ConcreteCategory.comp_apply, rightUnitor_inv_app,
      whiskerLeft_app_tmulSection]
    exact hcomm U x ((η.val.app (op U)).hom (1 : Γ(X, U)))
  have hLn : ∀ n : ℕ, (tensorPullback (j n)).map L = 𝟙 _ := by
    intro n
    apply (cancel_mono (ψ n).hom).mp
    apply finiteStructureAdjoint_injective (j n) (fnY n) G
    rw [finiteStructureAdjoint_precomp, Category.id_comp]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (finiteStructureAdjoint (j n) (fnY n) G (ψ n).hom).app (unop U)
      (L.app (unop U) x) =
      (finiteStructureAdjoint (j n) (fnY n) G (ψ n).hom).app (unop U) x
    rw [hL]
    have hm := hμ n (unop U) ((η.val.app U).hom (1 : Γ(X, unop U))) x
    dsimp only at hm
    refine hm.trans ?_
    rw [hη n (unop U) 1, map_one, one_mul]
  have hLeq : L = 𝟙 G := by
    obtain ⟨z, hz, huniq⟩ :=
      (grothendieck_existence_fullyFaithful A I f i hi hp d) G G hG hG hproper hproper
      (fun n ↦ 𝟙 ((tensorPullback (j n)).obj G)) (by
        intro n
        exact (Category.comp_id _).trans
          ((Category.id_comp _).symm.trans (congrArg
            (fun t ↦ t ≫ (d n).hom.app G)
            (CategoryTheory.Functor.map_id (tensorPullback (i n))
              ((tensorPullback (j (n + 1))).obj G)).symm)))
    have hid : ∀ n, (tensorPullback (j n)).map (𝟙 G) = 𝟙 _ := by
      intro n
      exact CategoryTheory.Functor.map_id _ _
    exact (huniq L hLn).trans (huniq (𝟙 G) hid).symm
  refine ⟨η, ?_, hη⟩
  intro U x
  rw [← hL, hLeq]
  rfl

end AlgebraicGeometry
