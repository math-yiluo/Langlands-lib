import Langlands.GroupScheme.HomScheme.AdicAlgebraization
import Langlands.GroupScheme.Descent.EtaleHomDescent
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Finite étale descent of algebraized adic Hom systems -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints
open Langlands.GroupScheme.RelativeMultiplicativeType

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A] {I : Ideal A}
  {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- A finite test scheme over `Spec A` is, over `Spec A`, the spectrum of a finite
`A`-algebra. -/
theorem exists_spec_iso_of_isFinite (V : Over (Spec (CommRingCat.of A))) [IsFinite V.hom] :
    ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C), ψ.Finite ∧
      Nonempty (Over.mk (Spec.map (CommRingCat.ofHom ψ)) ≅ V) := by
  have : IsAffine V.left := isAffine_of_isAffineHom V.hom
  refine ⟨Γ(V.left, ⊤), inferInstance,
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ V.hom.appTop).hom, ?_, ⟨?_⟩⟩
  · exact V.hom.finite_appTop.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.finite
  · refine Over.isoMk V.left.isoSpec.symm ?_
    change V.left.isoSpec.inv ≫ V.hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ V.hom.appTop)
    rw [← Scheme.isoSpec_inv_naturality V.hom, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- Diagonalizability of a pulled-back group transfers along an isomorphism of test
schemes. -/
theorem isDiagonalizable_of_overIso {V W : Over (Spec (CommRingCat.of A))} (e : W ≅ V)
    (hH : IsDiagonalizable ((baseChange V.hom).obj H)) :
    IsDiagonalizable ((baseChange W.hom).obj H) :=
  IsDiagonalizable.of_iso
    (Descent.pullbackComparison V.hom e.hom.left W.hom (Over.w e.hom) H).symm
    (hH.baseChange e.hom.left)

section Transport

variable (I H G)

/-- Existence of algebraizations over spectra of finite algebras. -/
def AffineAlgebraizationExists : Prop :=
  ∀ {C : Type u} [CommRing C] (ψ : A →+* C), ψ.Finite →
    IsDiagonalizable ((baseChange (Spec.map (CommRingCat.ofHom ψ))).obj H) →
      ∀ s : System I H G, ∃ a : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom ψ))),
        s.IsAlgebraization a

/-- Uniqueness of algebraizations over spectra of finite algebras. -/
def AffineAlgebraizationUnique : Prop :=
  ∀ {C : Type u} [CommRing C] (ψ : A →+* C), ψ.Finite →
    IsDiagonalizable ((baseChange (Spec.map (CommRingCat.ofHom ψ))).obj H) →
      ∀ (s : System I H G) (a b : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom ψ)))),
        s.IsAlgebraization a → s.IsAlgebraization b → a = b

variable {I H G}

/-- Algebraizations exist over every finite test scheme on which the source becomes
diagonalizable. -/
theorem exists_isAlgebraization_of_isFinite (hE : AffineAlgebraizationExists I H G)
    (V : Over (Spec (CommRingCat.of A))) [IsFinite V.hom]
    (hH : IsDiagonalizable ((baseChange V.hom).obj H)) (s : System I H G) :
    ∃ a : RelativeHom H G V, s.IsAlgebraization a := by
  obtain ⟨C, _, ψ, hψ, ⟨e⟩⟩ := exists_spec_iso_of_isFinite V
  obtain ⟨a, ha⟩ := hE ψ hψ (isDiagonalizable_of_overIso e hH) s
  exact ⟨evaluate e.inv a, System.isAlgebraization_evaluate ha e.inv⟩

/-- Algebraizations are unique over every finite test scheme on which the source becomes
diagonalizable. -/
theorem eq_of_isAlgebraization_of_isFinite (hU : AffineAlgebraizationUnique I H G)
    (V : Over (Spec (CommRingCat.of A))) [IsFinite V.hom]
    (hH : IsDiagonalizable ((baseChange V.hom).obj H)) {s : System I H G}
    {a b : RelativeHom H G V} (ha : s.IsAlgebraization a) (hb : s.IsAlgebraization b) :
    a = b := by
  obtain ⟨C, _, ψ, hψ, ⟨e⟩⟩ := exists_spec_iso_of_isFinite V
  have h := hU ψ hψ (isDiagonalizable_of_overIso e hH) s _ _
    (System.isAlgebraization_evaluate ha e.hom) (System.isAlgebraization_evaluate hb e.hom)
  have hid : ∀ c : RelativeHom H G V, evaluate e.inv (evaluate e.hom c) = c := by
    intro c
    rw [← evaluate_comp, e.inv_hom_id, evaluate_id]
  rw [← hid a, ← hid b, h]

end Transport

section Descent

variable {S' : Scheme.{u}} (p : S' ⟶ Spec (CommRingCat.of A))

/-- The first projection of the double overlap as a test-scheme map. -/
abbrev overlapFst : Over.mk (Descent.fst p ≫ p) ⟶ Over.mk p :=
  Over.homMk (Descent.fst p) rfl

/-- The second projection of the double overlap as a test-scheme map. -/
abbrev overlapSnd : Over.mk (Descent.fst p ≫ p) ⟶ Over.mk p :=
  Over.homMk (Descent.snd p) pullback.condition.symm

/-- Equal evaluations on the two overlap projections give compatibility with the
canonical descent data. -/
theorem compatible_of_evaluate_eq (f : RelativeHom H G (Over.mk p))
    (h : evaluate (overlapFst p) f = evaluate (overlapSnd p) f) :
    Descent.Compatible (Descent.canonicalDatum p H) (Descent.canonicalDatum p G) f := by
  have h' : (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl H).inv ≫
        (baseChange (Descent.fst p)).map f ≫
          (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl G).hom =
      (Descent.pullbackComparison p (Descent.snd p) (Descent.fst p ≫ p)
          pullback.condition.symm H).inv ≫
        (baseChange (Descent.snd p)).map f ≫
          (Descent.pullbackComparison p (Descent.snd p) (Descent.fst p ≫ p)
            pullback.condition.symm G).hom := h
  simp only [Descent.Compatible, Descent.canonicalDatum, Descent.canonicalOverlap,
    Iso.trans_hom, Iso.symm_hom]
  calc (baseChange (Descent.fst p)).map f ≫
        (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl G).hom ≫
          (Descent.pullbackComparison p (Descent.snd p) (Descent.fst p ≫ p)
            pullback.condition.symm G).inv =
      (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl H).hom ≫
        ((Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl H).inv ≫
          (baseChange (Descent.fst p)).map f ≫
            (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl G).hom) ≫
          (Descent.pullbackComparison p (Descent.snd p) (Descent.fst p ≫ p)
            pullback.condition.symm G).inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
        rw [h']
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [IsFinite p] [Etale p] [Surjective p]

/-- Restriction to the adic thickenings is bijective once the source becomes diagonalizable
on a finite étale surjective cover, given existence and uniqueness of algebraizations over
spectra of finite algebras. -/
theorem restrict_bijective_of_finiteEtale (hE : AffineAlgebraizationExists I H G)
    (hU : AffineAlgebraizationUnique I H G)
    (hH : IsDiagonalizable ((baseChange p).obj H)) :
    Function.Bijective (System.restrict I H G) := by
  have hHp : IsDiagonalizable ((baseChange (Over.mk p).hom).obj H) := hH
  have : IsFinite (Over.mk p).hom := inferInstanceAs (IsFinite p)
  constructor
  · intro f g hfg
    have hf := System.isAlgebraization_restrict (I := I) f (Over.mk p)
    have hg := System.isAlgebraization_restrict (I := I) g (Over.mk p)
    rw [← hfg] at hg
    have h := eq_of_isAlgebraization_of_isFinite hU (Over.mk p) hHp hf hg
    apply Grp.hom_ext
    apply (Over.pullback p).map_injective
    exact congrArg (fun k => k.hom.hom) h
  · intro s
    obtain ⟨fU, hfU⟩ := exists_isAlgebraization_of_isFinite hE (Over.mk p) hHp s
    have hW : IsDiagonalizable ((baseChange (Over.mk (Descent.fst p ≫ p)).hom).obj H) :=
      IsDiagonalizable.of_iso
        (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl H).symm
        (hH.baseChange (Descent.fst p))
    have : IsFinite (Over.mk (Descent.fst p ≫ p)).hom :=
      inferInstanceAs (IsFinite (Descent.fst p ≫ p))
    have hc : evaluate (overlapFst p) fU = evaluate (overlapSnd p) fU :=
      eq_of_isAlgebraization_of_isFinite hU _ hW
        (System.isAlgebraization_evaluate hfU _) (System.isAlgebraization_evaluate hfU _)
    have hcompat := compatible_of_evaluate_eq p fU hc
    refine ⟨Descent.EtaleHomDescent.hom p fU hcompat, ?_⟩
    have hbase := Descent.EtaleHomDescent.baseChange_hom p fU hcompat
    apply System.ext
    intro n
    let q := quotientMap I n
    let T : Over (Spec (CommRingCat.of A)) := Over.mk (pullback.snd p q ≫ q)
    let r : T ⟶ Over.mk q := Over.homMk (pullback.snd p q) rfl
    let t : T ⟶ Over.mk p := Over.homMk (pullback.fst p q) pullback.condition
    have : Flat r.left := inferInstanceAs (Flat (pullback.snd p q))
    have : Surjective r.left := inferInstanceAs (Surjective (pullback.snd p q))
    have : QuasiCompact r.left := inferInstanceAs (QuasiCompact (pullback.snd p q))
    apply evaluate_injective_of_flat_surjective r
    rw [System.restrict_hom]
    have h1 : evaluate r ((baseChange q).map (Descent.EtaleHomDescent.hom p fU hcompat)) =
        evaluate t ((baseChange p).map (Descent.EtaleHomDescent.hom p fU hcompat)) := by
      exact (evaluate_baseChange (M := Over.mk q) r _).trans (evaluate_baseChange t _).symm
    rw [h1, hbase]
    exact hfU n t (pullback.snd p q) rfl

end Descent

end Langlands.GroupScheme.HomScheme.Adic
