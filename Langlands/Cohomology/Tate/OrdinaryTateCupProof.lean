import Langlands.Cohomology.Tate.OrdinaryCupLawsProof
import Langlands.Cohomology.Tate.OrdinaryCupBoundaryProof
import Langlands.Cohomology.Tate.OrdinaryTateBoundary
import Langlands.Cohomology.Tate.OrdinaryShift
import Langlands.Cohomology.Tate.CupLawsProof
import Langlands.Cohomology.Tate.OrdinaryTateCupStatement

noncomputable section

universe u

open CategoryTheory
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate.OrdinaryTateCup

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

def comparison (A : Rep.{u} R G) (i : ℕ) (m : ℤ) (h : (i : ℤ) = m) :
    groupCohomology A i ⟶ tateCohomology A m :=
  ordinaryToTate A i ≫ (tateDegreeIso A h).hom

lemma comparison_refl (A : Rep.{u} R G) (i : ℕ) :
    comparison A i i rfl = ordinaryToTate A i := by
  simp [comparison, tateDegreeIso]

lemma comparison_delta {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) (m n : ℤ)
    (him : (i : ℤ) = m) (hmn : m + 1 = n)
    (x : groupCohomology S.X₃ i) :
    comparison S.X₁ j n (by omega)
      ((eqToIso (congrArg (groupCohomology S.X₁) hij)).hom
        (groupCohomology.δ hS i (i + 1) rfl x)) =
      (tateDegreeIso S.X₁ hmn).hom (TateCohomology.δ hS m
        (comparison S.X₃ i m him x)) := by
  subst j m n
  simpa [comparison, tateDegreeIso] using
    ConcreteCategory.congr_hom (ordinaryToTate_delta hS i) x

lemma comparison_naturality {A B : Rep.{u} R G} (f : A ⟶ B)
    (i : ℕ) (m : ℤ) (h : (i : ℤ) = m) (x : groupCohomology A i) :
    comparison B i m h (groupCohomology.map (MonoidHom.id G) f i x) =
      (tateCohomologyFunctor m).map f (comparison A i m h x) := by
  subst m
  simpa [comparison, tateDegreeIso] using
    ConcreteCategory.congr_hom (ordinaryToTate_naturality f i) x

lemma tensor_zero (A B : Rep.{u} R G) (a : A.ρ.invariants) (b : B.ρ.invariants) :
    comparison (A ⊗ B) (0 + 0) (0 + 0) rfl
      (ordinaryCup (tensorPairing A B) 0 0
        ((groupCohomology.H0Iso A).inv a) ((groupCohomology.H0Iso B).inv b)) =
      tensorCup A B 0 0
        (ordinaryToTate A 0 ((groupCohomology.H0Iso A).inv a))
        (ordinaryToTate B 0 ((groupCohomology.H0Iso B).inv b)) := by
  simp only [comparison, tateDegreeIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [ordinaryCup_zero_invariant, ordinaryToTate_zero_invariant,
    ordinaryToTate_zero_invariant, tensorCup_zero_zero]
  exact (ordinaryToTate_zero_invariant (A ⊗ B)
    ((tensorPairing A B).onInvariants a b)).trans
      (cupZero_zeroClass (tensorPairing A B) a b).symm

lemma tensor_left {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p q : ℕ) (a : groupCohomology S.X₃ p) (b : groupCohomology B q)
    (ih : comparison (S.X₃ ⊗ B) (p + q) ((p : ℤ) + q) (by omega)
      (ordinaryCup (tensorPairing S.X₃ B) p q a b) =
        tensorCup S.X₃ B p q (ordinaryToTate S.X₃ p a) (ordinaryToTate B q b)) :
    comparison (S.X₁ ⊗ B) ((p + 1) + q) (((p + 1 : ℕ) : ℤ) + q) (by omega)
      (ordinaryCup (tensorPairing S.X₁ B) (p + 1) q
        (groupCohomology.δ hS p (p + 1) rfl a) b) =
      tensorCup S.X₁ B (p + 1 : ℕ) q
        (ordinaryToTate S.X₁ (p + 1) (groupCohomology.δ hS p (p + 1) rfl a))
        (ordinaryToTate B q b) := by
  have hd := ConcreteCategory.congr_hom (ordinaryToTate_delta hS p) a
  change ordinaryToTate S.X₁ (p + 1) (groupCohomology.δ hS p (p + 1) rfl a) =
    TateCohomology.δ hS p (ordinaryToTate S.X₃ p a) at hd
  rw [OrdinaryCupBoundary.tensor_left_boundary hS B hB]
  refine Eq.trans (comparison_delta hB (p + q) ((p + 1) + q) (by omega)
    ((p : ℤ) + q) (((p + 1 : ℕ) : ℤ) + q) (by omega) (by omega)
      (ordinaryCup (tensorPairing S.X₃ B) p q a b)) ?_
  change (tateDegreeIso (S.X₁ ⊗ B) _).hom
    (TateCohomology.δ hB ((p : ℤ) + q)
      (comparison (S.X₃ ⊗ B) (p + q) ((p : ℤ) + q) _
        (ordinaryCup (tensorPairing S.X₃ B) p q a b))) = _
  rw [ih, hd]
  exact (tensorCup_delta_first S hS B hB p q
    (ordinaryToTate S.X₃ p a) (ordinaryToTate B q b)).symm

lemma sign_smul (A : Rep.{u} R G) (n : ℤ) (p : ℕ) (x : tateCohomology A n) :
    (-1 : R) ^ p • x = ((p : ℤ).negOnePow : ℤ) • x := by
  rw [Int.coe_negOnePow_natCast, ← Int.cast_smul_eq_zsmul R]
  simp

lemma tensor_right {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology S.X₃ q)
    (ih : comparison (A ⊗ S.X₃) (p + q) ((p : ℤ) + q) (by omega)
      (ordinaryCup (tensorPairing A S.X₃) p q a b) =
        tensorCup A S.X₃ p q (ordinaryToTate A p a) (ordinaryToTate S.X₃ q b)) :
    comparison (A ⊗ S.X₁) (p + (q + 1)) ((p : ℤ) + ((q + 1 : ℕ) : ℤ)) (by omega)
      (ordinaryCup (tensorPairing A S.X₁) p (q + 1) a
        (groupCohomology.δ hS q (q + 1) rfl b)) =
      tensorCup A S.X₁ p (q + 1 : ℕ) (ordinaryToTate A p a)
        (ordinaryToTate S.X₁ (q + 1) (groupCohomology.δ hS q (q + 1) rfl b)) := by
  have hd := ConcreteCategory.congr_hom (ordinaryToTate_delta hS q) b
  change ordinaryToTate S.X₁ (q + 1) (groupCohomology.δ hS q (q + 1) rfl b) =
    TateCohomology.δ hS q (ordinaryToTate S.X₃ q b) at hd
  rw [OrdinaryCupBoundary.tensor_right_boundary hS A hA, map_smul]
  refine Eq.trans (congrArg (fun x => (-1 : R) ^ p • x)
    (comparison_delta hA (p + q) (p + (q + 1)) (by omega)
      ((p : ℤ) + q) ((p : ℤ) + ((q + 1 : ℕ) : ℤ)) (by omega) (by omega)
      (ordinaryCup (tensorPairing A S.X₃) p q a b))) ?_
  change (-1 : R) ^ p • (tateDegreeIso (A ⊗ S.X₁) _).hom
    (TateCohomology.δ hA ((p : ℤ) + q)
      (comparison (A ⊗ S.X₃) (p + q) ((p : ℤ) + q) _
        (ordinaryCup (tensorPairing A S.X₃) p q a b))) = _
  rw [ih, hd, sign_smul]
  exact (tensorCup_delta_second S hS A hA p q
    (ordinaryToTate A p a) (ordinaryToTate S.X₃ q b)).symm

lemma tensor (A B : Rep.{u} R G) (p q : ℕ)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    comparison (A ⊗ B) (p + q) ((p : ℤ) + q) (by omega)
      (ordinaryCup (tensorPairing A B) p q a b) =
        tensorCup A B p q (ordinaryToTate A p a) (ordinaryToTate B q b) := by
  apply ordinaryClasses_shift_induction
    (fun A B p q a b => comparison (A ⊗ B) (p + q) ((p : ℤ) + q) (by omega)
      (ordinaryCup (tensorPairing A B) p q a b) =
        tensorCup A B p q (ordinaryToTate A p a) (ordinaryToTate B q b))
    (fun A B a b => tensor_zero A B a b)
  · intro A B p a b ih
    exact tensor_left (shiftUpSequence_shortExact A) B
      (scalarSplit_tensorRight_shortExact (shiftUpSequence A)
        (shiftUpSequence_scalarSplitting A) B) p 0 a b ih
  · intro A B p q a b ih
    exact tensor_right (shiftUpSequence_shortExact B) A
      (scalarSplit_tensorLeft_shortExact (shiftUpSequence B)
        (shiftUpSequence_scalarSplitting B) A) p q a b ih

omit [Fintype G] in
lemma ordinary_tensorHom {A B C : Rep.{u} R G} (φ : Pairing A B C)
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q) :
    groupCohomology.map (MonoidHom.id G) φ.tensorHom (p + q)
      (ordinaryCup (tensorPairing A B) p q a b) = ordinaryCup φ p q a b := by
  simpa using ordinaryCup_naturality (tensorPairing A B) φ (𝟙 A) (𝟙 B) φ.tensorHom
    (fun _ _ => rfl) p q a b

end Langlands.Tate.OrdinaryTateCup

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma ordinaryToTate_cup {A B C : Rep.{u} R G} (φ : Pairing A B C)
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q) :
    (tateDegreeIso C (show ((p + q : ℕ) : ℤ) = (p : ℤ) + q by omega)).hom
      (ordinaryToTate C (p + q) (ordinaryCup φ p q a b)) =
      cup φ p q (ordinaryToTate A p a) (ordinaryToTate B q b) := by
  change OrdinaryTateCup.comparison C (p + q) ((p : ℤ) + q) (by omega)
    (ordinaryCup φ p q a b) = _
  rw [← OrdinaryTateCup.ordinary_tensorHom φ p q a b,
    OrdinaryTateCup.comparison_naturality, OrdinaryTateCup.tensor]
  rfl

/-- Exact comparison of the two independently constructed products. -/
theorem ordinaryTateCupLaws : OrdinaryTateCupLaws.{u} := by
  intro R G _ _ _ A B C φ p q a b
  exact ordinaryToTate_cup φ p q a b

end Langlands.Tate
