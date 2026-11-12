import Langlands.GroupScheme.Quaternionic.IsometryCutAffine
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Split-torus rank bounds from the division-algebra Witt index -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace splitTorus

variable {K : Type u} [Field K] [Infinite K]
  {I : Type u} [Fintype I] [DecidableEq I]

/-- Two integral monomials whose exponent sum is nonzero have product
different from one at some tuple of field units. -/
theorem exists_exponentValue_mul_ne_one {m p : I → ℤ} (hmp : m + p ≠ 0) :
    ∃ t : I → Kˣ,
      (exponentValue I t (Multiplicative.ofAdd m) : K) *
        (exponentValue I t (Multiplicative.ofAdd p) : K) ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_exponentValue_ne_one (k := K) hmp
  refine ⟨t, fun h => ht ?_⟩
  apply Units.ext
  change (exponentValue I t
    (Multiplicative.ofAdd m * Multiplicative.ofAdd p) : K) = 1
  simpa only [_root_.map_mul, Units.val_mul] using h

end splitTorus

namespace Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {n : Type} [Fintype n] [DecidableEq n]

section WeightRows

variable (I : Type u) [Fintype I] [DecidableEq I]
  (jmap : splitTorus (Spec (CommRingCat.of K)) I ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)))

/-- The original inverse unit matrices at the base-field points of a
supplied split-torus homomorphism. -/
def torusInverseUnitMatrices (t : I → Kˣ) : Matrix n n D :=
  ((FiniteAlgebraUnits.baseAffineUnit (Module.finBasis K (Matrix n n D))
    ((splitTorus.algebraPointsEquiv I K).symm t ≫ jmap.hom.hom))⁻¹ :
      (Matrix n n D)ˣ).val

/-- A nonzero universal algebra weight element has a nonzero row in the
division-algebra common weight space of the inverse unit matrices. -/
theorem commonWeightSpace_ne_bot_of_coefficientColumn
    {m : I → ℤ} {j : Fin (Module.finrank K (Matrix n n D))}
    (hj : GeneralLinear.CocharacterDiagonal.coefficientColumn I
      ((FiniteAlgebraUnits.rightRegularRepresentation
        (Module.finBasis K (Matrix n n D))).restrict jmap) m j ≠ 0) :
    commonWeightSpace (torusInverseUnitMatrices I jmap)
      (fun t : I → Kˣ =>
        (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : K)) ≠ ⊥ := by
  let b := Module.finBasis K (Matrix n n D)
  let y := FiniteAlgebraUnits.torusCoefficientElement b I jmap m j
  have hy : y ≠ 0 := FiniteAlgebraUnits.torusCoefficientElement_ne_zero b I jmap hj
  intro hzero
  apply hy
  ext r c
  have hr : y r ∈ commonWeightSpace (torusInverseUnitMatrices I jmap)
      (fun t : I → Kˣ =>
        (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : K)) := by
    intro t
    exact congrArg (fun z : Matrix n n D => z r)
      (FiniteAlgebraUnits.torusCoefficientElement_eigen b I jmap m j t)
  rw [hzero, Submodule.mem_bot] at hr
  exact congrFun hr c

end WeightRows

variable [Infinite K] (σ : FirstKindInvolution K D) (H : Matrix n n D)

/-- A faithful split torus of rank at least two in the actual unitary
isometry group forces Witt index at least two. -/
theorem two_le_wittIndex_of_unitaryTorus (I : Type u) [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.unitaryGroup H)
    [Mono i.hom.hom.left] (hI : 2 ≤ Nat.card I) :
    2 ≤ σ.wittIndex H := by
  let b := Module.finBasis K (Matrix n n D)
  let jmap := i ≫ σ.unitaryGroupι H
  let ρ := (FiniteAlgebraUnits.rightRegularRepresentation b).restrict jmap
  have : Mono (σ.unitaryGroupι H).hom.hom.left :=
    (σ.isClosedSubgroup_unitaryGroupι H).mono
  have : Mono (i.hom.hom.left ≫ (σ.unitaryGroupι H).hom.hom.left) := mono_comp _ _
  have : Mono (FiniteAlgebraUnits.rightRegularRepresentation b).hom.hom.left :=
    FiniteAlgebraUnits.mono_rightRegularRepresentation_left b
  have : Mono ρ.hom.hom.left := by
    change Mono ((i.hom.hom.left ≫ (σ.unitaryGroupι H).hom.hom.left) ≫
      (FiniteAlgebraUnits.rightRegularRepresentation b).hom.hom.left)
    exact mono_comp _ _
  let w := MatrixRepresentation.nonreciprocalWeightPair I ρ hI
  let A := torusInverseUnitMatrices I jmap
  let χ := fun t : I → Kˣ =>
    (splitTorus.exponentValue I t (Multiplicative.ofAdd w.first) : K)
  let ψ := fun t : I → Kˣ =>
    (splitTorus.exponentValue I t (Multiplicative.ofAdd w.second) : K)
  have hA : ∀ t, A t * H * σ.matrix n (A t) = H := by
    intro t
    simpa only [A, torusInverseUnitMatrices, jmap, unitaryGroupι,
      Grp.comp_hom_hom, Category.assoc] using
      IsometryCut.baseAffineUnit_inv_isometry (σ.matrix n) H
        ((splitTorus.algebraPointsEquiv I K).symm t ≫ i.hom.hom)
  have hsum (m : I → ℤ) (hm : m ≠ 0) : m + m ≠ 0 := by
    intro hz
    apply hm
    funext a
    have ha := congrFun hz a
    change m a + m a = 0 at ha
    change m a = 0
    omega
  have hfirst : ∃ t, χ t * χ t ≠ 1 :=
    splitTorus.exists_exponentValue_mul_ne_one (K := K) (hsum w.first w.first_ne_zero)
  have hsecond : ∃ t, ψ t * ψ t ≠ 1 :=
    splitTorus.exists_exponentValue_mul_ne_one (K := K) (hsum w.second w.second_ne_zero)
  have hsum_ne : w.first + w.second ≠ 0 := by
    intro hz
    apply w.second_ne_neg_first
    funext a
    have ha := congrFun hz a
    change w.first a + w.second a = 0 at ha
    change w.second a = -w.first a
    omega
  have hprod : ∃ t, χ t * ψ t ≠ 1 :=
    splitTorus.exists_exponentValue_mul_ne_one (K := K) hsum_ne
  have hne : χ ≠ ψ := by
    intro he
    exact w.second_ne_first
      (splitTorus.exponentValue_function_injective (k := K) he.symm)
  have hχ : commonWeightSpace A χ ≠ ⊥ :=
    commonWeightSpace_ne_bot_of_coefficientColumn I jmap w.firstVector_ne_zero
  have hψ : commonWeightSpace A ψ ≠ ⊥ :=
    commonWeightSpace_ne_bot_of_coefficientColumn I jmap w.secondVector_ne_zero
  exact σ.two_le_wittIndex_of_commonWeightSpaces hA hfirst hsecond hprod hne hχ hψ

/-- For Witt index at most one, any faithful split torus in the unitary
isometry group has dimension at most one. -/
theorem card_le_one_of_unitaryTorus (hH : σ.wittIndex H ≤ 1)
    (I : Type u) [Finite I]
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.unitaryGroup H)
    [Mono i.hom.hom.left] : Nat.card I ≤ 1 := by
  classical
  let := Fintype.ofFinite I
  by_contra h
  have hI : 2 ≤ Nat.card I := by omega
  have hw := σ.two_le_wittIndex_of_unitaryTorus H I i hI
  omega

/-- Every group admitting a monomorphism into a unitary group of Witt
index at most one has split rank at most one. -/
theorem splitRank_le_one_of_mono_unitary (hH : σ.wittIndex H ≤ 1)
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (q : G ⟶ σ.unitaryGroup H) [Mono q.hom.hom.left] :
    splitRank G ≤ 1 := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono (i ≫ q).hom.hom.left := by
    change Mono (i.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  have hc := σ.card_le_one_of_unitaryTorus H hH I (i ≫ q)
  exact_mod_cast hc

/-- The actual full isometry group has split rank at most one if the
division-algebra Witt index is at most one. -/
theorem splitRank_unitaryGroup_le_one (hH : σ.wittIndex H ≤ 1) :
    splitRank (σ.unitaryGroup H) ≤ 1 :=
  σ.splitRank_le_one_of_mono_unitary H hH (𝟙 _)

/-- The reduced-norm-one symplectic subgroup has the same upper bound. -/
theorem splitRank_symplecticGroup_le_one [Algebra.IsCentral K D] [Nonempty n]
    (hH : σ.wittIndex H ≤ 1) :
    splitRank (σ.symplecticGroup H) ≤ 1 := by
  have : Mono (σ.symplecticGroupι H).hom.hom.left := by
    change Mono (kernelι _).hom.hom.left
    infer_instance
  exact σ.splitRank_le_one_of_mono_unitary H hH (σ.symplecticGroupι H)

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
