import Langlands.Automorphic.FiniteInfiniteMultiplicityArchimedean
import Langlands.Automorphic.FiniteFamilyGKPairing
import Langlands.Automorphic.PlaceComponentExistence
import Mathlib.Algebra.Group.Subgroup.Finite

/-! # The finite family of actual archimedean place operators -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped TensorProduct Matrix

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

namespace InfinitePlaceFamily

/-- Index the real and complex places together without changing their local fields. -/
abbrev Index (F : Type u) [Field F] [NumberField F] :=
  {v : NumberField.InfinitePlace F // v.IsReal} ⊕
    {v : NumberField.InfinitePlace F // v.IsComplex}

/-- The genuine orthogonal or unitary compact group at the indexed place. -/
abbrev Compact (n : ℕ) : Index F → Type
  | .inl _ => Matrix.unitaryGroup (Fin n) ℝ
  | .inr _ => Matrix.unitaryGroup (Fin n) ℂ

instance compactGroup (n : ℕ) (i : Index F) : Group (Compact n i) := by
  cases i <;> exact inferInstance

instance compactTopology (n : ℕ) (i : Index F) : TopologicalSpace (Compact n i) := by
  cases i <;> exact inferInstance

/-- The whole complexification of the real local matrix Lie algebra. -/
abbrev Lie (n : ℕ) : Index F → Type
  | .inl _ => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
  | .inr _ => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

instance placeLieRing (n : ℕ) (i : Index F) : LieRing (Lie n i) := by
  cases i <;> exact inferInstance

instance placeLieAlgebra (n : ℕ) (i : Index F) : LieAlgebra ℂ (Lie n i) := by
  cases i <;> exact inferInstance

def compactFactor (n : ℕ) (i : Index F) :
    Compact n i →ₜ* ArchimedeanCompactFactors F n :=
  match i with
  | .inl v => ArchimedeanCompactFactors.realPlaceFactor F n v
  | .inr v => ArchimedeanCompactFactors.complexPlaceFactor F n v

def compactInclusion (n : ℕ) (i : Index F) :
    Compact n i →ₜ* standardInfiniteCompact F n :=
  (ArchimedeanCompactFactors.toStandardCompact F n).comp (compactFactor n i)

def lieInclusion (n : ℕ) (i : Index F) :
    Lie n i →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  match i with
  | .inl v => realPlaceComplexLieInclusion F n v
  | .inr v => complexPlaceComplexLieInclusion F n v

theorem compactInclusion_commute (n : ℕ) (i j : Index F) (hij : i ≠ j)
    (k : Compact n i) (l : Compact n j) :
    compactInclusion n i k * compactInclusion n j l =
      compactInclusion n j l * compactInclusion n i k := by
  classical
  change ArchimedeanCompactFactors.toStandardCompact F n (compactFactor n i k) *
      ArchimedeanCompactFactors.toStandardCompact F n (compactFactor n j l) =
    ArchimedeanCompactFactors.toStandardCompact F n (compactFactor n j l) *
      ArchimedeanCompactFactors.toStandardCompact F n (compactFactor n i k)
  rw [← map_mul, ← map_mul]
  apply congrArg (ArchimedeanCompactFactors.toStandardCompact F n)
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      have hvw : w ≠ v := fun h => hij (congrArg Sum.inl h.symm)
      exact commute_realPlaceFactor w
        (q := ArchimedeanCompactFactors.realPlaceFactor F n v k)
        (by simp [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_of_ne hvw]) l
    | inr w =>
      exact commute_complexPlaceFactor w
        (q := ArchimedeanCompactFactors.realPlaceFactor F n v k) rfl l
  | inr v =>
    cases j with
    | inl w =>
      exact commute_realPlaceFactor w
        (q := ArchimedeanCompactFactors.complexPlaceFactor F n v k) rfl l
    | inr w =>
      have hvw : w ≠ v := fun h => hij (congrArg Sum.inr h.symm)
      exact commute_complexPlaceFactor w
        (q := ArchimedeanCompactFactors.complexPlaceFactor F n v k)
        (by simp [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_of_ne hvw]) l

/-- The single-place compact inclusions generate the entire standard compact group. -/
theorem mem_of_place_mem (n : ℕ) (H : Submonoid (standardInfiniteCompact F n))
    (hH : ∀ i k, compactInclusion n i k ∈ H) (k : standardInfiniteCompact F n) : k ∈ H := by
  classical
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  let P := H.comap (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
  change p ∈ P
  have hr : (p.1, 1) ∈ P := by
    change p.1 ∈ P.comap (MonoidHom.inl _ _)
    apply Submonoid.pi_mem_of_mulSingle_mem p.1
    intro v
    exact hH (.inl v) (p.1 v)
  have hc : (1, p.2) ∈ P := by
    change p.2 ∈ P.comap (MonoidHom.inr _ _)
    apply Submonoid.pi_mem_of_mulSingle_mem p.2
    intro v
    exact hH (.inr v) (p.2 v)
  have h := P.mul_mem hr hc
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using h

theorem compact_mem_of_placeStable {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (N : Submodule ℂ V)
    (hN : ∀ i k x, x ∈ N → κ (compactInclusion n i k) x ∈ N)
    (k : standardInfiniteCompact F n) (x : V) (hx : x ∈ N) : κ k x ∈ N := by
  let H : Submonoid (standardInfiniteCompact F n) :=
    { carrier := {k | ∀ x ∈ N, κ k x ∈ N}
      one_mem' := fun x hx => by simpa using hx
      mul_mem' := fun hk hl x hx => by
        rw [map_mul, Module.End.mul_apply]
        exact hk _ (hl x hx) }
  exact mem_of_place_mem n H hN k x hx

theorem lie_mem_of_placeStable {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (π : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V)
    (N : Submodule ℂ V)
    (hN : ∀ i X x, x ∈ N → π (lieInclusion n i X) x ∈ N)
    (Y : ComplexLieAlgebra F n) (x : V) (hx : x ∈ N) : π Y x ∈ N := by
  classical
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have heq : π (complexify F n X) x =
        (∑ v : {v : NumberField.InfinitePlace F // v.IsReal},
          π (realPlaceComplexLieInclusion F n v
            ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X)) x) +
        ∑ v : {v : NumberField.InfinitePlace F // v.IsComplex},
          π (complexPlaceComplexLieInclusion F n v
            ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X)) x := by
      have h := congrArg (fun Y : RealLieAlgebra F n => π (complexify F n Y) x)
        (sum_placeLieInclusions F n X).symm
      simpa only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
        LieHom.comp_apply, realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
        complexify_apply] using h
    have hmem : π (complexify F n X) x ∈ N := by
      rw [heq]
      exact N.add_mem (N.sum_mem fun v _ => hN (.inl v) _ x hx)
        (N.sum_mem fun v _ => hN (.inr v) _ x hx)
    have hY : (c ⊗ₜ[ℝ] X : ComplexLieAlgebra F n) = c • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hY, map_smul, LinearMap.smul_apply]
    exact N.smul_mem c hmem
  | add Y Z hY hZ =>
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem hY hZ

end InfinitePlaceFamily

local instance placeFamilyRationalGroup {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeFamilyContinuousGroup {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeFamilySmoothGroup {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeFamilyFormsGroup {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeFamilyStableGroup {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeFamilySpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

open InfinitePlaceFamily

variable {n : ℕ} (S : OperatorRealization F n)

def placeCompactFamily (i : Index F) : Representation ℂ (Compact n i) S.Space :=
  S.compactRepresentation.comp (compactInclusion n i).toMonoidHom

def placeLieFamily (i : Index F) : Lie n i →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.complexLieAction.comp (lieInclusion n i)

theorem placeOperatorFamily_commutes :
    Archimedean.FiniteFamilyPairing.FamilyCommutes S.placeCompactFamily S.placeLieFamily := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij k l x
    exact LinearMap.congr_fun
      ((map_mul S.compactRepresentation (compactInclusion n i k) (compactInclusion n j l)).symm.trans
        ((congrArg S.compactRepresentation (compactInclusion_commute n i j hij k l)).trans
          (map_mul S.compactRepresentation (compactInclusion n j l) (compactInclusion n i k)))) x
  · intro i j hij k X x
    cases i with
    | inl v =>
      cases j with
      | inl w =>
        exact S.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w
          (fun h => hij (congrArg Sum.inl h.symm)) k X x
      | inr w => exact S.realPlaceCompactRepresentation_complexPlaceLieAction v w k X x
    | inr v =>
      cases j with
      | inl w => exact S.complexPlaceCompactRepresentation_realPlaceLieAction v w k X x
      | inr w =>
        exact S.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne v w
          (fun h => hij (congrArg Sum.inr h.symm)) k X x
  · intro i j hij X Y x
    cases i with
    | inl v =>
      cases j with
      | inl w =>
        exact S.realPlaceLieAction_comm_of_ne (fun h => hij (congrArg Sum.inl h.symm)) X Y x
      | inr w => exact S.realPlaceLieAction_comm_complexPlace v w X Y x
    | inr v =>
      cases j with
      | inl w => exact (S.realPlaceLieAction_comm_complexPlace w v Y X x).symm
      | inr w =>
        exact S.complexPlaceLieAction_comm_of_ne (fun h => hij (congrArg Sum.inr h.symm)) X Y x

variable (A : Subrepresentation S.finiteRepresentation)

local instance placeFamilyFiniteFactorGroup : AddCommGroup A.toSubmodule := Submodule.addCommGroup _

def finiteMultiplicityPlaceCompact (i : Index F) :
    Representation ℂ (Compact n i) (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityCompact A).comp (compactInclusion n i).toMonoidHom

def finiteMultiplicityPlaceLie (i : Index F) :
    Lie n i →ₗ⁅ℂ⁆ Module.End ℂ (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityLie A).comp (lieInclusion n i)

@[simp]
theorem finiteMultiplicityPlaceCompact_apply (i : Index F) (k : Compact n i)
    (f : S.FiniteMultiplicity A) (a : A.toSubmodule) :
    S.finiteMultiplicityPlaceCompact A i k f a = S.placeCompactFamily i k (f a) := rfl

@[simp]
theorem finiteMultiplicityPlaceLie_apply (i : Index F) (X : Lie n i)
    (f : S.FiniteMultiplicity A) (a : A.toSubmodule) :
    S.finiteMultiplicityPlaceLie A i X f a = S.placeLieFamily i X (f a) := rfl

theorem finiteMultiplicityPlaceFamily_commutes (hne : A ≠ ⊥)
    (hA : A.toRepresentation.IsIrreducible) :
    Archimedean.FiniteFamilyPairing.FamilyCommutes
      (S.finiteMultiplicityPlaceCompact A) (S.finiteMultiplicityPlaceLie A) := by
  obtain ⟨a, haA, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  have ha₀ : (⟨a, haA⟩ : A.toSubmodule) ≠ 0 :=
    fun h => ha0 (congrArg Subtype.val h)
  have hinj := S.finiteMultiplicityEvalAt_injective A hA ha₀
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij k l f
    apply hinj
    exact S.placeOperatorFamily_commutes.1 i j hij k l (f ⟨a, haA⟩)
  · intro i j hij k X f
    apply hinj
    exact S.placeOperatorFamily_commutes.2.1 i j hij k X (f ⟨a, haA⟩)
  · intro i j hij X Y f
    apply hinj
    exact S.placeOperatorFamily_commutes.2.2 i j hij X Y (f ⟨a, haA⟩)

theorem finiteMultiplicityPlaceFamily_irreducible
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) :
    Archimedean.FiniteFamilyPairing.FamilyIrreducible
      (S.finiteMultiplicityPlaceCompact A) (S.finiteMultiplicityPlaceLie A) := by
  have h := S.finiteMultiplicity_isIrreducibleGKModule A hS hne hA ha
  refine ⟨h.1, fun N hk hl => h.2 N ?_ ?_⟩
  · exact compact_mem_of_placeStable (S.finiteMultiplicityCompact A) N hk
  · exact lie_mem_of_placeStable (S.finiteMultiplicityLie A) N hl

end OperatorRealization
end Langlands.Automorphic
