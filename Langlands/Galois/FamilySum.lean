import Langlands.Galois.CompatibleFamily
import Langlands.Weil.Representation.SumsTensor

/-!
# Direct sums of actual compatible Galois families

The algebraic sum is the published product-carrier construction. Continuity,
Euler multiplication and compatibility are proved, without imposing one
common pure weight on the summands.
-/

noncomputable section

universe uK uL uV uW

namespace Langlands.GaloisRepresentation

open Polynomial

variable {K : Type uK} [Field K]
variable {L : Type uL} [Field L]

section CoefficientObjects

variable [TopologicalSpace L]

/-- Direct sum on actual carriers, with continuity in the specified coefficient
topology proved from the linear block-diagonal map on endomorphisms. -/
def directSum (A : Objects.{uK, uL, uV} K L)
    (B : Objects.{uK, uL, uW} K L) : Objects.{uK, uL, max uV uW} K L := by
  refine ⟨FiniteRepresentation.sum A.val B.val, ?_⟩
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L _
  let : TopologicalSpace (Module.End L B.val) := moduleTopology L _
  let : TopologicalSpace (Module.End L (A.val × B.val)) := moduleTopology L _
  let : ContinuousAdd (Module.End L (A.val × B.val)) :=
    IsModuleTopology.toContinuousAdd L _
  exact (IsModuleTopology.continuous_of_linearMap
    (LinearMap.prodMapAlgHom L A.val B.val).toLinearMap).comp
      (A.property.prodMk B.property)

@[simp]
theorem directSum_rank (A : Objects.{uK, uL, uV} K L)
    (B : Objects.{uK, uL, uW} K L) :
    (directSum A B).val.rank = A.val.rank + B.val.rank :=
  Module.finrank_prod

@[simp]
theorem characteristicPolynomial_directSum
    (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uL, uW} K L)
    (g : Field.absoluteGaloisGroup K) :
    characteristicPolynomial (directSum A B) g =
      characteristicPolynomial A g * characteristicPolynomial B g :=
  LinearMap.charpoly_prodMap _ _

@[simp]
theorem eulerPolynomial_directSum
    (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uL, uW} K L)
    (g : Field.absoluteGaloisGroup K) :
    eulerPolynomial (directSum A B) g =
      eulerPolynomial A g * eulerPolynomial B g := by
  rw [eulerPolynomial, characteristicPolynomial_directSum, reverse_mul_of_domain]
  rfl

section Local

variable [NumberField K]

theorem IsUnramifiedAt.directSum
    {A : Objects.{uK, uL, uV} K L} {B : Objects.{uK, uL, uW} K L}
    {v : Global.FinitePlace K} (hA : IsUnramifiedAt A v) (hB : IsUnramifiedAt B v) :
    IsUnramifiedAt (directSum A B) v := by
  intro i
  change ((atFinitePlace v A).val.representation i.val).prodMap
    ((atFinitePlace v B).val.representation i.val) = 1
  rw [hA i, hB i, LinearMap.prodMap_one]

theorem HasEulerPolynomialAt.directSum
    {A : Objects.{uK, uL, uV} K L} {B : Objects.{uK, uL, uW} K L}
    {v : Global.FinitePlace K} {P Q : L[X]}
    (hA : HasEulerPolynomialAt A v P) (hB : HasEulerPolynomialAt B v Q) :
    HasEulerPolynomialAt (directSum A B) v (P * Q) := by
  refine ⟨hA.1.directSum hB.1, ?_⟩
  obtain ⟨g, hg, hP⟩ := hA.2
  refine ⟨g, hg, ?_⟩
  change eulerPolynomial
    (GaloisRepresentation.directSum (atFinitePlace v A) (atFinitePlace v B)) g = _
  rw [eulerPolynomial_directSum, hP, hB.forall_lifts g hg]

end Local
end CoefficientObjects

section Families

variable [NumberField K] [NumberField L]

local instance : DecidableEq (Global.FinitePlace K) := Classical.decEq _
local instance : DecidableEq (Global.FinitePlace L) := Classical.decEq _

/-- Direct sum at every retained coefficient place. The same finite coefficient
exclusion is used here; `restrictCollection` aligns different exclusions. -/
def sumCollection (excluded : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded)
    (T : Collection.{uK, uL, uW} K L excluded) :
    Collection.{uK, uL, max uV uW} K L excluded :=
  fun lam => directSum (R lam) (T lam)

theorem MatchesOutside.sumCollection
    {excluded : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L excluded}
    {S U : Finset (Global.FinitePlace K)} {P Q : Global.FinitePlace K → L[X]}
    (hR : MatchesOutside excluded R S P) (hT : MatchesOutside excluded T U Q) :
    MatchesOutside excluded (sumCollection excluded R T) (S ∪ U)
      (fun v => P v * Q v) := by
  classical
  intro lam v hv hchar
  have hvS : v ∉ S := fun h => hv (Finset.mem_union.mpr (Or.inl h))
  have hvU : v ∉ U := fun h => hv (Finset.mem_union.mpr (Or.inr h))
  simpa only [GaloisRepresentation.sumCollection, Polynomial.map_mul] using
    (hR lam v hvS hchar).directSum (hT lam v hvU hchar)

theorem IsCompatible.sumCollection
    {excluded : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L excluded}
    (hR : IsCompatible excluded R) (hT : IsCompatible excluded T) :
    IsCompatible excluded (sumCollection excluded R T) := by
  classical
  obtain ⟨S, P, hP⟩ := hR
  obtain ⟨U, Q, hQ⟩ := hT
  exact ⟨S ∪ U, fun v => P v * Q v, hP.sumCollection hQ⟩

omit [NumberField K] in
theorem HasRank.sumCollection
    {excluded : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L excluded} {n m : ℕ}
    (hR : HasRank excluded R n) (hT : HasRank excluded T m) :
    HasRank excluded (sumCollection excluded R T) (n + m) := by
  intro lam
  change (directSum (R lam) (T lam)).val.rank = n + m
  rw [directSum_rank, hR lam, hT lam]

/-- Discard more coefficient places without changing any retained representation. -/
def restrictCollection {excluded larger : Finset (Global.FinitePlace L)}
    (h : excluded ⊆ larger) (R : Collection.{uK, uL, uV} K L excluded) :
    Collection.{uK, uL, uV} K L larger :=
  fun lam => R ⟨lam.val, fun hm => lam.property (h hm)⟩

theorem MatchesOutside.restrictCollection
    {excluded larger : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {S : Finset (Global.FinitePlace K)} {P : Global.FinitePlace K → L[X]}
    (h : excluded ⊆ larger) (hR : MatchesOutside excluded R S P) :
    MatchesOutside larger (restrictCollection h R) S P := by
  intro lam v hv hchar
  exact hR ⟨lam.val, fun hm => lam.property (h hm)⟩ v hv hchar

theorem IsCompatible.restrictCollection
    {excluded larger : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    (h : excluded ⊆ larger) (hR : IsCompatible excluded R) :
    IsCompatible larger (restrictCollection h R) := by
  obtain ⟨S, P, hP⟩ := hR
  exact ⟨S, P, hP.restrictCollection h⟩

theorem IsPureCompatible.restrictCollection
    {excluded larger : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded} {w : ℤ}
    (h : excluded ⊆ larger) (hR : IsPureCompatible excluded R w) :
    IsPureCompatible larger (restrictCollection h R) w := by
  obtain ⟨S, P, hP, hw⟩ := hR
  exact ⟨S, P, hP.restrictCollection h, hw⟩

omit [NumberField K] in
theorem HasRank.restrictCollection
    {excluded larger : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded} {n : ℕ}
    (h : excluded ⊆ larger) (hR : HasRank excluded R n) :
    HasRank larger (restrictCollection h R) n :=
  fun lam => hR ⟨lam.val, fun hm => lam.property (h hm)⟩

/-- Two coefficient exclusions are combined by their finite union. -/
def unionSumCollection (excluded other : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded)
    (T : Collection.{uK, uL, uW} K L other) :
    Collection.{uK, uL, max uV uW} K L (excluded ∪ other) :=
  sumCollection (excluded ∪ other)
    (restrictCollection Finset.subset_union_left R)
    (restrictCollection Finset.subset_union_right T)

theorem IsCompatible.unionSumCollection
    {excluded other : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L other}
    (hR : IsCompatible excluded R) (hT : IsCompatible other T) :
    IsCompatible (excluded ∪ other) (unionSumCollection excluded other R T) :=
  (hR.restrictCollection Finset.subset_union_left).sumCollection
    (hT.restrictCollection Finset.subset_union_right)

omit [NumberField K] in
theorem HasRank.unionSumCollection
    {excluded other : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L other} {n m : ℕ}
    (hR : HasRank excluded R n) (hT : HasRank other T m) :
    HasRank (excluded ∪ other) (unionSumCollection excluded other R T) (n + m) :=
  (hR.restrictCollection Finset.subset_union_left).sumCollection
    (hT.restrictCollection Finset.subset_union_right)

theorem IsPureCompatible.isCompatible
    {excluded : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded} {w : ℤ}
    (hR : IsPureCompatible excluded R w) : IsCompatible excluded R := by
  obtain ⟨S, P, hP, _⟩ := hR
  exact ⟨S, P, hP⟩

/-- The sum of two pure constituents is compatible even when their weights differ.
No single pure weight is asserted for that sum. -/
theorem IsPureCompatible.unionSum_isCompatible
    {excluded other : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {T : Collection.{uK, uL, uW} K L other} {w z : ℤ}
    (hR : IsPureCompatible excluded R w) (hT : IsPureCompatible other T z) :
    IsCompatible (excluded ∪ other) (unionSumCollection excluded other R T) :=
  hR.isCompatible.unionSumCollection hT.isCompatible

end Families

end Langlands.GaloisRepresentation
