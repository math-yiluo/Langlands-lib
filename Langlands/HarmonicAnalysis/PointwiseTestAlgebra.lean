import Langlands.HarmonicAnalysis.PointwiseTestAlgebraCore
import Langlands.Algebra.IdempotentedRing

/-!
# Compact-clopen characteristic idempotents and finite local units

Renard (9 July 2026), II.2.4–II.2.5, printed pp.38–40 / PDF44–46.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.PointwiseTestAlgebra

universe uX uI

variable {X : Type uX} [TopologicalSpace X]

/-- The actual compact-clopen indicator, transported without changing any values. -/
def characteristic {U : Set X} (hU : IsClopen U) (hc : IsCompact U) : Carrier X :=
  scalarEquiv.symm (Hecke.TestFunction.characteristic hU hc)

@[simp]
theorem characteristic_apply {U : Set X} (hU : IsClopen U) (hc : IsCompact U) (x : X) :
    characteristic hU hc x = U.indicator (fun _ => (1 : ℂ)) x := rfl

@[simp]
theorem scalarEquiv_characteristic {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    scalarEquiv (characteristic hU hc) = Hecke.TestFunction.characteristic hU hc :=
  scalarEquiv.apply_symm_apply _

@[simp]
theorem inclusion_characteristic {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    inclusion (characteristic hU hc) = LocallyConstant.charFn ℂ hU := rfl

theorem support_characteristic {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    Function.support (characteristic hU hc : X → ℂ) = U :=
  Hecke.TestFunction.support_characteristic hU hc

@[simp]
theorem characteristic_empty :
    characteristic (X := X) isClopen_empty isCompact_empty = 0 := by
  ext x
  simp

theorem characteristic_mul {U V : Set X} (hU : IsClopen U) (hUc : IsCompact U)
    (hV : IsClopen V) (hVc : IsCompact V) :
    characteristic hU hUc * characteristic hV hVc =
      characteristic (hU.inter hV) (hUc.inter_right hV.isClosed) := by
  classical
  ext x
  by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;>
    simp [characteristic_apply, hu, hv]

theorem characteristic_idempotent {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    IsIdempotentElem (characteristic hU hc) := by
  classical
  change characteristic hU hc * characteristic hU hc = characteristic hU hc
  ext x
  by_cases hx : x ∈ U <;> simp [characteristic_apply, hx]

/-- The compact-clopen indicator as an idempotent in the public corner-order API. -/
def characteristicIdempotent {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    Langlands.Algebra.Idempotent (Carrier X) :=
  ⟨characteristic hU hc, characteristic_idempotent hU hc⟩

theorem characteristic_mul_eq_self_iff {U : Set X} (hU : IsClopen U) (hc : IsCompact U)
    (f : Carrier X) :
    characteristic hU hc * f = f ↔ Function.support f ⊆ U := by
  classical
  constructor
  · intro h x hx
    by_contra hxu
    have hz := congrArg (fun g : Carrier X => g x) h
    exact hx (by simpa [characteristic_apply, hxu] using hz.symm)
  · intro h
    ext x
    by_cases hx : x ∈ U
    · simp [characteristic_apply, hx]
    · have hf : f x = 0 := by
        by_contra hn
        exact hx (h hn)
      simp [characteristic_apply, hx, hf]

theorem mul_characteristic_eq_self_iff {U : Set X} (hU : IsClopen U) (hc : IsCompact U)
    (f : Carrier X) :
    f * characteristic hU hc = f ↔ Function.support f ⊆ U := by
  rw [mul_comm]
  exact characteristic_mul_eq_self_iff hU hc f

theorem characteristic_mul_of_subset {U V : Set X} (hU : IsClopen U) (hUc : IsCompact U)
    (hV : IsClopen V) (hVc : IsCompact V) (hUV : U ⊆ V) :
    characteristic hU hUc * characteristic hV hVc = characteristic hU hUc := by
  apply (mul_characteristic_eq_self_iff hV hVc _).mpr
  simpa only [support_characteristic] using hUV

theorem characteristicIdempotent_le {U V : Set X} (hU : IsClopen U) (hUc : IsCompact U)
    (hV : IsClopen V) (hVc : IsCompact V) (hUV : U ⊆ V) :
    characteristicIdempotent hU hUc ≤ characteristicIdempotent hV hVc := by
  apply (Langlands.Algebra.Idempotent.le_iff_mul _ _).mpr
  have h := characteristic_mul_of_subset hU hUc hV hVc hUV
  change characteristic hV hVc * characteristic hU hUc = characteristic hU hUc ∧
    characteristic hU hUc * characteristic hV hVc = characteristic hU hUc
  exact ⟨by rw [mul_comm]; exact h, h⟩

theorem characteristic_union {U V : Set X} (hU : IsClopen U) (hUc : IsCompact U)
    (hV : IsClopen V) (hVc : IsCompact V) :
    characteristic (hU.union hV) (hUc.union hVc) =
      characteristic hU hUc + characteristic hV hVc -
        characteristic (hU.inter hV) (hUc.inter_right hV.isClosed) := by
  classical
  ext x
  change characteristic (hU.union hV) (hUc.union hVc) x =
    characteristic hU hUc x + characteristic hV hVc x -
      characteristic (hU.inter hV) (hUc.inter_right hV.isClosed) x
  by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;>
    simp [characteristic_apply, hu, hv]

theorem characteristic_union_disjoint {U V : Set X} (hU : IsClopen U) (hUc : IsCompact U)
    (hV : IsClopen V) (hVc : IsCompact V) (hd : Disjoint U V) :
    characteristic (hU.union hV) (hUc.union hVc) =
      characteristic hU hUc + characteristic hV hVc := by
  classical
  ext x
  by_cases hu : x ∈ U <;> by_cases hv : x ∈ V
  · exact (Set.disjoint_left.mp hd hu hv).elim
  all_goals simp [characteristic_apply, hu, hv]

/-- The indicator of a finite union of compact-clopen sets, including an empty union. -/
def finiteUnionCharacteristic {ι : Type uI} (s : Finset ι) (U : ι → Set X)
    (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) : Carrier X :=
  characteristic (isClopen_biUnion_finset (fun i _ => hU i))
    (s.isCompact_biUnion (fun i _ => hc i))

@[simp]
theorem finiteUnionCharacteristic_apply {ι : Type uI} (s : Finset ι) (U : ι → Set X)
    (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) (x : X) :
    finiteUnionCharacteristic s U hU hc x =
      (⋃ i ∈ s, U i).indicator (fun _ => (1 : ℂ)) x := rfl

@[simp]
theorem finiteUnionCharacteristic_empty {ι : Type uI} (U : ι → Set X)
    (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) :
    finiteUnionCharacteristic ∅ U hU hc = 0 := by
  ext x
  simp

/-- The insertion recurrence gives the indicator law for every finite union. -/
theorem finiteUnionCharacteristic_insert {ι : Type uI} [DecidableEq ι]
    (s : Finset ι) (i : ι) (U : ι → Set X)
    (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) :
    finiteUnionCharacteristic (insert i s) U hU hc =
      characteristic (hU i) (hc i) + finiteUnionCharacteristic s U hU hc -
        characteristic (hU i) (hc i) * finiteUnionCharacteristic s U hU hc := by
  classical
  ext x
  change finiteUnionCharacteristic (insert i s) U hU hc x =
    characteristic (hU i) (hc i) x + finiteUnionCharacteristic s U hU hc x -
      characteristic (hU i) (hc i) x * finiteUnionCharacteristic s U hU hc x
  by_cases hi : x ∈ U i <;> by_cases hs : x ∈ ⋃ j ∈ s, U j <;>
    simp [finiteUnionCharacteristic_apply, characteristic_apply, hi, hs]

theorem finiteUnionCharacteristic_mul {ι : Type uI} (s : Finset ι) (i : ι)
    (hi : i ∈ s) (U : ι → Set X)
    (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) :
    finiteUnionCharacteristic s U hU hc * characteristic (hU i) (hc i) =
      characteristic (hU i) (hc i) := by
  apply (characteristic_mul_eq_self_iff _ _ _).mpr
  rw [support_characteristic]
  exact fun x hx => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩

/-- The finite union of the actual compact-clopen supports of the tests. -/
def finiteSupport (s : Finset (Carrier X)) : Set X := ⋃ f ∈ s, Function.support f

theorem finiteSupport_isClopen (s : Finset (Carrier X)) : IsClopen (finiteSupport s) :=
  isClopen_biUnion_finset (fun f _ => isClopen_support f)

theorem finiteSupport_isCompact (s : Finset (Carrier X)) : IsCompact (finiteSupport s) :=
  s.isCompact_biUnion (fun f _ => isCompact_support f)

/-- A specified characteristic local unit for the whole finite family. -/
def localUnit (s : Finset (Carrier X)) : Carrier X :=
  characteristic (finiteSupport_isClopen s) (finiteSupport_isCompact s)

theorem localUnit_idempotent (s : Finset (Carrier X)) : IsIdempotentElem (localUnit s) :=
  characteristic_idempotent _ _

theorem support_localUnit (s : Finset (Carrier X)) :
    Function.support (localUnit s : X → ℂ) = finiteSupport s :=
  support_characteristic _ _

@[simp]
theorem localUnit_empty : localUnit (∅ : Finset (Carrier X)) = 0 := by
  ext x
  simp [localUnit, finiteSupport]

theorem localUnit_mul (s : Finset (Carrier X)) {f : Carrier X} (hf : f ∈ s) :
    localUnit s * f = f := by
  apply (characteristic_mul_eq_self_iff _ _ _).mpr
  exact fun x hx => Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hx⟩⟩

theorem mul_localUnit (s : Finset (Carrier X)) {f : Carrier X} (hf : f ∈ s) :
    f * localUnit s = f := by
  rw [mul_comm]
  exact localUnit_mul s hf

theorem exists_characteristic_local_unit (s : Finset (Carrier X)) :
    ∃ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
      ∀ f ∈ s, characteristic hU hc * f = f ∧ f * characteristic hU hc = f :=
  ⟨finiteSupport s, finiteSupport_isClopen s, finiteSupport_isCompact s,
    fun _ hf => ⟨localUnit_mul s hf, mul_localUnit s hf⟩⟩

/-- Renard II.2.4: the actual pointwise test algebra is idempotented. -/
theorem isIdempotented : Langlands.Algebra.IsIdempotented (Carrier X) := by
  apply Langlands.Algebra.IsIdempotented.iff_two_sided_local_units.mpr
  intro s
  exact ⟨characteristicIdempotent (finiteSupport_isClopen s) (finiteSupport_isCompact s),
    fun _ hf => ⟨localUnit_mul s hf, mul_localUnit s hf⟩⟩

/-- Finite families may have an index type in a universe independent of the space. -/
theorem finite_family_local_unit {ι : Type uI} [Finite ι] (f : ι → Carrier X) :
    ∃ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
      ∀ i, characteristic hU hc * f i = f i ∧ f i * characteristic hU hc = f i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨U, hU, hc, h⟩ := exists_characteristic_local_unit (Finset.univ.image f)
  exact ⟨U, hU, hc, fun i =>
    h (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩

/-- A compact open is clopen in the source's Hausdorff convention. -/
def characteristicOfCompactOpen [T2Space X] {U : Set X} (hU : IsOpen U)
    (hc : IsCompact U) : Carrier X :=
  characteristic ⟨hc.isClosed, hU⟩ hc

@[simp]
theorem characteristicOfCompactOpen_apply [T2Space X] {U : Set X} (hU : IsOpen U)
    (hc : IsCompact U) (x : X) :
    characteristicOfCompactOpen hU hc x = U.indicator (fun _ => (1 : ℂ)) x := rfl

end Langlands.HarmonicAnalysis.PointwiseTestAlgebra
