import Langlands.Analysis.Local.NormalSubgroupModularCharacter
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Induction.CompactQuotientDuality
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Algebra.BigOperators.Finprod

/-! # Modular characters of actual restricted products -/

noncomputable section

universe u v

open MeasureTheory MeasureTheory.Measure Topology
open scoped RestrictedProduct NNReal

namespace Langlands.RestrictedProductMeasure

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
  (K : ∀ i, Subgroup (G i))
  [hKopen : Fact (∀ i, IsOpen (K i : Set (G i)))] [∀ i, CompactSpace (K i)]

private def coordinateSubgroup (i : ι) : Subgroup (Πʳ j, [G j, K j]) where
  carrier := {x | ∀ j, j ≠ i → x j = 1}
  one_mem' := by simp
  mul_mem' hx hy j hj := by simp [hx j hj, hy j hj]
  inv_mem' hx j hj := by simp [hx j hj]

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  hKopen [∀ i, CompactSpace (K i)] in
private theorem coordinateSubgroup_closed (i : ι) :
    IsClosed (coordinateSubgroup K i : Set (Πʳ j, [G j, K j])) := by
  change IsClosed {x : Πʳ j, [G j, K j] | ∀ j, j ≠ i → x j = 1}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (RestrictedProduct.continuous_eval j) continuous_const

private instance coordinateSubgroup_normal (i : ι) : (coordinateSubgroup K i).Normal where
  conj_mem x hx y j hj := by
    change y j * x j * (y j)⁻¹ = 1
    simp [hx j hj]

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
  [∀ i, LocallyCompactSpace (G i)] hKopen [∀ i, CompactSpace (K i)] in
private theorem continuous_mulSingle [DecidableEq ι] (i : ι) :
    Continuous (RestrictedProduct.mulSingle K i) := by
  classical
  let S : Set ι := {i}ᶜ
  let f : G i → Πʳ j, [G j, K j]_[Filter.principal S] :=
    fun g => ⟨Pi.mulSingle i g, fun j hj => by
      have hji : j ≠ i := by simpa [S] using hj
      simp [Pi.mulSingle_eq_of_ne hji]⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.mpr (_root_.continuous_mulSingle i)
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

private def coordinateEquiv [DecidableEq ι] (i : ι) : G i ≃ₜ* coordinateSubgroup K i := by
  classical
  exact
    { toFun := fun g => ⟨RestrictedProduct.mulSingle K i g, fun j hj =>
        RestrictedProduct.mulSingle_eq_of_ne K g hj⟩
      invFun := fun x => x.val i
      left_inv := fun g => RestrictedProduct.mulSingle_eq_same K i g
      right_inv := fun x => by
        apply Subtype.ext
        apply RestrictedProduct.ext
        intro j
        by_cases hji : j = i
        · subst j
          exact RestrictedProduct.mulSingle_eq_same K i _
        · rw [RestrictedProduct.mulSingle_eq_of_ne K _ hji, x.property j hji]
      map_mul' := fun g h => Subtype.ext (RestrictedProduct.mulSingle_mul K i g h)
      continuous_toFun := (continuous_mulSingle K i).subtype_mk _
      continuous_invFun := (RestrictedProduct.continuous_eval i).comp continuous_subtype_val }

/-- A single local coordinate has its original modular character in the restricted product. -/
theorem modularCharacter_mulSingle [DecidableEq ι] (i : ι) (g : G i) :
    modularCharacter (RestrictedProduct.mulSingle K i g) = modularCharacter g := by
  classical
  let R := Πʳ j, [G j, K j]
  let H := coordinateSubgroup K i
  have hH : IsClosed (H : Set R) := coordinateSubgroup_closed K i
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace R := borel R
  let : BorelSpace R := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (Langlands.QuotientIntegration.LeftQuotient H) := borel (Langlands.QuotientIntegration.LeftQuotient H)
  let : BorelSpace (Langlands.QuotientIntegration.LeftQuotient H) := ⟨rfl⟩
  let : MeasurableSpace (R ⧸ H) := borel (R ⧸ H)
  let : BorelSpace (R ⧸ H) := ⟨rfl⟩
  exact (Langlands.QuotientIntegration.modularCharacter_normalSubgroup H hH
    (coordinateEquiv K i g)).symm.trans
    (Langlands.Aubert.General.modularCharacter_continuousMulEquiv (coordinateEquiv K i) g)

private def integralSubgroup : Subgroup (Πʳ i, [G i, K i]) where
  carrier := {x | ∀ i, x i ∈ K i}
  one_mem' := fun i => (K i).one_mem
  mul_mem' hx hy i := (K i).mul_mem (hx i) (hy i)
  inv_mem' hx i := (K i).inv_mem (hx i)

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
  [∀ i, LocallyCompactSpace (G i)] [∀ i, CompactSpace (K i)] in
private theorem integralSubgroup_open :
    IsOpen (integralSubgroup K : Set (Πʳ i, [G i, K i])) :=
  RestrictedProduct.isOpen_forall_mem hKopen.out

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
  [∀ i, LocallyCompactSpace (G i)] hKopen in
private theorem integralSubgroup_compact :
    IsCompact (integralSubgroup K : Set (Πʳ i, [G i, K i])) := by
  rw [show (integralSubgroup K : Set (Πʳ i, [G i, K i])) =
    Set.range (RestrictedProduct.structureMap G (fun i => (K i : Set (G i)))
      Filter.cofinite) from (RestrictedProduct.range_structureMap _ _).symm]
  exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)

omit [∀ i, T2Space (G i)] in
/-- The local modular character is one on each distinguished compact open subgroup. -/
theorem local_modularCharacter_eq_one (i : ι) {g : G i} (hg : g ∈ K i) :
    modularCharacter g = 1 :=
  Langlands.Induction.modularCharacter_eq_one_of_isCompact (K i) (hKopen.out i)
    (isCompact_iff_compactSpace.mpr inferInstance) hg

omit [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] in
/-- The restricted-product modular character is one when every coordinate is integral. -/
theorem modularCharacter_eq_one_of_forall_mem (x : Πʳ i, [G i, K i])
    (hx : ∀ i, x i ∈ K i) : modularCharacter x = 1 :=
  Langlands.Induction.modularCharacter_eq_one_of_isCompact (integralSubgroup K)
    (integralSubgroup_open K) (integralSubgroup_compact K) hx

/-- A finite set containing the exceptional coordinates computes the modular character. -/
theorem modularCharacter_eq_prod (s : Finset ι) (x : Πʳ i, [G i, K i])
    (hx : ∀ i, i ∉ s → x i ∈ K i) :
    modularCharacter x = ∏ i ∈ s, modularCharacter (x i) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simpa using modularCharacter_eq_one_of_forall_mem K x (fun i => hx i (by simp))
  | @insert a s ha ih =>
    let y := (RestrictedProduct.mulSingle K a (x a))⁻¹ * x
    have hy : ∀ i, i ∉ s → y i ∈ K i := by
      intro i hi
      by_cases hia : i = a
      · subst i
        simp [y]
      · simpa [y, RestrictedProduct.mulSingle_eq_of_ne K _ hia] using
          hx i (by simp [hia, hi])
    have hxy : x = RestrictedProduct.mulSingle K a (x a) * y := by simp [y]
    calc
      modularCharacter x =
          modularCharacter (RestrictedProduct.mulSingle K a (x a)) * modularCharacter y := by
        conv_lhs => rw [hxy, map_mul]
      _ = modularCharacter (x a) * ∏ i ∈ s, modularCharacter (y i) := by
        rw [modularCharacter_mulSingle K a (x a), ih y hy]
      _ = ∏ i ∈ insert a s, modularCharacter (x i) := by
        rw [Finset.prod_insert ha]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        simp [y, RestrictedProduct.mulSingle_eq_of_ne K _ hia]

omit [∀ i, T2Space (G i)] in
/-- Local modular values of a restricted-product point have finite multiplicative support. -/
theorem hasFiniteMulSupport_modularCharacter (x : Πʳ i, [G i, K i]) :
    Function.HasFiniteMulSupport (fun i => modularCharacter (x i)) := by
  apply (Filter.eventually_cofinite.mp x.eventually).subset
  intro i hi hx
  exact hi (local_modularCharacter_eq_one K i hx)

/-- The intrinsic modular character is the finite product of the actual local modular values. -/
theorem modularCharacter_eq_finprod (x : Πʳ i, [G i, K i]) :
    modularCharacter x = ∏ᶠ i, modularCharacter (x i) := by
  classical
  let s := (Filter.eventually_cofinite.mp x.eventually).toFinset
  have hs : ∀ i, i ∉ s → x i ∈ K i := by
    intro i hi
    simpa [s] using hi
  rw [modularCharacter_eq_prod K s x hs]
  exact (finprod_eq_prod_of_mulSupport_subset _ (by
    intro i hi
    by_contra his
    exact hi (local_modularCharacter_eq_one K i (hs i his)))).symm

/-- The local finite-product expression as a homomorphism on the actual restricted product. -/
def modularCharacterHom : (Πʳ i, [G i, K i]) →* ℝ≥0 where
  toFun x := ∏ᶠ i, modularCharacter (x i)
  map_one' := by simp
  map_mul' x y := by
    simp only [← modularCharacter_eq_finprod K, map_mul]

@[simp] theorem modularCharacterHom_apply (x : Πʳ i, [G i, K i]) :
    modularCharacterHom K x = modularCharacter x :=
  (modularCharacter_eq_finprod K x).symm

/-- Positive right translation scales fixed Haar by the finite product of local modular values. -/
theorem map_mul_right_haar_eq_finprod
    [MeasurableSpace (Πʳ i, [G i, K i])] [BorelSpace (Πʳ i, [G i, K i])]
    (x : Πʳ i, [G i, K i]) :
    Measure.map (· * x) (haar : Measure (Πʳ i, [G i, K i])) =
      (∏ᶠ i, modularCharacter (x i)) • haar := by
  rw [Langlands.Induction.map_mul_right_haar_eq, modularCharacter_eq_finprod K x]

end Langlands.RestrictedProductMeasure
