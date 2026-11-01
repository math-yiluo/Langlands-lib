import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalFiniteTypeSubalgebraStatement
import Mathlib.RingTheory.Localization.FractionRing

/-! # Finite stages inside a chosen fraction field -/

universe u v

noncomputable section

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fraction field of an actual integer subalgebra embeds in the given
fraction field through its inclusion in `R`. -/
def stageFractionFieldMap (T : Subalgebra ℤ R) : FractionRing ↥T →+* K :=
  IsFractionRing.lift (A := ↥T) (K := FractionRing ↥T)
    (g := (algebraMap R K).comp T.val.toRingHom)
    ((IsFractionRing.injective R K).comp (show Function.Injective T.val from
      Subtype.val_injective))

@[simp]
theorem stageFractionFieldMap_algebraMap (T : Subalgebra ℤ R) (x : T) :
    stageFractionFieldMap R K T (algebraMap T (FractionRing T) x) =
      algebraMap R K x.val :=
  IsFractionRing.lift_algebraMap _ _

theorem stageFractionFieldMap_injective (T : Subalgebra ℤ R) :
    Function.Injective (stageFractionFieldMap R K T) :=
  (stageFractionFieldMap R K T).injective

/-- Finitely many elements of the chosen field are fractions of elements
of one finite subset of the original ring. Every subalgebra containing that
subset contains these field elements in the image of its fraction field. -/
theorem exists_finset_fractionFieldData (sR : Finset R) (sK : Finset K) :
    ∃ t : Finset R, sR ⊆ t ∧
      ∀ T : Subalgebra ℤ R, (↑t : Set R) ⊆ T →
        (↑sK : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange := by
  classical
  choose n d hd heq using fun x : K => IsFractionRing.div_surjective R x
  let t := sR ∪ (sK.image n ∪ sK.image d)
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_union_left _ hx
  intro T ht x hx
  have hnT : n x ∈ T := ht (by
    change n x ∈ t
    simp only [t, Finset.mem_union]
    exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
  have hdT : d x ∈ T := ht (by
    change d x ∈ t
    simp only [t, Finset.mem_union]
    exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
  refine ⟨algebraMap T (FractionRing T) ⟨n x, hnT⟩ /
    algebraMap T (FractionRing T) ⟨d x, hdT⟩, ?_⟩
  simpa only [map_div₀, stageFractionFieldMap_algebraMap] using heq x

/-- The finite-data bridge always has a finitely generated stage. -/
theorem exists_fg_fractionFieldStage (sR : Finset R) (sK : Finset K) :
    ∃ T : Subalgebra ℤ R, T.FG ∧ (↑sR : Set R) ⊆ T ∧
      (↑sK : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange := by
  obtain ⟨t, hst, ht⟩ := exists_finset_fractionFieldData R K sR sK
  refine ⟨Algebra.adjoin ℤ (↑t : Set R), Subalgebra.fg_adjoin_finset t, ?_,
    ht _ Algebra.subset_adjoin⟩
  intro x hx
  exact Algebra.subset_adjoin (hst hx)

/-- Under the separately stated normal-subalgebra existence theorem, the
same finite data can be placed in a normal noetherian stage. -/
theorem exists_normal_fractionFieldStage
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    [IsIntegrallyClosed R] (sR : Finset R) (sK : Finset K) :
    ∃ T : Subalgebra ℤ R, T.FG ∧ (↑sR : Set R) ⊆ T ∧
      IsIntegrallyClosed ↥T ∧ IsNoetherianRing ↥T ∧
      (↑sK : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange := by
  obtain ⟨t, hst, ht⟩ := exists_finset_fractionFieldData R K sR sK
  obtain ⟨T, hfg, hT, hn, hnoeth⟩ := hNormal R t
  exact ⟨T, hfg, fun _ hx => hT (hst hx), hn, hnoeth, ht T hT⟩

/-- A subalgebra contained in a fraction-field image has an actual ring
map into that fraction field, obtained from the inverse range equivalence. -/
def factorToStageFractionField (T : Subalgebra ℤ R) (B : Subalgebra ℤ K)
    (hB : (B : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange) :
    B →+* FractionRing T :=
  (stageFractionFieldMap R K T).rangeRestrictFieldEquiv.symm.toRingHom.comp
    (B.val.toRingHom.codRestrict (stageFractionFieldMap R K T).fieldRange
      fun x => hB x.property)

@[simp]
theorem stageFractionFieldMap_factorToStageFractionField
    (T : Subalgebra ℤ R) (B : Subalgebra ℤ K)
    (hB : (B : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange) (x : B) :
    stageFractionFieldMap R K T (factorToStageFractionField R K T B hB x) = x.val := by
  exact (stageFractionFieldMap R K T).rangeRestrictFieldEquiv_apply_symm_apply _

theorem factorToStageFractionField_injective
    (T : Subalgebra ℤ R) (B : Subalgebra ℤ K)
    (hB : (B : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange) :
    Function.Injective (factorToStageFractionField R K T B hB) := by
  intro x y h
  apply Subtype.ext
  simpa only [stageFractionFieldMap_factorToStageFractionField] using
    congrArg (stageFractionFieldMap R K T) h

/-- A finitely generated field subalgebra, together with finite data in
the original ring, admits a compatible factorization through a finite stage.
Normality is conditional on the separate normal-subalgebra statement. -/
theorem exists_normal_fractionFieldFactor
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    [IsIntegrallyClosed R] (sR : Finset R) (B : Subalgebra ℤ K) (hB : B.FG) :
    ∃ T : Subalgebra ℤ R, T.FG ∧ (↑sR : Set R) ⊆ T ∧
      IsIntegrallyClosed ↥T ∧ IsNoetherianRing ↥T ∧
      ∃ f : B →+* FractionRing T,
        Function.Injective f ∧
          (stageFractionFieldMap R K T).comp f = B.val.toRingHom := by
  obtain ⟨sK, hsK⟩ := hB
  obtain ⟨T, hfg, hsR, hn, hnoeth, hs⟩ :=
    exists_normal_fractionFieldStage R K hNormal sR sK
  have hBT : (B : Set K) ⊆ (stageFractionFieldMap R K T).fieldRange := by
    have hle : B ≤ subalgebraOfSubring
        (stageFractionFieldMap R K T).fieldRange.toSubring := by
      rw [← hsK]
      exact Algebra.adjoin_le hs
    exact hle
  refine ⟨T, hfg, hsR, hn, hnoeth, factorToStageFractionField R K T B hBT,
    factorToStageFractionField_injective R K T B hBT, ?_⟩
  ext x
  exact stageFractionFieldMap_factorToStageFractionField R K T B hBT x

end Langlands.AlgebraicGeometry.NoetherianApproximation
