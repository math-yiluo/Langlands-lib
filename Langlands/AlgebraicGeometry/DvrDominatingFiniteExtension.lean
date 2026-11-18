import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion

/-! # A DVR dominating a DVR inside a finite extension of its fraction field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension

/-- For a DVR `R` and a finite field extension `L` of `FractionRing R`, a valuation subring of
`L` that is a discrete valuation ring, contains the image of `R` and dominates `R`, for the
`R`-algebra structure `R → FractionRing R → L`. It is chosen using the Library lemma
`NoetherianValuativeCriterion.exists_valuationSubring_dominates`. -/
def dominatingValuationSubring (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] : ValuationSubring L :=
  letI : Algebra R L :=
    ((algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  Classical.choose
    (NoetherianValuativeCriterion.exists_valuationSubring_dominates (A := R)
      (IsDiscreteValuationRing.ringKrullDim_eq_one R) (K := FractionRing R) (L := L))

/-- The defining properties of `dominatingValuationSubring R L`: it is a DVR, it contains the
image of `R`, and an element of `R` lies in the maximal ideal exactly when its image is a
nonunit of the valuation subring. -/
theorem dominatingValuationSubring_spec (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] :
    IsDiscreteValuationRing (dominatingValuationSubring R L) ∧
      (∀ a : R, algebraMap (FractionRing R) L (algebraMap R (FractionRing R) a) ∈
        dominatingValuationSubring R L) ∧
      (∀ a : R, a ∈ maximalIdeal R ↔
        algebraMap (FractionRing R) L (algebraMap R (FractionRing R) a) ∈
          (dominatingValuationSubring R L).nonunits) :=
  letI : Algebra R L :=
    ((algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  Classical.choose_spec
    (NoetherianValuativeCriterion.exists_valuationSubring_dominates (A := R)
      (IsDiscreteValuationRing.ringKrullDim_eq_one R) (K := FractionRing R) (L := L))

/-- Given a DVR `R` and a finite field extension `L` of its fraction field, there is a DVR
`R'` in the same universe, faithfully flat over `R`, whose fraction field receives `L`
compatibly with `R → R'`. -/
theorem exists_dvr_of_finite_extension (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] :
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R') (aR' : Algebra R R'),
          letI := aR'
          ∃ (σ : L →+* FractionRing R'),
            (algebraMap R R').FaithfullyFlat ∧
            Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
            Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
            σ.comp ((algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))) =
              (algebraMap R' (FractionRing R')).comp (algebraMap R R') := by
  classical
  let K := FractionRing R
  let _ : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let V := dominatingValuationSubring R L
  obtain ⟨hVdvr, hRV, hdom⟩ := dominatingValuationSubring_spec R L
  let j : R →+* V := (algebraMap R L).codRestrict V hRV
  let _ : Algebra R V := j.toAlgebra
  have hj : ∀ r : R, (j r : L) = algebraMap R L r := fun _ => rfl
  have hinjL : Function.Injective (algebraMap R L) := by
    show Function.Injective ((algebraMap K L).comp (algebraMap R K))
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hinj : Function.Injective j := fun a b hab => hinjL (by rw [← hj, ← hj, hab])
  have hloc : IsLocalHom (algebraMap R V) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal R := (mem_maximalIdeal _).2 hna
    have h2 : algebraMap R L a ∈ V.nonunits := (hdom a).1 h1
    rw [← hj, ValuationSubring.coe_mem_nonunits_iff] at h2
    exact (mem_maximalIdeal _).1 h2 ha
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by rw [map_zero]; exact h))
    · exact Or.inr h
  have : Module.Flat R V := inferInstance
  have : Module.FaithfullyFlat R V := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff : (algebraMap R V).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
  have hspec := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R V))).2 hff
  let e : L ≃ₐ[V] FractionRing V := (FractionRing.algEquiv V L).symm
  refine ⟨V, inferInstance, inferInstance, hVdvr, inferInstance, e.toRingEquiv.toRingHom,
    hff, hspec.1, hspec.2, ?_⟩
  ext r
  show e (algebraMap R L r) = algebraMap V (FractionRing V) (j r)
  rw [← hj]
  exact e.commutes (j r)

end Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension
