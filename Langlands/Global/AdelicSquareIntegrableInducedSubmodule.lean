import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Mathlib.MeasureTheory.Function.L2Space

/-! # The complex submodule of square-integrable adelic inducing forms

The half-modulus-normalized Levi restriction is linear and has squared norm equal to
the weighted square in `IsSquareIntegrableInducedForm`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open InducedInnerProductIntegrable

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) (K : Subgroup (AdelicGroupPoints F G))

private def normalizedLeviRestriction :
    (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (K × RestrictionSplitCentre.CanonicalQuotient F M → ℂ) where
  toFun φ z :=
    parameterPower F P (-halfModulusParameter F P) (map F M P l z.2.out) *
      φ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G))
  map_add' φ ψ := by
    ext z
    simp only [Pi.add_apply, mul_add]
  map_smul' c φ := by
    ext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem continuous_normalizedLeviRestriction {φ : AdelicGroupPoints F G → ℂ}
    {iU : U ⟶ P} (hc : Continuous φ)
    (hi : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (he : IsSplitComponentEquivariant p l φ) :
    Continuous (normalizedLeviRestriction p l K φ) := by
  let f : K → AdelicGroupPoints F M → ℂ := fun k m =>
    parameterPower F P (-halfModulusParameter F P) (map F M P l m) *
      φ (map F P G p (map F M P l m) * (k : AdelicGroupPoints F G))
  have hMc : Continuous (fun z : K × AdelicGroupPoints F M => map F M P l z.2) :=
    (map F M P l).continuous.comp continuous_snd
  have hf : Continuous (fun z : K × AdelicGroupPoints F M => f z.1 z.2) :=
    ((continuous_parameterPower _).comp hMc).mul
      (hc.comp (((map F P G p).continuous.comp hMc).mul
        (continuous_subtype_val.comp continuous_fst)))
  refine LeftCosetSpace.continuous_out_of_invariant
    (RestrictionSplitCentre.canonicalRationalSubgroup F M) f hf (fun k => ?_)
  refine LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
    (Δ := rationalSubgroup F M) (f k) ?_ ?_
  · intro a ha m
    have hcancel : parameterPower F P (-halfModulusParameter F P) (map F M P l a) *
        parameterPower F P (halfModulusParameter F P) (map F M P l a) = 1 := by
      rw [← parameterPower_add, neg_add_cancel, parameterPower_zero]
    dsimp only [f]
    rw [form_canonical_mul he ha, map_mul (map F M P l) a m, parameterPower_mul]
    rw [mul_mul_mul_comm, hcancel, one_mul]
  · intro a ha m
    dsimp only [f]
    rw [parameterPower_map_mul_left _ l (rationalSubgroup_le_normOneSubgroup F M ha),
      form_rational_mul hi ha]

variable {K} (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : U ⟶ P)

local notation "μKM" =>
  Measure.prod (compactHaarProbability F G K hKc) (RestrictionSplitCentre.canonicalMeasure F M)

local notation "AutForms" =>
  automorphicFunctionsOn (parabolicQuotientSubgroup F p iU l)
    (Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K) rho hsmooth hcalc

omit [LocallyOfFiniteType G.X.hom] in
private theorem integrable_sq_norm_normalizedLeviRestriction_iff {φ : AdelicGroupPoints F G → ℂ} :
    Integrable (fun z => ‖normalizedLeviRestriction p l K φ z‖ ^ 2) μKM ↔
      Integrable (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
        ‖parameterPower F P (-modulusParameter F P) (map F M P l z.2.out)‖ *
          ‖φ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G))‖ ^ 2) μKM := by
  have hpar : -halfModulusParameter F P + -halfModulusParameter F P = -modulusParameter F P := by
    have h := neg_modulus_add_half_add_half (F := F) (P := P)
    calc
      _ = (-modulusParameter F P + halfModulusParameter F P + halfModulusParameter F P) +
          (-halfModulusParameter F P + -halfModulusParameter F P) := by rw [h, zero_add]
      _ = _ := by abel
  refine integrable_congr (Filter.Eventually.of_forall (fun z => ?_))
  change ‖parameterPower F P (-halfModulusParameter F P) (map F M P l z.2.out) * _‖ ^ 2 = _
  rw [norm_mul, mul_pow, sq ‖parameterPower F P (-halfModulusParameter F P) (map F M P l z.2.out)‖,
    ← norm_mul, ← parameterPower_add, hpar]

private theorem memLp_normalizedLeviRestriction {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ) :
    MemLp (normalizedLeviRestriction p l K φ) 2 μKM := by
  let : OpensMeasurableSpace (RestrictionSplitCentre.CanonicalQuotient F M) :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr (fun _ hs =>
      measurableSet_quotient.mpr
        (hs.preimage (LeftCosetSpace.continuous_mk
          (RestrictionSplitCentre.canonicalRationalSubgroup F M))).measurableSet)
  have hc := continuous_normalizedLeviRestriction p l K hφ.1.2.1.1 hφ.1.1 hφ.2.1
  exact (memLp_two_iff_integrable_sq_norm hc.measurable.aestronglyMeasurable).2
    ((integrable_sq_norm_normalizedLeviRestriction_iff p l hKc).2 hφ.2.2)

/-- The Library's `A²_P` predicate as a complex submodule of scalar adelic functions. -/
def squareIntegrableInducedForms : Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {φ | IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ}
  zero_mem' := by
    refine ⟨(AutForms).zero_mem, ?_, ?_⟩
    · intro a ha g
      simp
    · simp
  add_mem' := by
    intro φ ψ hφ hψ
    change IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ at hφ
    change IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l ψ at hψ
    refine ⟨(AutForms).add_mem hφ.1 hψ.1, ?_, ?_⟩
    · intro a ha g
      simp only [Pi.add_apply, hφ.2.1 a ha g, hψ.2.1 a ha g, mul_add]
    · have hL : MemLp (normalizedLeviRestriction p l K (φ + ψ)) 2 μKM := by
        rw [map_add]
        exact (memLp_normalizedLeviRestriction p l hKc rho hsmooth hcalc iU hφ).add
          (memLp_normalizedLeviRestriction p l hKc rho hsmooth hcalc iU hψ)
      exact (integrable_sq_norm_normalizedLeviRestriction_iff p l hKc).1
        ((memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).1 hL)
  smul_mem' := by
    intro c φ hφ
    change IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ at hφ
    refine ⟨(AutForms).smul_mem c hφ.1, ?_, ?_⟩
    · intro a ha g
      simp only [Pi.smul_apply, smul_eq_mul, hφ.2.1 a ha g]
      ring
    · have hL : MemLp (normalizedLeviRestriction p l K (c • φ)) 2 μKM := by
        rw [map_smul]
        exact (memLp_normalizedLeviRestriction p l hKc rho hsmooth hcalc iU hφ).const_smul c
      exact (integrable_sq_norm_normalizedLeviRestriction_iff p l hKc).1
        ((memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).1 hL)

@[simp] theorem mem_squareIntegrableInducedForms {φ : AdelicGroupPoints F G → ℂ} :
    φ ∈ squareIntegrableInducedForms p l hKc rho hsmooth hcalc iU ↔
      IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ :=
  Iff.rfl

end Langlands.Global.AdelicGroupPoints
