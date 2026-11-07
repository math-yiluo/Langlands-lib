import Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
import Langlands.Representation.Jacquet.CoefficientScalarRestriction

/-! # Native coefficient compact-induction coinvariants -/

noncomputable section

namespace Langlands.Induction.Coefficient

open MeasureTheory
open Langlands.Jacquet.CoefficientRestriction

universe uR uG uV uW

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
  [IsScalarTower ℂ R V]

/-- Restriction of scalars preserves the literal compact covariant functions. -/
def compactFunctionsComplexEquiv (H : Subgroup G) (σ : Representation R H V) :
    CompactFunctions H σ ≃ₗ[ℂ] CompactFunctions H (complexRepresentation σ) where
  toFun f := ⟨⟨⟨f.val.val.val, f.val.val.property⟩, f.val.property⟩, f.property⟩
  invFun f := ⟨⟨⟨f.val.val.val, f.val.val.property⟩, f.val.property⟩, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem compactFunctionsComplexEquiv_eval (H : Subgroup G) (σ : Representation R H V)
    (f : CompactFunctions H σ) (g : G) :
    eval H (complexRepresentation σ) (compactFunctionsComplexEquiv H σ f).val g =
      eval H σ f.val g := rfl

/-- Scalar restriction commutes with the original right-translation operators. -/
def compactInducedComplexEquiv (H : Subgroup G) (σ : Representation R H V) :
    (complexRepresentation (compactInduced H σ)).Equiv
      (compactInduced H (complexRepresentation σ)) where
  toLinearEquiv := compactFunctionsComplexEquiv H σ
  isIntertwining' g := by
    ext f x
    rfl

section FullCoinvariants

variable {K : Type*} [Group K]

/-- The complex relation span already contains all coefficient multiples of
its generators, so it equals the restricted native relation submodule. -/
theorem fullRelations_complex_eq (σ : Representation R K V) :
    Representation.Coinvariants.ker (complexRepresentation σ) =
      (Representation.Coinvariants.ker σ).restrictScalars ℂ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := σ) g v
  · intro v hv
    change v ∈ Representation.Coinvariants.ker σ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g, w⟩, rfl⟩ := hv
      exact Representation.Coinvariants.sub_mem_ker
        (ρ := complexRepresentation σ) g w
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih =>
      have hstable : ∀ {x : V},
          x ∈ Representation.Coinvariants.ker (complexRepresentation σ) →
          r • x ∈ Representation.Coinvariants.ker (complexRepresentation σ) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨⟨g, w⟩, rfl⟩ := hx
          change r • (σ g w - w) ∈
            Representation.Coinvariants.ker (complexRepresentation σ)
          rw [smul_sub, ← (σ g).map_smul r w]
          exact Representation.Coinvariants.sub_mem_ker
            (ρ := complexRepresentation σ) g (r • w)
        | zero =>
          simpa only [smul_zero] using
            (Representation.Coinvariants.ker (complexRepresentation σ)).zero_mem
        | add x y _ _ ihx ihy =>
          simpa only [smul_add] using Submodule.add_mem _ ihx ihy
        | smul c x _ ih =>
          rw [← smul_comm c r x]
          exact Submodule.smul_mem _ c ih
      exact hstable ih

/-- Complex scalars inherited from the native quotient module. -/
instance fullCoinvariantsComplexModule (σ : Representation R K V) :
    Module ℂ (Representation.Coinvariants σ) :=
  inferInstanceAs (Module ℂ (V ⧸ Representation.Coinvariants.ker σ))

/-- The actual full coinvariants before and after restricting scalars,
with the identity formula on original vectors. -/
def fullCoinvariantsComplexEquiv (σ : Representation R K V) :
    Representation.Coinvariants (complexRepresentation σ) ≃ₗ[ℂ]
      Representation.Coinvariants σ :=
  (Submodule.quotEquivOfEq _ _ (fullRelations_complex_eq σ)).trans
    (Submodule.Quotient.restrictScalarsEquiv ℂ (Representation.Coinvariants.ker σ))

@[simp]
theorem fullCoinvariantsComplexEquiv_mk (σ : Representation R K V) (v : V) :
    fullCoinvariantsComplexEquiv σ
      (Representation.Coinvariants.mk (complexRepresentation σ) v) =
        Representation.Coinvariants.mk σ v := rfl

/-- Multiplication by a coefficient on inducing vectors descends to the
same multiplication on the native full quotient. -/
theorem fullCoinvariantsComplexEquiv_coefficient (σ : Representation R K V)
    (r : R) (q : Representation.Coinvariants (complexRepresentation σ)) :
    fullCoinvariantsComplexEquiv σ
      (Representation.Coinvariants.map _ _
        (Langlands.Jacquet.coefficientIntertwiner R (complexRepresentation σ) r) q) =
      r • fullCoinvariantsComplexEquiv σ q := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rfl

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An actual representation equivalence induces the full-coinvariant
linear equivalence by the original quotient maps in both directions. -/
def fullCoinvariantsCongr {ρ : Representation ℂ K V}
    {τ : Representation ℂ K W} (e : ρ.Equiv τ) :
    Representation.Coinvariants ρ ≃ₗ[ℂ] Representation.Coinvariants τ :=
  LinearEquiv.ofLinearMap
    (Representation.Coinvariants.map _ _ e.toIntertwiningMap)
    (Representation.Coinvariants.map _ _ e.symm.toIntertwiningMap)
    (by
      apply Representation.Coinvariants.hom_ext
      ext w
      change Representation.Coinvariants.mk τ (e (e.symm w)) =
        Representation.Coinvariants.mk τ w
      rw [e.apply_symm_apply])
    (by
      apply Representation.Coinvariants.hom_ext
      ext v
      change Representation.Coinvariants.mk ρ (e.symm (e v)) =
        Representation.Coinvariants.mk ρ v
      rw [e.symm_apply_apply])

@[simp]
theorem fullCoinvariantsCongr_mk {ρ : Representation ℂ K V}
    {τ : Representation ℂ K W} (e : ρ.Equiv τ) (v : V) :
    fullCoinvariantsCongr e (Representation.Coinvariants.mk ρ v) =
      Representation.Coinvariants.mk τ (e v) := rfl

end FullCoinvariants

/-- The compact-induced ambient quotient is unchanged by scalar restriction. -/
def compactCoinvariantsComplexEquiv (H : Subgroup G) (σ : Representation R H V) :
    Representation.Coinvariants (compactInduced H σ) ≃ₗ[ℂ]
      Representation.Coinvariants (compactInduced H (complexRepresentation σ)) :=
  (fullCoinvariantsComplexEquiv (compactInduced H σ)).symm.trans
    (fullCoinvariantsCongr (compactInducedComplexEquiv H σ))

@[simp]
theorem compactCoinvariantsComplexEquiv_mk (H : Subgroup G)
    (σ : Representation R H V) (f : CompactFunctions H σ) :
    compactCoinvariantsComplexEquiv H σ
      (Representation.Coinvariants.mk (compactInduced H σ) f) =
      Representation.Coinvariants.mk (compactInduced H (complexRepresentation σ))
        (compactFunctionsComplexEquiv H σ f) := rfl

/-- The scalar endomorphism of the inducing carrier acts pointwise on the
original compact functions after scalar restriction. -/
theorem compactFunctionsComplexEquiv_coefficient (H : Subgroup G)
    (σ : Representation R H V) (r : R) (f : CompactFunctions H σ) :
    compactInducedMap H
      (Langlands.Jacquet.coefficientIntertwiner R (complexRepresentation σ) r)
        (compactFunctionsComplexEquiv H σ f) =
      compactFunctionsComplexEquiv H σ (r • f) := by
  ext x
  rfl

section Integral

variable (H : Subgroup G) (σ : Representation R H V)
variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]
variable (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- The original quotient integral, retaining its native coefficient action. -/
def compactCoinvariantIntegral :
    CompactFunctions H σ →ₗ[R] Representation.Coinvariants σ where
  toFun f := fullCoinvariantsComplexEquiv σ
    (Induction.compactCoinvariantIntegral H (complexRepresentation σ) ν
      (compactFunctionsComplexEquiv H σ f))
  map_add' f k := by
    simp only [map_add]
  map_smul' r f := by
    change fullCoinvariantsComplexEquiv σ
      (Induction.compactCoinvariantIntegral H (complexRepresentation σ) ν
        (compactFunctionsComplexEquiv H σ (r • f))) = _
    rw [← compactFunctionsComplexEquiv_coefficient,
      Induction.compactCoinvariantIntegral_natural,
      fullCoinvariantsComplexEquiv_coefficient]
    rfl

/-- On every original function the native integral is exactly the published
finite-fiber integral, followed by the identity comparison on quotient classes. -/
theorem compactCoinvariantIntegral_apply (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H σ ν f = fullCoinvariantsComplexEquiv σ
      (Langlands.HarmonicAnalysis.AlgebraicIntegral.integral ν
        (quotientCoinvariantSimple H (complexRepresentation σ)
          (compactFunctionsComplexEquiv H σ f))) := rfl

variable (hν : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)

include hν in
/-- Right invariance of the same finite-fiber integral. -/
theorem compactCoinvariantIntegral_translate (g : G) (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H σ ν (compactInduced H σ g f) =
      compactCoinvariantIntegral H σ ν f := by
  change fullCoinvariantsComplexEquiv σ
    (Induction.compactCoinvariantIntegral H (complexRepresentation σ) ν
      (compactInduced H (complexRepresentation σ) g
        (compactFunctionsComplexEquiv H σ f))) = _
  rw [Induction.compactCoinvariantIntegral_translate H (complexRepresentation σ) ν hν]
  rfl

/-- The native coefficient-linear integral descended through the actual
ambient relation-span quotient. -/
def compactCoinvariantDesc :
    Representation.Coinvariants (compactInduced H σ) →ₗ[R]
      Representation.Coinvariants σ :=
  Representation.Coinvariants.lift (compactInduced H σ) (compactCoinvariantIntegral H σ ν)
    (fun g => LinearMap.ext (compactCoinvariantIntegral_translate H σ ν hν g))

@[simp]
theorem compactCoinvariantDesc_mk (f : CompactFunctions H σ) :
    compactCoinvariantDesc H σ ν hν
      (Representation.Coinvariants.mk (compactInduced H σ) f) =
        compactCoinvariantIntegral H σ ν f := rfl

/-- Scalar restriction compares the descended maps on the original quotient. -/
theorem compactCoinvariantDesc_complex (q : Representation.Coinvariants (compactInduced H σ)) :
    compactCoinvariantDesc H σ ν hν q =
      fullCoinvariantsComplexEquiv σ
        (Induction.compactCoinvariantDesc H (complexRepresentation σ) ν hν
          (compactCoinvariantsComplexEquiv H σ q)) := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rfl

end Integral

section Bijectivity

open MeasureTheory.Measure

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H]
variable (μG : Measure G) (μH : Measure H)
variable [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
variable [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]
variable (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
variable (hν : QuotientIntegration.IsCompatible H μG μH ν)
variable (σ : Representation R H V) (hσ : IsSmooth σ)

include hG hH hσ in
/-- Bijectivity of the actual coefficient-linear quotient integral follows from
the published complex theorem, retaining every original vector and group action. -/
theorem compactCoinvariantDesc_bijective :
    Function.Bijective (compactCoinvariantDesc H σ ν hν.right_invariant) := by
  have hb := Induction.compactCoinvariantIntegralBijective hG H hH μG μH ν hν
    V (complexRepresentation σ) ((isSmooth_complexRepresentation σ).mpr hσ)
  have he : (compactCoinvariantDesc H σ ν hν.right_invariant :
      Representation.Coinvariants (compactInduced H σ) → Representation.Coinvariants σ) =
      (fullCoinvariantsComplexEquiv σ) ∘
        (Induction.compactCoinvariantDesc H (complexRepresentation σ) ν hν.right_invariant) ∘
          (compactCoinvariantsComplexEquiv H σ) :=
    funext (compactCoinvariantDesc_complex H σ ν hν.right_invariant)
  rw [he]
  exact (fullCoinvariantsComplexEquiv σ).bijective.comp
    (hb.comp (compactCoinvariantsComplexEquiv H σ).bijective)

/-- Native coefficient compact-induction coinvariants, identified by the
actual compatible quotient integral. -/
def compactCoinvariantEquiv :
    Representation.Coinvariants (compactInduced H σ) ≃ₗ[R]
      Representation.Coinvariants σ :=
  LinearEquiv.ofBijective (compactCoinvariantDesc H σ ν hν.right_invariant)
    (compactCoinvariantDesc_bijective hG H hH μG μH ν hν σ hσ)

@[simp]
theorem compactCoinvariantEquiv_mk (f : CompactFunctions H σ) :
    compactCoinvariantEquiv hG H hH μG μH ν hν σ hσ
      (Representation.Coinvariants.mk (compactInduced H σ) f) =
        compactCoinvariantIntegral H σ ν f := rfl

/-- The equivalence on original compact functions is the finite-fiber integral
of their original values in the inducing quotient. -/
theorem compactCoinvariantEquiv_mk_integral (f : CompactFunctions H σ) :
    compactCoinvariantEquiv hG H hH μG μH ν hν σ hσ
      (Representation.Coinvariants.mk (compactInduced H σ) f) =
      fullCoinvariantsComplexEquiv σ
        (Langlands.HarmonicAnalysis.AlgebraicIntegral.integral ν
          (quotientCoinvariantSimple H (complexRepresentation σ)
            (compactFunctionsComplexEquiv H σ f))) := rfl

end Bijectivity

end Langlands.Induction.Coefficient

