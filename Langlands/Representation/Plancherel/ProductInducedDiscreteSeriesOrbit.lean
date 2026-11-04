import Langlands.Representation.Plancherel.ProductInducedOrbitSections
import Langlands.Representation.Plancherel.TwistStabilizerComparison

/-! # Actual discrete-series orbits and the full-stabilizer tensor model -/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)

section DiscreteSeries

variable [MeasurableSpace (M ⧸ C)] (μ : MeasureTheory.Measure (M ⧸ C))
  [MeasureTheory.Measure.IsHaarMeasure μ]
  (hπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

include hπ in
/-- Every actual representative of a discrete-series unitary orbit is itself
square-integrable on the same prescribed central quotient. -/
theorem unitaryOrbitRepresentative_isDiscreteSeries
    (A : UnitaryOrbitRepresentative ν π) :
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μ := by
  change IsDiscreteSeriesClass C hC μ (Quotient.mk _ A.val)
  obtain ⟨χ, hχ⟩ := A.property
  rw [← hχ]
  exact isDiscreteSeriesClass_unitaryTwist C hC μ
    (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ))
    χ.property.2 (Quotient.mk _ π) hπ

/-- The actual representative index maps to the source's actual
discrete-series orbit, with its original canonical smooth class. -/
def unitaryOrbitRepresentativeDiscreteSeriesOrbit
    (A : UnitaryOrbitRepresentative ν π) :
    discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hπ) :=
  ⟨discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hπ A), by
    obtain ⟨χ, hχ⟩ := A.property
    exact ⟨χ, Subtype.ext hχ⟩⟩

/-- Every class in the source's actual discrete-series orbit has an actual
representative among the indices of the coherent section space. -/
theorem unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective :
    Function.Surjective
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hπ) := by
  rintro ⟨ω, χ, hχ⟩
  refine ⟨⟨IrreducibleAdmissibleRep.twist
    (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ)) π,
    χ, rfl⟩, ?_⟩
  apply Subtype.ext
  exact hχ

/-- The unitary stabilizer of the underlying smooth class is the stabilizer
of the actual discrete-series class, with the same character. -/
def unitaryClassStabilizerEquivDiscreteSeries :
    unitaryClassTwistStabilizer ν (Quotient.mk _ π) ≃*
      discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hπ) where
  toFun χ := ⟨χ.val, Subtype.ext χ.property⟩
  invFun χ := ⟨χ.val, congrArg Subtype.val χ.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

end DiscreteSeries

section FullStabilizer

variable [hfin : Finite (M ⧸ (commonNormKernel ν ⊔ C))]

/-- The published central-quotient argument proves that the unitary-class
stabilizer is the full unramified stabilizer. -/
def unitaryClassStabilizerEquivFull
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    unitaryClassTwistStabilizer ν ω ≃* unramifiedTwistStabilizer ν ω where
  toFun := unitaryClassStabilizerInclusion ν ω
  invFun χ := ⟨⟨χ.val.val, χ.val.property,
    unramifiedTwistStabilizer_norm_eq_one ν C hC ω χ⟩, χ.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem unitaryClassStabilizerEquivFull_apply
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M))
    (χ : unitaryClassTwistStabilizer ν ω) :
    unitaryClassStabilizerEquivFull ν C hC ω χ =
      unitaryClassStabilizerInclusion ν ω χ := rfl

include hC hfin in
/-- This is finiteness of the stabilizer of one actual class. It does not
assert finiteness of the family of discrete-series orbits. -/
theorem finite_unitaryClassTwistStabilizer
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    Finite (unitaryClassTwistStabilizer ν ω) := by
  let := finite_unramifiedTwistStabilizer ν C hC ω
  exact Finite.of_injective _
    (unitaryClassStabilizerEquivFull ν C hC ω).injective

variable {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- Torus coordinates of each actual character in the full stabilizer. Its
unitarity is a consequence of the displayed finite central quotient. -/
def fullStabilizerTorusHom
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    unramifiedTwistStabilizer ν ω →* (J → Circle) :=
  (unitaryStabilizerTorusHom ν e ω).comp
    (unitaryClassStabilizerEquivFull ν C hC ω).symm.toMonoidHom

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

local instance discreteSeriesSmoothTensorAddCommGroup :
    AddCommGroup
      (smoothFiniteTorusFunctions J ⊗[ℂ] ProductInducedCompactPicture h K π.obj) :=
  TensorProduct.addCommGroup

/-- The full stabilizer acts by inverse torus translation and its actual
compact self-twist coefficient representation. -/
abbrev productInducedFullStabilizerTensorRepresentation :=
  smoothTensorRepresentation J (ProductInducedCompactPicture h K π.obj)
    (fullStabilizerTorusHom ν C hC e (Quotient.mk _ π))
    (unramifiedStabilizerCompactRepresentation ν π h K hP hK hν hr)

omit [LocallyCompactSpace G] in
/-- Passing from the unitary class stabilizer to the full stabilizer leaves
exactly the same diagonal invariant tensors. -/
theorem productInducedFullStabilizerTensorInvariants_eq :
    (productInducedFullStabilizerTensorRepresentation ν π C hC e h K hP hK hν hr).invariants =
      (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants := by
  apply Submodule.ext
  intro t
  rw [mem_smoothTensorInvariants_iff, mem_smoothTensorInvariants_iff]
  constructor
  · intro ht s z
    exact ht (unitaryClassStabilizerEquivFull ν C hC (Quotient.mk _ π) s) z
  · intro ht s z
    exact ht ((unitaryClassStabilizerEquivFull ν C hC (Quotient.mk _ π)).symm s) z

/-- The source's full-stabilizer invariant tensor space gives the actual
coherent smooth sections, retaining the concrete compact evaluation. -/
def productInducedFullStabilizerTensorOrbitEquiv :
    (productInducedFullStabilizerTensorRepresentation ν π C hC e h K hP hK hν hr).invariants ≃ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  (LinearEquiv.ofEq _ _
    (productInducedFullStabilizerTensorInvariants_eq ν π C hC e h K hP hK hν hr)).trans
    (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK)

@[simp]
theorem productInducedFullStabilizerTensorOrbitEquiv_restriction
    (t : (productInducedFullStabilizerTensorRepresentation ν π C hC e h K hP hK hν hr).invariants)
    (z : J → Circle) :
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π e h hU
        (productInducedFullStabilizerTensorOrbitEquiv ν π C hC e h hU K hP hK hν hr hPK t).val) z =
      smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj) t.val z :=
  productInducedSmoothTensorOrbitEquiv_restriction ν π e h hU K hP hK hν hr hPK _ z

@[simp]
theorem productInducedFullStabilizerTensorOrbitEquiv_symm_evaluation
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (z : J → Circle) :
    smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj)
      ((productInducedFullStabilizerTensorOrbitEquiv ν π C hC e h hU K hP hK hν hr hPK).symm q).val z =
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q.val) z :=
  productInducedSmoothTensorOrbitEquiv_symm_evaluation ν π e h hU K hP hK hν hr hPK q z

end FullStabilizer

end Langlands.Plancherel
