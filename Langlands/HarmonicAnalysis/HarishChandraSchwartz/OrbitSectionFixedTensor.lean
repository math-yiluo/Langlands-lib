import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology
import Langlands.Representation.Plancherel.CompactIntertwiningCompression
import Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation
import Langlands.Representation.Smooth.Factorization.TwoFactorExternalTensorProof
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Actual fixed coefficients and the faithful tensor map of a section level -/

noncomputable section

open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- The actual compact-picture coefficients fixed by `(H ∩ K) × (H ∩ K)`;
for `H ≤ K` these are precisely the `H × H` fixed coefficients. -/
def orbitSectionFixedCoefficients (H : OpenSubgroup G) :
    Submodule ℂ (ProductInducedCompactPicture h K π.obj) :=
  fixedVectors (productInducedCompactRepresentation h K π.obj)
    (compactFixedSubgroup (K.prod K) (H.prod H))

omit [LocallyCompactSpace G] in
/-- Explicit comparison with the action of `H × H` when `H ≤ K`. -/
theorem mem_orbitSectionFixedCoefficients_iff (H : OpenSubgroup G) (hHK : H ≤ K)
    (v : ProductInducedCompactPicture h K π.obj) :
    v ∈ orbitSectionFixedCoefficients h K π H ↔
      ∀ x : H.prod H, productInducedCompactRepresentation h K π.obj
        ⟨x.val, hHK x.property.1, hHK x.property.2⟩ v = v := by
  constructor
  · intro hv x
    exact hv ⟨⟨x.val, hHK x.property.1, hHK x.property.2⟩, x.property⟩
  · intro hv x
    exact hv ⟨x.val.val, x.property⟩

omit [LocallyCompactSpace G] in
/-- Admissibility of the actual product Levi object follows from the two factors. -/
theorem orbitSectionProductLevi_isAdmissible (hcofinal : CompactOpenCofinal M) :
    (productLeviObject π.obj π.obj.contragredient).IsAdmissible := by
  exact isAdmissible_comp_continuousMulEquiv
    (Induction.BinaryTensor.external π.obj.representation π.obj.contragredient.representation)
    (HaarModulus.subgroupProdEquiv M M)
    (TwoFactorExternalTensor.admissible _ _ π.property.2
      ((SmoothRep.isAdmissible_contragredient_iff hcofinal π.obj).mpr π.property.2))

/-- Finiteness target under compactness and compact-open cofinality of the Levi,
without an admissibility premise for any product or induced representation. -/
def OrbitSectionFixedCoefficientsFiniteStatement : Prop :=
  IsCompact (K : Set G) → CompactOpenCofinal M →
    ∀ H : OpenSubgroup G, H ≤ K →
      FiniteDimensional ℂ (orbitSectionFixedCoefficients h K π H)

omit [LocallyCompactSpace G] in
/-- Adapter of the published compact fixed-space theorem to the actual product
Levi. This uses no admissibility theorem for induced representations. -/
theorem finiteDimensional_orbitSectionFixedCoefficients (hK : IsCompact (K : Set G))
    (hcofinal : CompactOpenCofinal M) (H : OpenSubgroup G) (hHK : H ≤ K) :
    FiniteDimensional ℂ (orbitSectionFixedCoefficients h K π H) := by
  exact finiteDimensional_compactFixedVectors (h.prod h) (K.prod K) (hK.prod hK)
    (productLeviObject π.obj π.obj.contragredient)
    (orbitSectionProductLevi_isAdmissible π hcofinal) (H.prod H)
    (fun _ hx => ⟨hHK hx.1, hHK hx.2⟩)

variable {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (H : OpenSubgroup G) (hHK : H ≤ K)

/-- The actual compact restriction with its values restricted to the fixed
coefficient submodule. -/
def orbitSectionLevelFixedRestriction :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      ((J → Circle) → orbitSectionFixedCoefficients h K π H) where
  toFun q z := ⟨productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
    (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) z,
    (mem_orbitSectionFixedCoefficients_iff h K π H hHK _).mpr fun x =>
      productInducedCompactRepresentation_orbitSectionCompactRestriction
        ν π e h hU K hP hK hν hr hPK H hHK
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) q.property x z⟩
  map_add' q r := by
    funext z
    apply Subtype.ext
    change productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H (q + r)) z =
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) z +
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H r) z
    rw [map_add, map_add, Pi.add_apply]
  map_smul' c q := by
    funext z
    apply Subtype.ext
    change productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H (c • q)) z =
      c • productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) z
    rw [map_smul, map_smul, Pi.smul_apply]

/-- The fixed-valued restriction is still a finite scalar-smooth family. -/
theorem orbitSectionLevelFixedRestriction_mem
    (q : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :
    orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK q ∈
      finiteSmoothFamilies J (orbitSectionFixedCoefficients h K π H) := by
  exact mem_finiteSmoothFamilies_of_injective_linearMap
    (orbitSectionFixedCoefficients h K π H).subtype (Submodule.subtype_injective _)
    _ q.property.1.2

/-- Actual fixed-valued finite smooth families arising from sections. The
self-twist constraint is retained by the source. -/
def orbitSectionLevelFixedFamily :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      finiteSmoothFamilies J (orbitSectionFixedCoefficients h K π H) :=
  (orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK).codRestrict _
    (orbitSectionLevelFixedRestriction_mem h K π ν e hU hP hK hν hr hPK H hHK)

/-- The faithful algebraic tensor representing the actual compact restriction
of a fixed section. No finite-dimensionality choice is needed for this map. -/
def orbitSectionLevelTensor :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      smoothFiniteTorusFunctions J ⊗[ℂ] orbitSectionFixedCoefficients h K π H :=
  (smoothTensorFamilyEquiv J (orbitSectionFixedCoefficients h K π H)).symm.toLinearMap ∘ₗ
    orbitSectionLevelFixedFamily h K π ν e hU hP hK hν hr hPK H hHK

/-- Evaluating the tensor, followed by coefficient inclusion, is exactly the
compact restriction of the original section. -/
@[simp]
theorem orbitSectionLevelTensor_evaluation
    (q : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) (z : J → Circle) :
    (smoothTensorEvaluation J (orbitSectionFixedCoefficients h K π H)
      (orbitSectionLevelTensor h K π ν e hU hP hK hν hr hPK H hHK q) z).val =
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) z := by
  have heq := congrArg (fun F => F.val z)
    ((smoothTensorFamilyEquiv J (orbitSectionFixedCoefficients h K π H)).apply_symm_apply
      (orbitSectionLevelFixedFamily h K π ν e hU hP hK hν hr hPK H hHK q))
  exact congrArg Subtype.val heq

/-- Distinct actual sections cannot have the same fixed coefficient tensor. -/
theorem orbitSectionLevelTensor_injective :
    Function.Injective (orbitSectionLevelTensor h K π ν e hU hP hK hν hr hPK H hHK) := by
  intro q r hqr
  apply OrbitSectionLevel.toSections_injective ν π e h hU K hP hK hν hr hPK H
  apply productInducedSmoothOrbitCompactRestriction_injective h hU ν π K hP hK hν hr hPK e
  funext z
  have heq := congrArg (fun t => (smoothTensorEvaluation J
    (orbitSectionFixedCoefficients h K π H) t z).val) hqr
  simpa only [orbitSectionLevelTensor_evaluation] using heq

end Langlands.HarishChandraSchwartz
