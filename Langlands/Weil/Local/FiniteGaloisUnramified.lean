import Langlands.GroupTheory.CyclicPowerSection
import Langlands.Weil.Local.FiniteGaloisPushout
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityStatement
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessProof
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.ClassFieldTheory.Local.ExtensionValuationTransport
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.FundamentalClasses

/-! # The actual Weil pushout class of a finite unramified extension -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne GroupExtensionPushout ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- Under geometric reciprocity the chosen geometric Frobenius has base order one. -/
theorem ord_reciprocityUnits_localGeometricFrobenius (eF : ReciprocityCandidate F)
    (heF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF) :
    F.canonicalTopologicalData.ord
      (reciprocityUnits F eF (localGeometricFrobenius F) : F.Carrier) = 1 := by
  have h : F.canonicalTopologicalData.orderHom
      (reciprocityUnits F eF (localGeometricFrobenius F)) =
        localDegree F (localGeometricFrobenius F) :=
    DFunLike.congr_fun heF.1
      (WeilQuotients.projection (localResidueDegree F) (localGeometricFrobenius F))
  rw [localGeometricFrobenius_degree] at h
  exact congrArg Multiplicative.toAdd h

set_option backward.isDefEq.respectTransparency false in
/-- On a finite abelian Galois extension, the restriction of an absolute Galois
element acting on residues by geometric Frobenius satisfies the inverse
residue-power congruence for the canonical discrete valuation of `E`. -/
theorem finiteGaloisRestriction_inverse_power_congruence
    (hcomm : letI := extensionAlgebra F E f; IsMulCommutative Gal(E.Carrier/F.Carrier))
    (σ : Field.absoluteGaloisGroup F.Carrier)
    (hσ : localResidueMap F σ =
      Galois.FiniteField.geometricFrobenius (localResidueField F))
    (x : E.Carrier) (hx : E.canonicalTopologicalData.discreteValuation x ≤ 1) :
    letI := extensionAlgebra F E f
    E.canonicalTopologicalData.discreteValuation
      ((finiteGaloisRestriction F E f hGal σ).symm x -
        x ^ F.canonicalTopologicalData.residueCardinality) < 1 := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := hGal
  let J := extensionFiniteIntermediate F E f
  let e := extensionIntermediateFieldEquiv F E f
  let : IsGalois F.Carrier J.field := IsGalois.of_algEquiv e
  have hcommJ : IsMulCommutative Gal(J.field/F.Carrier) := .of_comm fun s t => by
    apply e.autCongr.symm.injective
    simp only [map_mul]
    exact hcomm.is_comm.comm _ _
  let L : LocalFiniteAbelianExtension F := ⟨{ toIntermediateField := J.field }, hcommJ⟩
  let := (L.asPadicField (p := p)).algebra
  let ψ : E.Carrier ≃ₐ[Padic p] (L.asPadicField (p := p)).Carrier :=
    { e.toRingEquiv with
      commutes' := fun a => by
        apply Subtype.ext
        change extensionFieldEmbedding F E f (algebraMap (Padic p) E.Carrier a) =
          algebraMap (Padic p) (AlgebraicClosure F.Carrier) a
        rw [← f.commutes a, extensionFieldEmbedding_comp,
          ← IsScalarTower.algebraMap_apply] }
  have hψx : (L.asPadicField (p := p)).canonicalTopologicalData.discreteValuation (ψ x) ≤ 1 := by
    rw [PadicField.CanonicalTransport.discreteValuation_map]
    exact hx
  have hcong := Correspondence.GeometricResidue.finite_inverse_power_congruence F L
    (L.asPadicField (p := p)).canonicalTopologicalData σ hσ (ψ x) hψx
  have hres : (L.restriction σ).symm (ψ x) =
      ψ ((finiteGaloisRestriction F E f hGal σ).symm x) := by
    apply Subtype.ext
    have h₁ : (L.restriction σ).symm = L.restriction σ⁻¹ := by
      rw [map_inv]
      rfl
    have h₂ : (finiteGaloisRestriction F E f hGal σ).symm =
        finiteGaloisRestriction F E f hGal σ⁻¹ := by
      rw [map_inv]
      rfl
    rw [h₁, h₂]
    change algebraMap L.field (AlgebraicClosure F.Carrier)
        ((σ⁻¹).restrictNormal L.field (ψ x)) =
      extensionFieldEmbedding F E f (finiteGaloisRestriction F E f hGal σ⁻¹ x)
    rw [AlgEquiv.restrictNormal_commutes, finiteGaloisRestriction_apply]
    rfl
  rw [hres] at hcong
  have key : (L.asPadicField (p := p)).canonicalTopologicalData.discreteValuation
      (ψ ((finiteGaloisRestriction F E f hGal σ).symm x -
        x ^ F.canonicalTopologicalData.residueCardinality)) < 1 := by
    rw [map_sub, map_pow]
    exact hcong
  rwa [PadicField.CanonicalTransport.discreteValuation_map] at key

/-- The actual Weil quotient sends the inverse of the chosen geometric Frobenius
to the positive generator of an arithmetic unramified coordinate. -/
theorem finiteGaloisQuotient_inv_localGeometricFrobenius
    {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    χ (finiteGaloisQuotient F E f hGal (localGeometricFrobenius F)⁻¹) =
      Multiplicative.ofAdd 1 := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := extensionAlgebra_isScalarTower F E f
  have hcomm : IsMulCommutative Gal(E.Carrier/F.Carrier) := .of_comm fun s t => by
    apply χ.injective
    simp only [map_mul]
    exact mul_comm _ _
  have h := FiniteArtinSystemUniqueness.inverse_coordinate_eq_one F E
    F.canonicalTopologicalData χ hχ
    (finiteGaloisQuotient F E f hGal (localGeometricFrobenius F))
    (fun x hx => finiteGaloisRestriction_inverse_power_congruence F E f hGal hcomm
      (localProjection F (localGeometricFrobenius F)) (localGeometricFrobenius_residue F) x hx)
  rw [map_inv, map_inv, h]

/-- The normalized section of the actual quotient `W_F → Gal(E/F)` sending the
element of arithmetic coordinate `k`, with `0 ≤ k < n`, to `Φ⁻ᵏ`, where `Φ` is
the chosen geometric Frobenius. -/
def frobeniusPowerSection {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    Section (finiteGaloisQuotient F E f hGal).toMonoidHom := by
  letI := extensionAlgebra F E f
  exact powerSection _ χ (localGeometricFrobenius F)⁻¹
    (finiteGaloisQuotient_inv_localGeometricFrobenius F E f hGal χ hχ)

theorem frobeniusPowerSection_apply {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ)
    (g : letI := extensionAlgebra F E f; Gal(E.Carrier/F.Carrier)) :
    frobeniusPowerSection F E f hGal χ hχ g =
      (localGeometricFrobenius F)⁻¹ ^ (χ g).toAdd.val := rfl

/-- The class of the actual Weil pushout of a finite Galois extension with an
arithmetic unramified coordinate is the explicit cyclic class of the base unit
`e_F(Φ)`, given the transfer square for `F → E`. -/
theorem finiteGaloisClass_eq_cyclicClass
    (hT : ExtensionWeilTransferReciprocityStatement.{u,v})
    (eF : ReciprocityCandidate F)
    (heF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    finiteGaloisClass F E f hGal e he =
      cyclicClass F.Carrier E.Carrier χ.toMonoidHom
        (reciprocityUnits F eF (localGeometricFrobenius F)) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  let q := (finiteGaloisQuotient F E f hGal).toMonoidHom
  let Φ := localGeometricFrobenius F
  have hw : χ (q Φ⁻¹) = Multiplicative.ofAdd 1 :=
    finiteGaloisQuotient_inv_localGeometricFrobenius F E f hGal χ hχ
  let s : Section q := frobeniusPowerSection F E f hGal χ hχ
  let r := (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
  let hr := finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he
  have hker : q.ker = extensionWeilRange F E f := finiteGaloisQuotient_ker F E f hGal
  have hmem : Φ⁻¹ ^ n ∈ extensionWeilRange F E f :=
    hker ▸ (powerKernel q χ Φ⁻¹ hw).property
  have htr := hT p F E f eF e heF he Φ⁻¹
  rw [transfer_powerSection q χ Φ⁻¹ hw _ hker hmem] at htr
  let y := (finiteGaloisQuotientKernelEquiv F E f hGal).symm (powerKernel q χ Φ⁻¹ hw)
  have hy : InductionAlong.rangeInverse (extensionWeilMap F E f).toMonoidHom
      (extensionWeilMap_injective F E f) ⟨Φ⁻¹ ^ n, hmem⟩ = y := by
    apply extensionWeilMap_injective F E f
    change (extensionWeilMap F E f).toMonoidHom (InductionAlong.rangeInverse _ _ _) = _
    rw [InductionAlong.apply_rangeInverse]
    exact (extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm F E f hGal
      (powerKernel q χ Φ⁻¹ hw)).symm
  have hrk : r (powerKernel q χ Φ⁻¹ hw) =
      Units.map f.toRingHom.toMonoidHom (reciprocityUnits F eF Φ) := by
    have hk : powerKernel q χ Φ⁻¹ hw = finiteGaloisQuotientKernelEquiv F E f hGal y :=
      ((finiteGaloisQuotientKernelEquiv F E f hGal).apply_symm_apply _).symm
    change finiteGaloisKernelReciprocity F E f hGal e (powerKernel q χ Φ⁻¹ hw) = _
    rw [hk, finiteGaloisKernelReciprocity_apply]
    have htr' : reciprocityUnits E e y =
        Units.map f.toRingHom.toMonoidHom (reciprocityUnits F eF Φ⁻¹) := by
      rw [← hy]
      exact htr
    rw [htr', map_inv, map_inv, inv_inv]
  rw [finiteGaloisClass_eq_of_section F E f hGal e he s]
  have hcoc : (NormalizedTwoCocycle.toCocycle₂ (s.cocycle r hr) :
      groupCohomology.cocycles₂ (unitsRepresentation F.Carrier E.Carrier)) =
      cyclicUnitCocycle F.Carrier E.Carrier χ.toMonoidHom (reciprocityUnits F eF Φ) := by
    apply Subtype.ext
    funext gh
    change Additive.ofMul (s.cocycle r hr (gh.1, gh.2)) =
      cyclicCarry (χ gh.1).toAdd (χ gh.2).toAdd •
        baseUnit F.Carrier E.Carrier (reciprocityUnits F eF Φ)
    rw [show s = powerSection q χ Φ⁻¹ hw from rfl, cocycle_powerSection, hrk, ofMul_pow]
    rfl
  exact congrArg (groupCohomology.H2π (unitsRepresentation F.Carrier E.Carrier)) hcoc

/-- With arithmetic normalization, the actual Weil pushout class of a finite
unramified Galois extension is its fundamental class, given the transfer square. -/
theorem finiteGaloisClass_isFundamental_of_unramified
    (hT : ExtensionWeilTransferReciprocityStatement.{u,u})
    (F M : PadicField.{u} p) (f : F.Carrier →ₐ[Padic p] M.Carrier)
    (hM : letI := extensionAlgebra F M f; IsGalois F.Carrier M.Carrier)
    (hUnr : F.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex)
    (eF : ReciprocityCandidate F)
    (heF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF)
    (eM : ReciprocityCandidate M)
    (heM : GeometricWeilReciprocityRelation M M.canonicalTopologicalData eM)
    (J : InvariantFamily.{u,u} p) (hJ : J.ArithmeticNormalization) :
    letI := extensionAlgebra F M f
    letI := extensionAlgebra_finiteDimensional F M f
    letI := hM
    IsFundamentalClass F.Carrier M.Carrier (J.relative F M.Carrier)
      (finiteGaloisClass F M f hM eM heM) := by
  let := extensionAlgebra F M f
  let := extensionAlgebra_finiteDimensional F M f
  let := extensionAlgebra_isScalarTower F M f
  let := hM
  let : NeZero (Module.finrank F.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨χ, hχ⟩ := arithmeticUnramifiedCoordinateExistence p F M hUnr
  change J.relative F M.Carrier (finiteGaloisClass F M f hM eM heM) =
    reciprocalClass (Module.finrank F.Carrier M.Carrier)
  rw [finiteGaloisClass_eq_cyclicClass F M f hM hT eF heF eM heM χ hχ]
  exact hJ F M.Carrier _ χ hχ _ (ord_reciprocityUnits_localGeometricFrobenius F eF heF)

end Langlands.Weil.Local
