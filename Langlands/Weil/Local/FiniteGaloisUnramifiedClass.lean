import Langlands.Weil.Local.FiniteGaloisUnramified
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Galois.Local.UnramifiedCriterionProof

/-! # The Weil class of a finite unramified extension without a transfer hypothesis -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne GroupExtensionPushout ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- The element `Φ⁻ⁿ` of the kernel of the finite Galois quotient `W_F → Gal(E/F)`, for an
arithmetic coordinate `χ` of order `n`, where `Φ` is the chosen geometric Frobenius. -/
def frobeniusPowerKernel {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    (finiteGaloisQuotient F E f hGal).toMonoidHom.ker := by
  letI := extensionAlgebra F E f
  exact powerKernel _ χ (localGeometricFrobenius F)⁻¹
    (finiteGaloisQuotient_inv_localGeometricFrobenius F E f hGal χ hχ)

/-- The inverse reciprocity value of `Φ⁻ⁿ` lies in the base field: conjugation by the power
section `Φ^{-k}` fixes `Φ⁻ⁿ`, so by equivariance every Galois element fixes its value. -/
theorem frobeniusPowerKernel_reciprocity_mem_range
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    ((finiteGaloisKernelReciprocity F E f hGal e (frobeniusPowerKernel F E f hGal χ hχ) :
        E.Carrierˣ) : E.Carrier) ∈ (algebraMap F.Carrier E.Carrier).range := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := hGal
  let := E.canonicalTopologicalData.topology
  let q := (finiteGaloisQuotient F E f hGal).toMonoidHom
  let Φ := localGeometricFrobenius F
  have hw : χ (q Φ⁻¹) = Multiplicative.ofAdd 1 :=
    finiteGaloisQuotient_inv_localGeometricFrobenius F E f hGal χ hχ
  let s : Section q := frobeniusPowerSection F E f hGal χ hχ
  let r := (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
  let hr := finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he
  have hfix : ∀ σ : Gal(E.Carrier/F.Carrier),
      σ ((r (powerKernel q χ Φ⁻¹ hw) : E.Carrierˣ) : E.Carrier) =
        r (powerKernel q χ Φ⁻¹ hw) := by
    intro σ
    have hσ : q (s σ) = σ := Section.map_apply s σ
    have hck : conjugateKernel q (s σ) (powerKernel q χ Φ⁻¹ hw) = powerKernel q χ Φ⁻¹ hw := by
      apply Subtype.ext
      change s σ * Φ⁻¹ ^ n * (s σ)⁻¹ = Φ⁻¹ ^ n
      rw [show s σ = Φ⁻¹ ^ (χ σ).toAdd.val from rfl, (Commute.pow_pow_self Φ⁻¹ _ n).eq,
        mul_inv_cancel_right]
    have h : r (powerKernel q χ Φ⁻¹ hw) = σ • r (powerKernel q χ Φ⁻¹ hw) := by
      have h0 := hr (s σ) (powerKernel q χ Φ⁻¹ hw)
      rw [hck] at h0
      rw [← hσ]
      exact h0
    exact (congrArg Units.val h).symm
  exact (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix

/-- The base unit whose image in `E` is the inverse reciprocity value of `Φ⁻ⁿ`. For an
unramified extension it has order one (`exists_finiteGaloisClass_eq_cyclicClass`). -/
def unramifiedFrobeniusUnit
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    F.Carrierˣ := by
  letI := extensionAlgebra F E f
  letI := E.canonicalTopologicalData.topology
  have h := RingHom.mem_range.mp
    (frobeniusPowerKernel_reciprocity_mem_range F E f hGal e he χ hχ)
  refine Units.mk0 h.choose fun h0 => ?_
  apply (finiteGaloisKernelReciprocity F E f hGal e (frobeniusPowerKernel F E f hGal χ hχ)).ne_zero
  rw [← h.choose_spec, h0, map_zero]

/-- The image of `unramifiedFrobeniusUnit` in `Eˣ` is the inverse reciprocity value of `Φ⁻ⁿ`. -/
theorem units_map_unramifiedFrobeniusUnit
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    {n : ℕ} [NeZero n]
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom
        (unramifiedFrobeniusUnit F E f hGal e he χ hχ) =
      finiteGaloisKernelReciprocity F E f hGal e (frobeniusPowerKernel F E f hGal χ hχ) := by
  let := extensionAlgebra F E f
  let := E.canonicalTopologicalData.topology
  apply Units.ext
  exact (RingHom.mem_range.mp
    (frobeniusPowerKernel_reciprocity_mem_range F E f hGal e he χ hχ)).choose_spec

/-- For a finite unramified Galois extension with an arithmetic unramified coordinate, the
actual Weil pushout class is the explicit cyclic class of a base unit of order one, namely
`unramifiedFrobeniusUnit`. -/
theorem exists_finiteGaloisClass_eq_cyclicClass
    (hUnr : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    {n : ℕ} [NeZero n] (hn : extensionDegree F E f = n)
    (χ : letI := extensionAlgebra F E f
      Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      IsArithmeticUnramifiedCoordinate F E.Carrier χ) :
    letI := extensionAlgebra F E f
    ∃ a : F.Carrierˣ, F.canonicalTopologicalData.ord (a : F.Carrier) = 1 ∧
      finiteGaloisClass F E f hGal e he = cyclicClass F.Carrier E.Carrier χ.toMonoidHom a := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  have := extensionAlgebra_isScalarTower F E f
  let := hGal
  let := E.canonicalTopologicalData.topology
  let q := (finiteGaloisQuotient F E f hGal).toMonoidHom
  let Φ := localGeometricFrobenius F
  have hw : χ (q Φ⁻¹) = Multiplicative.ofAdd 1 :=
    finiteGaloisQuotient_inv_localGeometricFrobenius F E f hGal χ hχ
  let s : Section q := frobeniusPowerSection F E f hGal χ hχ
  let r := (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
  let hr := finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he
  let a := unramifiedFrobeniusUnit F E f hGal e he χ hχ
  have hrk : r (powerKernel q χ Φ⁻¹ hw) =
      Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a :=
    (units_map_unramifiedFrobeniusUnit F E f hGal e he χ hχ).symm
  have ha0 : algebraMap F.Carrier E.Carrier (a : F.Carrier) =
      (r (powerKernel q χ Φ⁻¹ hw) : E.Carrier) :=
    congrArg Units.val hrk.symm
  -- The order of the unit is one.
  let y := (finiteGaloisQuotientKernelEquiv F E f hGal).symm (powerKernel q χ Φ⁻¹ hw)
  have hk : powerKernel q χ Φ⁻¹ hw = finiteGaloisQuotientKernelEquiv F E f hGal y :=
    ((finiteGaloisQuotientKernelEquiv F E f hGal).apply_symm_apply _).symm
  have hy : extensionWeilMap F E f y = Φ⁻¹ ^ n :=
    extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm F E f hGal _
  have hres : extensionResidueDegree F E f = n :=
    ((PadicField.ramificationIndex_eq_iff_extensionResidueDegree_eq F E f).mp hUnr).trans hn
  have hdeg : localDegreeInt E y = -1 := by
    have h1 := localDegreeInt_extensionWeilMap F E f y
    rw [hy, hres] at h1
    have h2 : localDegreeInt F (Φ⁻¹ ^ n) = -(n : ℤ) := by
      change (localDegree F ((localGeometricFrobenius F)⁻¹ ^ n)).toAdd = -(n : ℤ)
      rw [map_pow (localDegree F), map_inv (localDegree F), localGeometricFrobenius_degree,
        toAdd_pow, toAdd_inv, toAdd_ofAdd, nsmul_eq_mul, mul_neg, mul_one]
    rw [h2] at h1
    have hn0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact mul_left_cancel₀ hn0 (by rw [← h1]; ring)
  have hordE : E.canonicalTopologicalData.ord
      ((r (powerKernel q χ Φ⁻¹ hw) : E.Carrierˣ) : E.Carrier) = 1 := by
    have h : E.canonicalTopologicalData.ord ((reciprocityUnits E e y : E.Carrierˣ) : E.Carrier) =
        localDegreeInt E y :=
      congrArg Multiplicative.toAdd
        (DFunLike.congr_fun he.1 (WeilQuotients.projection (localResidueDegree E) y))
    change E.canonicalTopologicalData.ord
      ((finiteGaloisKernelReciprocity F E f hGal e (powerKernel q χ Φ⁻¹ hw) : E.Carrierˣ) :
        E.Carrier) = 1
    rw [hk, finiteGaloisKernelReciprocity_apply, Units.val_inv_eq_inv_val,
      PadicField.TopologicalData.ord_inv, h, hdeg, neg_neg]
  have hord : F.canonicalTopologicalData.ord (a : F.Carrier) = 1 := by
    have h := (relativeNormOrderLaws p F E F.canonicalTopologicalData
      E.canonicalTopologicalData).2.1 (a : F.Carrier)
    rw [ha0, hordE, hUnr, mul_one] at h
    have hpos : (E.canonicalTopologicalData.ramificationIndex : ℤ) ≠ 0 :=
      Nat.cast_ne_zero.mpr E.canonicalTopologicalData.ramificationIndex_pos.ne'
    exact (mul_right_eq_self₀.mp h.symm).resolve_right hpos
  refine ⟨a, hord, ?_⟩
  rw [finiteGaloisClass_eq_of_section F E f hGal e he s]
  have hcoc : (NormalizedTwoCocycle.toCocycle₂ (s.cocycle r hr) :
      groupCohomology.cocycles₂ (unitsRepresentation F.Carrier E.Carrier)) =
      cyclicUnitCocycle F.Carrier E.Carrier χ.toMonoidHom a := by
    apply Subtype.ext
    funext gh
    change Additive.ofMul (s.cocycle r hr (gh.1, gh.2)) =
      cyclicCarry (χ gh.1).toAdd (χ gh.2).toAdd • baseUnit F.Carrier E.Carrier a
    rw [show s = powerSection q χ Φ⁻¹ hw from rfl, cocycle_powerSection, hrk, ofMul_pow]
    rfl
  exact congrArg (groupCohomology.H2π (unitsRepresentation F.Carrier E.Carrier)) hcoc

/-- With arithmetic normalization, the actual Weil pushout class of a finite unramified
Galois extension is its fundamental class. No transfer square and no reciprocity for the base
field are assumed. -/
theorem finiteGaloisClass_isFundamental_of_unramified_of_order
    (F M : PadicField.{u} p) (f : F.Carrier →ₐ[Padic p] M.Carrier)
    (hM : letI := extensionAlgebra F M f; IsGalois F.Carrier M.Carrier)
    (hUnr : F.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex)
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
  obtain ⟨a, ha, hclass⟩ :=
    exists_finiteGaloisClass_eq_cyclicClass F M f hM hUnr eM heM
      (n := Module.finrank F.Carrier M.Carrier) rfl χ hχ
  change J.relative F M.Carrier (finiteGaloisClass F M f hM eM heM) =
    reciprocalClass (Module.finrank F.Carrier M.Carrier)
  rw [hclass]
  exact hJ F M.Carrier _ χ hχ a ha

end Langlands.Weil.Local
