import Langlands.Weil.Local.FiniteGaloisNormInflation
import Langlands.Weil.Local.FiniteGaloisUnramifiedClass
import Langlands.Weil.Local.FiniteGaloisCommonClosure
import Langlands.ClassFieldTheory.Local.ClassFormation

/-! # The Weil class of a finite Galois extension is its fundamental class -/

noncomputable section

namespace Langlands.Weil.Local.FiniteGaloisTower

universe u

open LocalClassField LocalFactor.RankOne ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (L₀ : FiniteIntermediateExtension F.Carrier)

local notation "LP" => L₀.asPadicField (p := p)

local instance finiteGaloisFundamentalAlgebra : Algebra (Padic p) L₀.field := (LP).algebra

section Tower

variable [Normal F.Carrier L₀.field]
  (hEL : extensionIntermediateField F E f ≤ L₀.field)

/-- The tower inflation theorem for an intermediate field `L₀ ⊇ E` of the closure of `F`,
with the tower embedding `towerFieldEmbedding`, without the transfer hypothesis. -/
theorem relativeInflation_finiteGaloisClass_of_le_of_norm
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    [IsGalois F.Carrier L₀.field]
    (eE : ReciprocityCandidate E)
    (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (eL : ReciprocityCandidate LP)
    (heL : GeometricWeilReciprocityRelation LP (LP).canonicalTopologicalData eL) :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
    letI := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL)
    letI : IsScalarTower F.Carrier E.Carrier (LP).Carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := hE
    relativeInflation F.Carrier E.Carrier (LP).Carrier 2 (finiteGaloisClass F E f hE eE heE) =
      Module.finrank E.Carrier (LP).Carrier •
        finiteGaloisClass F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
          (towerFieldEmbedding_isGalois F E f L₀ hEL) eL heL :=
  relativeInflation_finiteGaloisClass_of_norm F E LP f (towerFieldEmbedding F E f L₀ hEL) hE
    (towerFieldEmbedding_isGalois F E f L₀ hEL) (towerFieldEmbedding_hF1 F E f L₀ hEL)
    eE heE eL heL

omit [Normal F.Carrier L₀.field] in
/-- The invariant of the Weil class of `L₀/F` is the same for every embedding equal to the
literal inclusion of `F` into `L₀`. -/
theorem relative_finiteGaloisClass_congr [IsGalois F.Carrier L₀.field]
    (J : InvariantFamily.{u,u} p)
    (eL : ReciprocityCandidate LP)
    (heL : GeometricWeilReciprocityRelation LP (LP).canonicalTopologicalData eL)
    (g : F.Carrier →ₐ[Padic p] (LP).Carrier) (hg : g = intermediateEmbedding F L₀)
    (hgal : letI := extensionAlgebra F LP g; IsGalois F.Carrier (LP).Carrier) :
    (letI := extensionAlgebra F LP g
     letI := extensionAlgebra_finiteDimensional F LP g
     letI := hgal
     J.relative F (LP).Carrier (finiteGaloisClass F LP g hgal eL heL)) =
    (letI := extensionAlgebra F LP (intermediateEmbedding F L₀)
     letI := extensionAlgebra_finiteDimensional F LP (intermediateEmbedding F L₀)
     letI := intermediateEmbedding_isGalois F L₀
     J.relative F (LP).Carrier (finiteGaloisClass F LP (intermediateEmbedding F L₀)
       (intermediateEmbedding_isGalois F L₀) eL heL)) := by
  subst hg
  rfl

/-- The invariant of the Weil class of `E/F` is `[L₀ : E]` times the invariant of the Weil
class of `L₀/F`, by inflation compatibility of the invariants. -/
theorem relative_finiteGaloisClass_eq_of_le
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    [IsGalois F.Carrier L₀.field]
    (J : InvariantFamily.{u,u} p) (hJ : J.InflationCompatibility)
    (eE : ReciprocityCandidate E)
    (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (eL : ReciprocityCandidate LP)
    (heL : GeometricWeilReciprocityRelation LP (LP).canonicalTopologicalData eL) :
    (letI := extensionAlgebra F E f
     letI := extensionAlgebra_finiteDimensional F E f
     letI := hE
     J.relative F E.Carrier (finiteGaloisClass F E f hE eE heE)) =
    (letI := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL)
     Module.finrank E.Carrier (LP).Carrier) •
    (letI := extensionAlgebra F LP (intermediateEmbedding F L₀)
     letI := extensionAlgebra_finiteDimensional F LP (intermediateEmbedding F L₀)
     letI := intermediateEmbedding_isGalois F L₀
     J.relative F (LP).Carrier (finiteGaloisClass F LP (intermediateEmbedding F L₀)
       (intermediateEmbedding_isGalois F L₀) eL heL)) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
  let := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL)
  let _ : IsScalarTower F.Carrier E.Carrier (LP).Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := hE
  have := extensionAlgebra_finiteDimensional F E f
  have := extensionAlgebra_finiteDimensional F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
  have := extensionAlgebra_finiteDimensional E LP (towerFieldEmbedding F E f L₀ hEL)
  have := towerFieldEmbedding_isGalois F E f L₀ hEL
  rw [← hJ F E.Carrier (LP).Carrier,
    relativeInflation_finiteGaloisClass_of_le_of_norm F E f L₀ hEL hE eE heE eL heL, map_nsmul,
    relative_finiteGaloisClass_congr F L₀ J eL heL _ (towerFieldEmbedding_comp F E f L₀ hEL)]

end Tower

/-- **The Weil class is the fundamental class.** Given geometric Weil reciprocity for every
`p`-adic field, the actual Weil pushout class of a finite Galois extension `E/F` is its
fundamental class for every invariant family satisfying the relative class-formation laws and
the arithmetic normalization. -/
theorem finiteGaloisClass_isFundamental (hW : WeilReciprocityExistenceUniqueness.{u})
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    (eE : ReciprocityCandidate E)
    (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization) :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra_finiteDimensional F E f
    letI := hE
    IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
      (finiteGaloisClass F E f hE eE heE) := by
  obtain ⟨M₀, L₀, hM, hL, hUnr, hdeg, hEL, hML⟩ := exists_unramified_commonClosure F E f hE
  have : Normal F.Carrier L₀.field := hL.to_normal
  obtain ⟨eM, heM, -⟩ := hW p (M₀.asPadicField (p := p))
    (M₀.asPadicField (p := p)).canonicalTopologicalData
  obtain ⟨eL, heL, -⟩ := hW p (L₀.asPadicField (p := p))
    (L₀.asPadicField (p := p)).canonicalTopologicalData
  have hMgal := intermediateEmbedding_isGalois F M₀
  have hMfund := finiteGaloisClass_isFundamental_of_unramified_of_order F
    (M₀.asPadicField (p := p)) (intermediateEmbedding F M₀) hMgal hUnr eM heM J hA
  have h1 := relative_finiteGaloisClass_eq_of_le F E f L₀ hEL hE J hJ.2.2.1 eE heE eL heL
  have h2 := relative_finiteGaloisClass_eq_of_le F (M₀.asPadicField (p := p))
    (intermediateEmbedding F M₀) L₀ hML hMgal J hJ.2.2.1 eM heM eL heL
  have hm := towerFieldEmbedding_finrank_eq F E f L₀ hEL (M₀.asPadicField (p := p))
    (intermediateEmbedding F M₀) hML
    hdeg.symm
  change _ = reciprocalClass (extensionDegree F E f)
  rw [h1, hm, ← h2, ← hdeg]
  exact hMfund

section ClassMap

/-- Fundamental classes are unique, so the class of the Weil pushout cocycle is the class of
any normalized cocycle with fundamental class. -/
theorem cohomologyClass_finiteGaloisCocycle_eq (hW : WeilReciprocityExistenceUniqueness.{u})
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (z : letI := extensionAlgebra F E f
      NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ)
    (hz : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      letI := hE
      IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
        (NormalizedTwoCocycle.cohomologyClass z)) :
    letI := extensionAlgebra F E f
    NormalizedTwoCocycle.cohomologyClass (finiteGaloisCocycle F E f hE e he) =
      NormalizedTwoCocycle.cohomologyClass z := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := hE
  exact (hJ.2.1 F E.Carrier).1
    ((finiteGaloisClass_isFundamental F E f hW hE e he J hJ hA).trans hz.symm)

/-- **The local Weil class map.** Given geometric Weil reciprocity for every `p`-adic field,
the continuous homomorphism from the actual local Weil group `W_F` to the extension of
`Gal(E/F)` by `Eˣ` attached to a normalized cocycle `z` with fundamental class: the Weil
pushout `finiteGaloisPushout`, followed by the identity-component equivalence of extensions
with equal classes. -/
def weilClassMap (hW : WeilReciprocityExistenceUniqueness.{u})
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (z : letI := extensionAlgebra F E f
      NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ)
    (hz : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      letI := hE
      IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
        (NormalizedTwoCocycle.cohomologyClass z)) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    localWeilGroup F →ₜ* z.Extension := by
  letI := extensionAlgebra F E f
  letI := extensionAlgebra_finiteDimensional F E f
  letI := E.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.valuativeRel
  letI := E.canonicalTopologicalData.localField
  let ψ := NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq
    (cohomologyClass_finiteGaloisCocycle_eq F E f hW hE J hJ hA e he z hz)
  exact ({ toMonoidHom := ψ.toMulEquiv.toMonoidHom
           continuous_toFun := ψ.continuous } :
      (finiteGaloisCocycle F E f hE e he).Extension →ₜ* z.Extension).comp
    (finiteGaloisPushout F E f hE e he)

/-- The Galois projection of the Weil class map acts through `E → \bar F` as the Galois
image of the Weil element. -/
theorem weilClassMap_projection_apply (hW : WeilReciprocityExistenceUniqueness.{u})
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (z : letI := extensionAlgebra F E f
      NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ)
    (hz : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      letI := hE
      IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
        (NormalizedTwoCocycle.cohomologyClass z))
    (g : localWeilGroup F) (x : E.Carrier) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    extensionFieldEmbedding F E f
        (NormalizedTwoCocycle.Extension.projection z
          (weilClassMap F E f hW hE J hJ hA e he z hz g) x) =
      AlgEquiv.toAlgHom (localProjection F g) (extensionFieldEmbedding F E f x) :=
  finiteGaloisPushout_projection_apply F E f hE e he g x

/-- On `W_E` the Weil class map is the inverse of reciprocity followed by `Eˣ → z.Extension`. -/
theorem weilClassMap_extensionWeilMap (hW : WeilReciprocityExistenceUniqueness.{u})
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (z : letI := extensionAlgebra F E f
      NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ)
    (hz : letI := extensionAlgebra F E f
      letI := extensionAlgebra_finiteDimensional F E f
      letI := hE
      IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
        (NormalizedTwoCocycle.cohomologyClass z))
    (y : localWeilGroup E) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    weilClassMap F E f hW hE J hJ hA e he z hz (extensionWeilMap F E f y) =
      (NormalizedTwoCocycle.Extension.inl z (reciprocityUnits E e y))⁻¹ := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  change NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq
      (cohomologyClass_finiteGaloisCocycle_eq F E f hW hE J hJ hA e he z hz)
      (finiteGaloisPushout F E f hE e he (extensionWeilMap F E f y)) = _
  rw [finiteGaloisPushout_extensionWeilMap, map_inv,
    NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq_inl]

end ClassMap

end Langlands.Weil.Local.FiniteGaloisTower
