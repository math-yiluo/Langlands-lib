import Langlands.Weil.Local.FiniteGaloisEquivariance
import Langlands.Weil.Local.IntermediateWeil

/-! # Reciprocity and conjugation by absolute Galois elements on a finite Galois kernel -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- The finite Galois quotient of a Galois conjugate is the conjugate by the restriction. -/
theorem finiteGaloisQuotient_galoisConjugationWeil (κ : Field.absoluteGaloisGroup F.Carrier)
    (x : localWeilGroup F) :
    letI := extensionAlgebra F E f
    finiteGaloisQuotient F E f hGal (galoisConjugationWeil F κ x) =
      finiteGaloisRestriction F E f hGal κ * finiteGaloisQuotient F E f hGal x *
        (finiteGaloisRestriction F E f hGal κ)⁻¹ := by
  let := extensionAlgebra F E f
  change finiteGaloisRestriction F E f hGal (localProjection F (galoisConjugationWeil F κ x)) = _
  rw [localProjection_galoisConjugationWeil, map_mul, map_mul, map_inv]
  rfl

/-- Conjugation by an absolute Galois element preserves the finite Galois Weil kernel. -/
theorem galoisConjugationWeil_mem_ker (κ : Field.absoluteGaloisGroup F.Carrier)
    (x : localWeilGroup F)
    (hx : letI := extensionAlgebra F E f; x ∈ (finiteGaloisQuotient F E f hGal).toMonoidHom.ker) :
    letI := extensionAlgebra F E f
    galoisConjugationWeil F κ x ∈ (finiteGaloisQuotient F E f hGal).toMonoidHom.ker := by
  let := extensionAlgebra F E f
  rw [MonoidHom.mem_ker] at hx ⊢
  change finiteGaloisQuotient F E f hGal (galoisConjugationWeil F κ x) = 1
  rw [finiteGaloisQuotient_galoisConjugationWeil]
  change finiteGaloisQuotient F E f hGal x = 1 at hx
  rw [hx, mul_one, mul_inv_cancel]

/-- Conjugation by an absolute Galois element, restricted to the finite Galois kernel. -/
def kernelGaloisConjugation (κ : Field.absoluteGaloisGroup F.Carrier) :
    letI := extensionAlgebra F E f
    (finiteGaloisQuotient F E f hGal).toMonoidHom.ker ≃ₜ*
      (finiteGaloisQuotient F E f hGal).toMonoidHom.ker := by
  letI := extensionAlgebra F E f
  exact
    { toFun := fun n => ⟨galoisConjugationWeil F κ n,
        galoisConjugationWeil_mem_ker F E f hGal κ n n.property⟩
      invFun := fun n => ⟨galoisConjugationWeil F κ⁻¹ n,
        galoisConjugationWeil_mem_ker F E f hGal κ⁻¹ n n.property⟩
      left_inv := fun n => Subtype.ext
        ((galoisConjugationWeil F κ).symm_apply_apply (n : localWeilGroup F))
      right_inv := fun n => Subtype.ext
        ((galoisConjugationWeil F κ).apply_symm_apply (n : localWeilGroup F))
      map_mul' := fun m n => Subtype.ext
        (map_mul (galoisConjugationWeil F κ) (m : localWeilGroup F) n)
      continuous_toFun := ((galoisConjugationWeil F κ).continuous.comp
        continuous_subtype_val).subtype_mk _
      continuous_invFun := ((galoisConjugationWeil F κ⁻¹).continuous.comp
        continuous_subtype_val).subtype_mk _ }

/-- Conjugation by an absolute Galois element, transported to the actual `W_E`. -/
def finiteGaloisAbsoluteConjugation (κ : Field.absoluteGaloisGroup F.Carrier) :
    localWeilGroup E ≃ₜ* localWeilGroup E := by
  letI := extensionAlgebra F E f
  let j := finiteGaloisQuotientKernelEquiv F E f hGal
  exact (j.trans (kernelGaloisConjugation F E f hGal κ)).trans j.symm

/-- The transported conjugation agrees with Galois conjugation in `W_F`. -/
theorem extensionWeilMap_finiteGaloisAbsoluteConjugation
    (κ : Field.absoluteGaloisGroup F.Carrier) (y : localWeilGroup E) :
    extensionWeilMap F E f (finiteGaloisAbsoluteConjugation F E f hGal κ y) =
      galoisConjugationWeil F κ (extensionWeilMap F E f y) := by
  let := extensionAlgebra F E f
  exact extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm F E f hGal _

/-- The transported conjugation preserves the integer degree. -/
theorem localDegree_finiteGaloisAbsoluteConjugation
    (κ : Field.absoluteGaloisGroup F.Carrier) (y : localWeilGroup E) :
    localDegree E (finiteGaloisAbsoluteConjugation F E f hGal κ y) = localDegree E y := by
  have h := congrArg (localDegree F)
    (extensionWeilMap_finiteGaloisAbsoluteConjugation F E f hGal κ y)
  simp only [localDegree_extensionWeilMap, localDegree_galoisConjugationWeil] at h
  apply Multiplicative.toAdd.injective
  have hh := congrArg Multiplicative.toAdd h
  simp only [toAdd_pow, nsmul_eq_mul] at hh
  exact mul_left_cancel₀
    (by exact_mod_cast (extensionResidueDegree_pos F E f).ne') hh

/-- The closure automorphism of `E` attached to an absolute Galois element of `F`. -/
def absoluteClosureConjugation (κ : Field.absoluteGaloisGroup F.Carrier) :
    AlgebraicClosure E.Carrier ≃+* AlgebraicClosure E.Carrier :=
  ((extensionClosureEquiv F E f).symm.trans
    (κ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier).toRingEquiv).trans
    (extensionClosureEquiv F E f)

/-- The closure automorphism evaluated through the closure isomorphism. -/
theorem absoluteClosureConjugation_apply (κ : Field.absoluteGaloisGroup F.Carrier)
    (x : AlgebraicClosure F.Carrier) :
    absoluteClosureConjugation F E f κ (extensionClosureEquiv F E f x) =
      extensionClosureEquiv F E f (AlgEquiv.toAlgHom κ x) := by
  change extensionClosureEquiv F E f (AlgEquiv.toAlgHom κ
    ((extensionClosureEquiv F E f).symm (extensionClosureEquiv F E f x))) = _
  rw [RingEquiv.symm_apply_apply]

/-- Its inverse is given by the inverse Galois element. -/
theorem absoluteClosureConjugation_symm_apply (κ : Field.absoluteGaloisGroup F.Carrier)
    (x : AlgebraicClosure F.Carrier) :
    (absoluteClosureConjugation F E f κ).symm (extensionClosureEquiv F E f x) =
      extensionClosureEquiv F E f (AlgEquiv.toAlgHom κ⁻¹ x) := by
  apply (absoluteClosureConjugation F E f κ).injective
  rw [RingEquiv.apply_symm_apply, absoluteClosureConjugation_apply]
  congr 1
  change x = AlgEquiv.toAlgHom (κ * κ⁻¹) x
  rw [mul_inv_cancel]
  rfl

/-- On `E`, the closure automorphism is the finite Galois restriction of `κ`. -/
theorem absoluteClosureConjugation_algebraMap (κ : Field.absoluteGaloisGroup F.Carrier)
    (x : E.Carrier) :
    absoluteClosureConjugation F E f κ (algebraMap E.Carrier (AlgebraicClosure E.Carrier) x) =
      algebraMap E.Carrier (AlgebraicClosure E.Carrier)
        (letI := extensionAlgebra F E f; finiteGaloisRestriction F E f hGal κ x) := by
  let := extensionAlgebra F E f
  rw [← extensionClosureLift_fieldEmbedding F E f x, ← extensionClosureEquiv_apply,
    absoluteClosureConjugation_apply, ← extensionClosureLift_fieldEmbedding F E f,
    ← extensionClosureEquiv_apply]
  congr 1
  exact (finiteGaloisRestriction_apply F E f hGal κ x).symm

/-- The Galois image of a transported conjugate is conjugation by the closure automorphism. -/
theorem localProjection_finiteGaloisAbsoluteConjugation_closure
    (κ : Field.absoluteGaloisGroup F.Carrier) (w : localWeilGroup E)
    (x : AlgebraicClosure E.Carrier) :
    AlgEquiv.toAlgHom (localProjection E (finiteGaloisAbsoluteConjugation F E f hGal κ w))
        (absoluteClosureConjugation F E f κ x) =
      absoluteClosureConjugation F E f κ (AlgEquiv.toAlgHom (localProjection E w) x) := by
  obtain ⟨x, rfl⟩ := (extensionClosureEquiv F E f).surjective x
  have hc := congrArg (localProjection F)
    (extensionWeilMap_finiteGaloisAbsoluteConjugation F E f hGal κ w)
  rw [localProjection_extensionWeilMap, localProjection_galoisConjugationWeil,
    localProjection_extensionWeilMap] at hc
  rw [absoluteClosureConjugation_apply]
  calc AlgEquiv.toAlgHom (localProjection E (finiteGaloisAbsoluteConjugation F E f hGal κ w))
        (extensionClosureEquiv F E f (AlgEquiv.toAlgHom κ x))
      = extensionClosureLift F E f (AlgEquiv.toAlgHom (extensionGaloisMap F E f
          (localProjection E (finiteGaloisAbsoluteConjugation F E f hGal κ w)))
            (AlgEquiv.toAlgHom κ x)) :=
        (extensionClosureLift_galoisMap F E f _ _).symm
    _ = extensionClosureEquiv F E f (AlgEquiv.toAlgHom κ
          (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E w)) x)) := by
        rw [hc]
        change extensionClosureLift F E f (AlgEquiv.toAlgHom κ
          (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E w))
            (AlgEquiv.toAlgHom (κ⁻¹ * κ) x))) = _
        rw [inv_mul_cancel]
        rfl
    _ = absoluteClosureConjugation F E f κ (extensionClosureLift F E f
          (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E w)) x)) :=
        (absoluteClosureConjugation_apply F E f κ _).symm
    _ = _ := by
        rw [extensionClosureLift_galoisMap]
        rfl

/-- The base ring automorphism attached to `κ` by finite Galois restriction. -/
def absoluteBaseConjugation (κ : Field.absoluteGaloisGroup F.Carrier) :
    E.Carrier ≃+* E.Carrier :=
  letI := extensionAlgebra F E f
  (finiteGaloisRestriction F E f hGal κ).toRingEquiv

/-- The base and closure automorphisms form a compatible pair. -/
theorem absoluteBaseConjugation_compatible (κ : Field.absoluteGaloisGroup F.Carrier) :
    (algebraMap E.Carrier (AlgebraicClosure E.Carrier)).comp
        (absoluteBaseConjugation F E f hGal κ).toRingHom =
      (absoluteClosureConjugation F E f κ).toRingHom.comp
        (algebraMap E.Carrier (AlgebraicClosure E.Carrier)) := by
  ext x
  exact (absoluteClosureConjugation_algebraMap F E f hGal κ x).symm

/-- The restriction of `κ`, as an automorphism over `Padic p`. -/
def absolutePadicGaloisEquiv (κ : Field.absoluteGaloisGroup F.Carrier) :
    E.Carrier ≃ₐ[Padic p] E.Carrier :=
  letI := extensionAlgebra F E f
  haveI := extensionAlgebra_isScalarTower F E f
  (finiteGaloisRestriction F E f hGal κ).restrictScalars (Padic p)

/-- The base automorphism is continuous for the canonical topology. -/
theorem continuous_absoluteBaseConjugation (κ : Field.absoluteGaloisGroup F.Carrier) :
    letI := E.canonicalTopologicalData.topology
    Continuous (absoluteBaseConjugation F E f hGal κ) := by
  let := E.canonicalNormedField
  exact (extension_isometry E E (absolutePadicGaloisEquiv F E f hGal κ).toAlgHom).continuous

/-- Its inverse is continuous for the canonical topology. -/
theorem continuous_absoluteBaseConjugation_symm (κ : Field.absoluteGaloisGroup F.Carrier) :
    letI := E.canonicalTopologicalData.topology
    Continuous (absoluteBaseConjugation F E f hGal κ).symm := by
  let := E.canonicalNormedField
  exact (extension_isometry E E
    (absolutePadicGaloisEquiv F E f hGal κ).symm.toAlgHom).continuous

/-- The base automorphism preserves the canonical integer order of units. -/
theorem orderHom_absoluteBaseConjugation (κ : Field.absoluteGaloisGroup F.Carrier)
    (a : E.Carrierˣ) :
    E.canonicalTopologicalData.orderHom
        (Units.mapEquiv (absoluteBaseConjugation F E f hGal κ).toMulEquiv a) =
      E.canonicalTopologicalData.orderHom a := by
  change Multiplicative.ofAdd (E.canonicalTopologicalData.ord
      (absolutePadicGaloisEquiv F E f hGal κ a)) =
    Multiplicative.ofAdd (E.canonicalTopologicalData.ord a)
  rw [PadicField.CanonicalTransport.ord_map E E (absolutePadicGaloisEquiv F E f hGal κ)]

/-- Geometric reciprocity is equivariant for conjugation by absolute Galois elements:
`e(κ w κ⁻¹) = κ|_E (e(w))`. -/
theorem reciprocityUnits_finiteGaloisAbsoluteConjugation (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (κ : Field.absoluteGaloisGroup F.Carrier) (w : localWeilGroup E) :
    letI := E.canonicalTopologicalData.topology
    reciprocityUnits E e (finiteGaloisAbsoluteConjugation F E f hGal κ w) =
      Units.mapEquiv (absoluteBaseConjugation F E f hGal κ).toMulEquiv
        (reciprocityUnits E e w) :=
  WeilReciprocityTransport.reciprocity_conjugation E (absoluteBaseConjugation F E f hGal κ)
    (absoluteClosureConjugation F E f κ) (absoluteBaseConjugation_compatible F E f hGal κ)
    (finiteGaloisAbsoluteConjugation F E f hGal κ)
    (localProjection_finiteGaloisAbsoluteConjugation_closure F E f hGal κ)
    E.canonicalTopologicalData (continuous_absoluteBaseConjugation F E f hGal κ)
    (continuous_absoluteBaseConjugation_symm F E f hGal κ)
    (orderHom_absoluteBaseConjugation F E f hGal κ)
    (localDegree_finiteGaloisAbsoluteConjugation F E f hGal κ) e ⟨he.1, he.2.1⟩ w

end Langlands.Weil.Local
