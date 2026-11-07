import Langlands.Weil.Local.ExtensionWeilRange

/-! # Finite Galois quotients of the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- Restriction to the given finite Galois extension, using its specified closure embedding. -/
def finiteGaloisRestriction :
    letI := extensionAlgebra F E f
    Field.absoluteGaloisGroup F.Carrier →ₜ* Gal(E.Carrier/F.Carrier) := by
  letI := extensionAlgebra F E f
  letI := extensionAlgebra_finiteDimensional F E f
  letI := hGal
  let S := extensionIntermediateField F E f
  let e := extensionIntermediateFieldEquiv F E f
  letI : IsGalois F.Carrier S := IsGalois.of_algEquiv e
  exact
    { toMonoidHom := (AlgEquiv.autCongr e.symm).toMonoidHom.comp
        (AlgEquiv.restrictNormalHom S)
      continuous_toFun := (continuous_of_discreteTopology :
        Continuous (AlgEquiv.autCongr e.symm)).comp
          (InfiniteGalois.restrictNormalHom_continuous S) }

/-- The finite restriction has the required action through the closure embedding. -/
theorem finiteGaloisRestriction_apply (σ : Field.absoluteGaloisGroup F.Carrier)
    (x : E.Carrier) :
    letI := extensionAlgebra F E f
    extensionFieldEmbedding F E f (finiteGaloisRestriction F E f hGal σ x) =
      AlgEquiv.toAlgHom σ (extensionFieldEmbedding F E f x) := by
  let := extensionAlgebra F E f
  let := hGal
  let S := extensionIntermediateField F E f
  let e := extensionIntermediateFieldEquiv F E f
  let : IsGalois F.Carrier S := IsGalois.of_algEquiv e
  change ((e ((AlgEquiv.autCongr e.symm) (AlgEquiv.restrictNormalHom S σ) x)).val) = _
  rw [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes σ S (e x)

theorem finiteGaloisRestriction_surjective :
    letI := extensionAlgebra F E f
    Function.Surjective (finiteGaloisRestriction F E f hGal) := by
  let := extensionAlgebra F E f
  let := hGal
  let S := extensionIntermediateField F E f
  let e := extensionIntermediateFieldEquiv F E f
  let : IsGalois F.Carrier S := IsGalois.of_algEquiv e
  exact (AlgEquiv.autCongr e.symm).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F.Carrier))

/-- The kernel of restriction is the actual absolute Galois image of the extension. -/
theorem finiteGaloisRestriction_ker :
    letI := extensionAlgebra F E f
    (finiteGaloisRestriction F E f hGal).toMonoidHom.ker =
      (extensionGaloisMap F E f).toMonoidHom.range := by
  let := extensionAlgebra F E f
  rw [extensionGaloisMap_range]
  ext σ
  change (finiteGaloisRestriction F E f hGal σ = 1) ↔ _
  refine Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff
    (K := extensionIntermediateField F E f) σ).symm
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F E f y).mp hy
    have hh := finiteGaloisRestriction_apply F E f hGal σ x
    rw [h] at hh
    exact hh.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply (extensionFieldEmbedding F E f).injective
    rw [finiteGaloisRestriction_apply]
    exact h _ ((mem_extensionIntermediateField F E f _).mpr ⟨x, rfl⟩)

/-- The Galois quotient of the actual Weil group. -/
def finiteGaloisQuotient :
    letI := extensionAlgebra F E f
    localWeilGroup F →ₜ* Gal(E.Carrier/F.Carrier) := by
  letI := extensionAlgebra F E f
  exact (finiteGaloisRestriction F E f hGal).comp (localProjection F)

theorem finiteGaloisQuotient_apply (g : localWeilGroup F) (x : E.Carrier) :
    letI := extensionAlgebra F E f
    extensionFieldEmbedding F E f (finiteGaloisQuotient F E f hGal g x) =
      AlgEquiv.toAlgHom (localProjection F g) (extensionFieldEmbedding F E f x) :=
  finiteGaloisRestriction_apply F E f hGal _ _

theorem finiteGaloisQuotient_surjective :
    letI := extensionAlgebra F E f
    Function.Surjective (finiteGaloisQuotient F E f hGal) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  apply denseRange_discrete.mp
  exact (finiteGaloisRestriction_surjective F E f hGal).denseRange.comp
    (localProjection_denseRange F) (finiteGaloisRestriction F E f hGal).continuous

/-- The kernel of the finite quotient is exactly the image of the extension Weil group. -/
theorem finiteGaloisQuotient_ker :
    letI := extensionAlgebra F E f
    (finiteGaloisQuotient F E f hGal).toMonoidHom.ker = extensionWeilRange F E f := by
  let := extensionAlgebra F E f
  change ((finiteGaloisRestriction F E f hGal).toMonoidHom.comp
    (localProjection F).toMonoidHom).ker = _
  rw [← MonoidHom.comap_ker, finiteGaloisRestriction_ker]
  exact (extensionWeilMap_range F E f).symm

/-- The actual extension Weil group identified with the kernel of the finite quotient. -/
def finiteGaloisQuotientKernelEquiv :
    letI := extensionAlgebra F E f
    localWeilGroup E ≃ₜ* (finiteGaloisQuotient F E f hGal).toMonoidHom.ker := by
  letI := extensionAlgebra F E f
  let h := finiteGaloisQuotient_ker F E f hGal
  let c : extensionWeilRange F E f ≃ₜ*
      (finiteGaloisQuotient F E f hGal).toMonoidHom.ker :=
    { toMulEquiv := MulEquiv.subgroupCongr h.symm
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact (extensionWeilRangeEquiv F E f).trans c

@[simp] theorem finiteGaloisQuotientKernelEquiv_apply (y : localWeilGroup E) :
    letI := extensionAlgebra F E f
    (finiteGaloisQuotientKernelEquiv F E f hGal y : localWeilGroup F) =
      extensionWeilMap F E f y := rfl

@[simp] theorem extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm :
    letI := extensionAlgebra F E f
    ∀ x : (finiteGaloisQuotient F E f hGal).toMonoidHom.ker,
      extensionWeilMap F E f ((finiteGaloisQuotientKernelEquiv F E f hGal).symm x) = x := by
  let := extensionAlgebra F E f
  intro x
  exact extensionWeilMap_extensionWeilRangeEquiv_symm F E f _

end Langlands.Weil.Local
