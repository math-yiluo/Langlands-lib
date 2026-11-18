import Langlands.AlgebraicGeometry.DvrStableNormalization.GenericFibre
import Langlands.CommutativeAlgebra.FlatDvrNormality
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality

/-! # Flat normal schemes over a DVR are integrally closed in their generic fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

/-- Normal stalks give normal-domain localizations of the sections over an affine open. -/
theorem localization_normal_of_hasNormalStalks {X : Scheme.{u}} (hX : HasNormalStalks X)
    {U : X.Opens} (hU : IsAffineOpen U) (p : Ideal Γ(X, U)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let alg : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  let e : Localization.AtPrime p ≃ₐ[Γ(X, U)] X.presheaf.stalk (hU.fromSpec y) :=
    IsLocalization.algEquiv p.primeCompl _ _
  obtain ⟨h1, h2⟩ := hX (hU.fromSpec y)
  exact ⟨e.toMulEquiv.isDomain, h2.of_equiv e.symm.toRingEquiv⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A flat scheme with normal stalks over a DVR is its own relative normalization in its
generic fibre. -/
theorem isIso_fromNormalization_of_normal (T : Over (Spec (CommRingCat.of R))) [Flat T.hom]
    (hT : HasNormalStalks T.left) : IsIso (genericι T).fromNormalization := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set j := genericι T
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_affineOpens_eq_top _)).mpr fun U => ?_
  change IsIso (j.fromNormalization ∣_ U.1)
  rw [isIso_morphismRestrict_iff_isIso_app _ U.2, Scheme.Hom.fromNormalization_app _ U.2]
  let := (j.app U.1).hom.toAlgebra
  have hloc := isLocalization_genericι_app T hϖ U.2
  have hπ := resSec_mem_nonZeroDivisors T hϖ U.2
  suffices IsIso (CommRingCat.ofHom (algebraMap Γ(T.left, U.1)
      (integralClosure Γ(T.left, U.1) Γ(pullback T.hom (Spec.algebraMap R (FractionRing R)),
        j ⁻¹ᵁ U.1)))) by
    infer_instance
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    have hinj : Function.Injective (algebraMap Γ(T.left, U.1)
        Γ(pullback T.hom (Spec.algebraMap R (FractionRing R)), j ⁻¹ᵁ U.1)) :=
      IsLocalization.injective _ (Submonoid.powers_le.mpr hπ)
    apply hinj
    have := congrArg Subtype.val hab
    exact this
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Langlands.CommutativeAlgebra.FlatDvrNormality.mem_range_of_isIntegral_of_normal
      (resSec T ϖ U.1) hπ (fun m _ => localization_normal_of_hasNormalStalks hT U.2 m) hx
    exact ⟨y, Subtype.ext hy⟩

end Langlands.AlgebraicGeometry.DvrStableNormalization
