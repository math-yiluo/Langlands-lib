import Langlands.GroupScheme.HenselianParabolicCovering

/-!
# Integral-times-parabolic factorizations from strictly Henselian coverings

The covering `P(K) · M(R) = G(K)` of `HenselianParabolicCovering`, rewritten as a
factorization `g = κ * p` with `κ` integral and `p` in the dynamic parabolic of any
cocharacter of `G` that is the generic fibre of an integral cocharacter.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel

namespace Langlands.GroupScheme.HenselianParabolicCovering

section Factorization

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}

/-- A left covering `H · M(R) = G(K)` gives, for every `g`, a factorization `g = κ * p` with
`κ` integral and `p ∈ H`. -/
theorem exists_integral_mul_of_hasLeftIntegralCovering (M : IntegralModel R K G)
    {H : Subgroup (rationalPoints G)} (h : HasLeftIntegralCovering M H)
    (g : rationalPoints G) : ∃ κ ∈ M.integralPoints, ∃ p ∈ H, g = κ * p := by
  obtain ⟨p, hp, κ, hκ, hpk⟩ := (hasLeftIntegralCovering_iff M H).mp h g⁻¹
  refine ⟨κ⁻¹, inv_mem hκ, p⁻¹, inv_mem hp, ?_⟩
  rw [← mul_inv_rev, hpk, inv_inv]

end Factorization

section Dynamic

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] [IsNoetherianRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]

/-- **Integral Iwasawa factorization.** Over a strictly Henselian Noetherian valuation
domain, let `λ` be a cocharacter of `G` that is the generic fibre, read through the
supplied identification, of an integral cocharacter of a reductive model `M`. Then every
`g ∈ G(K)` is `κ * p` with `κ ∈ M(R)` and `p` in the dynamic parabolic `P_G(λ)(K)`. -/
theorem exists_integral_mul_parabolic (M : IntegralModel R K G) (hM : IsReductive M.group)
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
    {lam : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G}
    (hlam : Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫ M.genericIso.hom = lam)
    (g : rationalPoints G) :
    ∃ κ ∈ M.integralPoints, ∃ p ∈ (Dynamic.parabolic lam).carrier (Over.mk (𝟙 _)),
      g = κ * p := by
  have h := hasLeftIntegralCovering_parabolic M hM χ
  rw [hlam] at h
  exact exists_integral_mul_of_hasLeftIntegralCovering M h g

end Dynamic

section Unramified

open IntegralModel Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

/-- The integral Iwasawa factorization after maximal unramified base change, for every
cocharacter `λ` of the base-changed group that is the generic fibre of a cocharacter of
`M.baseChangeUnramified.group`. -/
theorem baseChangeUnramified_exists_integral_mul_parabolic
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (χ : (Gm (Spec (CommRingCat.of (fixedFieldIntegers F)))).toGrp ⟶
      M.baseChangeUnramified.group)
    {lam : (Gm (Spec (CommRingCat.of (inertiaFixedField F)))).toGrp ⟶
      baseChanged F (inertiaFixedField F) G}
    (hlam : Dynamic.baseChangeCocharacter
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) χ ≫
          M.baseChangeUnramified.genericIso.hom = lam)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    ∃ κ ∈ M.baseChangeUnramified.integralPoints,
      ∃ p ∈ (Dynamic.parabolic lam).carrier (Over.mk (𝟙 _)), g = κ * p := by
  have h := baseChangeUnramified_hasLeftIntegralCovering_parabolic M hG hSpecial χ
  rw [hlam] at h
  exact exists_integral_mul_of_hasLeftIntegralCovering M.baseChangeUnramified h g

end Unramified

end Langlands.GroupScheme.HenselianParabolicCovering
