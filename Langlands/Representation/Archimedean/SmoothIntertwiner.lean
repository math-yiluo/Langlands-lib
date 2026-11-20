import Langlands.Representation.Archimedean.SmoothDerivativeTopology

/-! # Bounded intertwiners on genuine smooth vectors -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Langlands.Archimedean.SmoothIntertwiner

universe u𝔤 uH uG uE uE'

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  (π : G →* (E →L[ℂ] E)) (π' : G →* (E' →L[ℂ] E'))
  (L : E →L[ℂ] E') (hL : ∀ g v, L (π g v) = π' g (L v))

include hL

/-- A bounded full-group intertwiner preserves genuine smoothness. -/
theorem isSmoothVector_map {v : E} (hv : IsSmoothVector I π v) :
    IsSmoothVector I π' (L v) := by
  have he : orbitMap π' (L v) = (L.restrictScalars ℝ) ∘ orbitMap π v := by
    funext g
    exact (hL g v).symm
  change ContMDiff I 𝓘(ℝ, E') ∞ (orbitMap π' (L v))
  rw [he]
  exact (L.restrictScalars ℝ).contDiff.contMDiff.comp hv

/-- Restriction of a bounded full-group intertwiner to smooth vectors. -/
def map : smoothVectors I π →ₗ[ℂ] smoothVectors I π' where
  toFun v := ⟨L v, isSmoothVector_map I π π' L hL v.property⟩
  map_add' v w := Subtype.ext (map_add L (v : E) (w : E))
  map_smul' c v := Subtype.ext (map_smul L c (v : E))

@[simp]
theorem map_apply (v : smoothVectors I π) :
    (map I π π' L hL v : E') = L v := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chain rule transports the actual real orbit derivative. -/
theorem lieDerivative_map (X : 𝔤) {v : E} (hv : IsSmoothVector I π v) :
    lieDerivative I π' X (L v) = L (lieDerivative I π X v) := by
  let A := L.restrictScalars ℝ
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π v) 1 :=
    hv.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') A (orbitMap π v 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : orbitMap π' (L v) = A ∘ orbitMap π v := by
    funext g
    exact (hL g v).symm
  unfold lieDerivative
  rw [he, mfderiv_comp 1 hA hf, ContinuousLinearMap.mfderiv_eq]
  rfl

variable [LieGroup I ∞ G]

/-- Restriction commutes with the genuine derived operators. -/
theorem map_smoothLieDerivative (X : 𝔤) (v : smoothVectors I π) :
    map I π π' L hL (smoothLieDerivative I π X v) =
      smoothLieDerivative I π' X (map I π π' L hL v) := by
  apply Subtype.ext
  exact (lieDerivative_map I π π' L hL X v.property).symm

/-- Restriction commutes with every genuine word of derived operators. -/
theorem map_smoothIteratedLieDerivative (Xs : List 𝔤) (v : smoothVectors I π) :
    map I π π' L hL (smoothIteratedLieDerivative I π Xs v) =
      smoothIteratedLieDerivative I π' Xs (map I π π' L hL v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      change map I π π' L hL
        (smoothLieDerivative I π X (smoothIteratedLieDerivative I π Xs v)) =
        smoothLieDerivative I π' X
          (smoothIteratedLieDerivative I π' Xs (map I π π' L hL v))
      rw [map_smoothLieDerivative, ih]

/-- Every genuine word derivative is transported by the original bounded map. -/
theorem iteratedLieDerivative_map (Xs : List 𝔤) (v : smoothVectors I π) :
    iteratedLieDerivative I π' Xs (map I π π' L hL v) =
      L (iteratedLieDerivative I π Xs v) := by
  have h := congrArg (fun w : smoothVectors I π' => (w : E'))
    (map_smoothIteratedLieDerivative I π π' L hL Xs v)
  simpa only [map_apply, smoothIteratedLieDerivative_apply] using h.symm

/-- A genuine word seminorm is controlled by the original operator norm. -/
theorem wordSeminorm_map_le (Xs : List 𝔤) (v : smoothVectors I π) :
    wordSeminorm I π' Xs (map I π π' L hL v) ≤
      ‖L‖ * wordSeminorm I π Xs v := by
  rw [wordSeminorm_apply, wordSeminorm_apply, iteratedLieDerivative_map]
  exact L.le_opNorm _

/-- The underlying linear map between the copies with genuine derivative topology. -/
def derivativeMapLinear :
    DerivativeSmoothVectors I π →ₗ[ℂ] DerivativeSmoothVectors I π' :=
  (DerivativeSmoothVectors.toSmooth I π').symm.toLinearMap.comp
    ((map I π π' L hL).comp (DerivativeSmoothVectors.toSmooth I π).toLinearMap)

omit [LieGroup I ∞ G] in
@[simp]
theorem toSmooth_derivativeMapLinear (v : DerivativeSmoothVectors I π) :
    DerivativeSmoothVectors.toSmooth I π'
      (derivativeMapLinear I π π' L hL v) =
      map I π π' L hL (DerivativeSmoothVectors.toSmooth I π v) := rfl

/-- All derivative coordinates of the induced map are the original map on coordinates. -/
theorem derivativeCoordinates_derivativeMapLinear
    (v : DerivativeSmoothVectors I π) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates I π'
      (derivativeMapLinear I π π' L hL v) Xs =
      L (DerivativeSmoothVectors.derivativeCoordinates I π v Xs) := by
  simp only [DerivativeSmoothVectors.derivativeCoordinates_apply,
    toSmooth_derivativeMapLinear, iteratedLieDerivative_map]

theorem continuous_derivativeMapLinear :
    Continuous (derivativeMapLinear I π π' L hL) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun v => DerivativeSmoothVectors.derivativeCoordinates I π'
    (derivativeMapLinear I π π' L hL v) Xs)
  simp_rw [derivativeCoordinates_derivativeMapLinear]
  exact L.continuous.comp (DerivativeSmoothVectors.derivativeCLM I π Xs).continuous

/-- A supplied bounded full-group intertwiner induces a continuous map for the
genuine derivative topologies. -/
def derivativeMap :
    DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π' :=
  ⟨derivativeMapLinear I π π' L hL,
    continuous_derivativeMapLinear I π π' L hL⟩

@[simp]
theorem derivativeMap_apply (v : DerivativeSmoothVectors I π) :
    derivativeMap I π π' L hL v = derivativeMapLinear I π π' L hL v := rfl

/-- Finite-word continuity of a functional pulls back along a bounded intertwiner. -/
theorem isContinuousOnSmoothVectors_comp
    (ℓ : smoothVectors I π' →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors I π' ℓ) :
    IsContinuousOnSmoothVectors I π (ℓ.comp (map I π π' L hL)) := by
  apply isContinuousOnSmoothVectors_of_continuous
  exact (continuous_of_isContinuousOnSmoothVectors I π' ℓ hℓ).comp
    (derivativeMap I π π' L hL).continuous

/-- The induced smooth map intertwines the full smooth representations. -/
theorem map_smoothRepresentation (g : G) (v : smoothVectors I π) :
    map I π π' L hL (smoothRepresentation I π g v) =
      smoothRepresentation I π' g (map I π π' L hL v) := by
  apply Subtype.ext
  exact hL g v

/-- A continuous Whittaker functional pulls back along a bounded full-group intertwiner. -/
theorem isWhittakerFunctional_comp (N : Subgroup G) (χ : N →* ℂˣ)
    (ℓ : smoothVectors I π' →ₗ[ℂ] ℂ) (hℓ : IsWhittakerFunctional I π' N χ ℓ) :
    IsWhittakerFunctional I π N χ (ℓ.comp (map I π π' L hL)) := by
  refine ⟨isContinuousOnSmoothVectors_comp I π π' L hL ℓ hℓ.1, ?_⟩
  intro u v
  change ℓ (map I π π' L hL (smoothRepresentation I π (u : G) v)) =
    (χ u : ℂ) * ℓ (map I π π' L hL v)
  rw [map_smoothRepresentation]
  exact hℓ.2 u _

omit hL

variable (e : E ≃L[ℂ] E') (he : ∀ g v, e (π g v) = π' g (e v))

include he

omit [TopologicalSpace G] in
/-- The inverse of a supplied continuous full-group equivalence also intertwines. -/
theorem intertwining_symm (g : G) (v : E') :
    e.symm (π' g v) = π g (e.symm v) := by
  apply e.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, he,
    ContinuousLinearEquiv.apply_symm_apply]

/-- A continuous full-group equivalence restricts to an equivalence of smooth vectors. -/
def smoothEquiv : smoothVectors I π ≃ₗ[ℂ] smoothVectors I π' where
  toLinearMap := map I π π' e.toContinuousLinearMap he
  invFun := map I π' π e.symm.toContinuousLinearMap (intertwining_symm π π' e he)
  left_inv v := Subtype.ext (e.symm_apply_apply (v : E))
  right_inv v := Subtype.ext (e.apply_symm_apply (v : E'))

omit [LieGroup I ∞ G] in
@[simp]
theorem smoothEquiv_apply (v : smoothVectors I π) :
    (smoothEquiv I π π' e he v : E') = e v := rfl

/-- A continuous full-group equivalence is a homeomorphism for the genuine
derivative topologies, with no density assumption. -/
def derivativeEquiv : DerivativeSmoothVectors I π ≃L[ℂ] DerivativeSmoothVectors I π' where
  toLinearEquiv := (DerivativeSmoothVectors.toSmooth I π).trans
    ((smoothEquiv I π π' e he).trans (DerivativeSmoothVectors.toSmooth I π').symm)
  continuous_toFun := continuous_derivativeMapLinear I π π' e.toContinuousLinearMap he
  continuous_invFun := continuous_derivativeMapLinear I π' π e.symm.toContinuousLinearMap
    (intertwining_symm π π' e he)

@[simp]
theorem toSmooth_derivativeEquiv (v : DerivativeSmoothVectors I π) :
    DerivativeSmoothVectors.toSmooth I π' (derivativeEquiv I π π' e he v) =
      smoothEquiv I π π' e he (DerivativeSmoothVectors.toSmooth I π v) := rfl

/-- Derivative-topology density transports along a supplied full-group equivalence. -/
theorem dense_image_derivativeEquiv_iff (s : Set (DerivativeSmoothVectors I π)) :
    Dense (derivativeEquiv I π π' e he '' s) ↔ Dense s :=
  (derivativeEquiv I π π' e he).toHomeomorph.isDenseEmbedding.dense_image

/-- Finite-word continuity transports in both directions along a supplied equivalence. -/
theorem isContinuousOnSmoothVectors_comp_iff
    (ℓ : smoothVectors I π' →ₗ[ℂ] ℂ) :
    IsContinuousOnSmoothVectors I π (ℓ.comp (smoothEquiv I π π' e he).toLinearMap) ↔
      IsContinuousOnSmoothVectors I π' ℓ := by
  constructor
  · intro h
    have h' := isContinuousOnSmoothVectors_comp I π' π e.symm.toContinuousLinearMap
      (intertwining_symm π π' e he) _ h
    have heq :
        (ℓ.comp (smoothEquiv I π π' e he).toLinearMap).comp
          (map I π' π e.symm.toContinuousLinearMap (intertwining_symm π π' e he)) = ℓ := by
      ext v
      apply congrArg ℓ
      apply Subtype.ext
      exact e.apply_symm_apply (v : E')
    rwa [heq] at h'
  · exact isContinuousOnSmoothVectors_comp I π π' e.toContinuousLinearMap he ℓ

/-- The Whittaker predicate transports in both directions along a supplied equivalence. -/
theorem isWhittakerFunctional_comp_iff (N : Subgroup G) (χ : N →* ℂˣ)
    (ℓ : smoothVectors I π' →ₗ[ℂ] ℂ) :
    IsWhittakerFunctional I π N χ (ℓ.comp (smoothEquiv I π π' e he).toLinearMap) ↔
      IsWhittakerFunctional I π' N χ ℓ := by
  constructor
  · intro h
    have h' := isWhittakerFunctional_comp I π' π e.symm.toContinuousLinearMap
      (intertwining_symm π π' e he) N χ _ h
    have heq :
        (ℓ.comp (smoothEquiv I π π' e he).toLinearMap).comp
          (map I π' π e.symm.toContinuousLinearMap (intertwining_symm π π' e he)) = ℓ := by
      ext v
      apply congrArg ℓ
      apply Subtype.ext
      exact e.apply_symm_apply (v : E')
    rwa [heq] at h'
  · exact isWhittakerFunctional_comp I π π' e.toContinuousLinearMap he N χ ℓ

omit [LieGroup I ∞ G] in
/-- Pullback by a supplied equivalence preserves nonvanishing of functionals. -/
theorem comp_eq_zero_iff (ℓ : smoothVectors I π' →ₗ[ℂ] ℂ) :
    ℓ.comp (smoothEquiv I π π' e he).toLinearMap = 0 ↔ ℓ = 0 := by
  constructor
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := (smoothEquiv I π π' e he).surjective v
    exact congrArg (fun f : smoothVectors I π →ₗ[ℂ] ℂ => f w) h
  · intro h
    simp [h]

end Langlands.Archimedean.SmoothIntertwiner
