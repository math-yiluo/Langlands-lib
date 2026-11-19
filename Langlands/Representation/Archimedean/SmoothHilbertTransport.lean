import Langlands.Representation.Archimedean.SmoothHilbert

/-! # Transport of Hilbert representations and their smooth vectors -/

noncomputable section

open scoped Manifold ContDiff Topology Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section ContinuousRepresentations

variable {G : Type*} [Group G] {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  (T : E ≃L[ℂ] E') (R : G →* (E →L[ℂ] E))

/-- Conjugate a representation by a continuous complex linear equivalence. -/
def transportRepresentation : G →* (E' →L[ℂ] E') where
  toFun g := T.toContinuousLinearMap.comp ((R g).comp T.symm.toContinuousLinearMap)
  map_one' := by
    ext x
    change T (R 1 (T.symm x)) = x
    simp [map_one, one_apply_eq_self]
  map_mul' g h := by
    ext x
    change T (R (g * h) (T.symm x)) = T (R g (T.symm (T (R h (T.symm x)))))
    rw [map_mul, mul_apply_eq_comp, T.symm_apply_apply]

@[simp]
theorem transportRepresentation_apply (g : G) (x : E') :
    transportRepresentation T R g x = T (R g (T.symm x)) := rfl

@[simp]
theorem transportRepresentation_apply_image (g : G) (x : E) :
    transportRepresentation T R g (T x) = T (R g x) := by simp

/-- Joint continuity is preserved by conjugating with a continuous linear equivalence. -/
theorem IsContinuousRepresentation.transport [TopologicalSpace G]
    (h : IsContinuousRepresentation R) : IsContinuousRepresentation (transportRepresentation T R) := by
  let q : G × E' → G × E := fun p => (p.1, T.symm p.2)
  have hq : Continuous q := continuous_fst.prodMk (T.symm.continuous.comp continuous_snd)
  unfold IsContinuousRepresentation at h ⊢
  simpa only [Function.comp_def, q, transportRepresentation_apply] using
    T.continuous.comp (h.comp hq)

/-- Closed invariant subspaces transfer through the underlying homeomorphism. -/
theorem IsTopologicallyIrreducible.transport (h : IsTopologicallyIrreducible R) :
    IsTopologicallyIrreducible (transportRepresentation T R) := by
  let A := T.toLinearEquiv.toLinearMap
  have hA := Submodule.comap_injective_of_surjective (f := A) T.surjective
  have : Nontrivial E := h.1
  refine ⟨T.injective.nontrivial, ?_⟩
  intro P hc hP
  have hc' : IsClosed (P.comap A : Set E) := hc.preimage T.continuous
  have hs (g : G) (v : E) (hv : v ∈ P.comap A) : R g v ∈ P.comap A := by
    change T (R g v) ∈ P
    rw [← transportRepresentation_apply_image]
    exact hP g (T v) hv
  rcases h.2 (P.comap A) hc' hs with hb | ht
  · exact Or.inl (hA (hb.trans ((Submodule.comap_bot A).trans
      (LinearMap.ker_eq_bot.mpr T.injective)).symm))
  · exact Or.inr (hA (ht.trans (Submodule.comap_top A).symm))

/-- Postcomposition by the inverse equivalence injects the transported compact intertwiners
into the original intertwiner space. -/
theorem IsAdmissible.transport [TopologicalSpace G] {K : Subgroup G}
    (h : IsAdmissible R K) : IsAdmissible (transportRepresentation T R) K := by
  intro d τ hτ
  let L : ((Fin d → ℂ) →ₗ[ℂ] E') →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] E) :=
    T.symm.toLinearEquiv.toLinearMap.compRight ℂ
  let L' := L.restrict (p := intertwiners (transportRepresentation T R) K d τ)
    (q := intertwiners R K d τ) (fun f hf => by
      intro k x
      change T.symm (f (τ k *ᵥ x)) = R (k : G) (T.symm (f x))
      rw [show f (τ k *ᵥ x) = transportRepresentation T R (k : G) (f x) from hf k x,
        transportRepresentation_apply, T.symm_apply_apply])
  have : FiniteDimensional ℂ (intertwiners R K d τ) := h d τ hτ
  apply FiniteDimensional.of_injective L'
  intro f g hfg
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact T.symm.injective (congrArg (fun u : intertwiners R K d τ => u.1 x) hfg)

end ContinuousRepresentations

section SmoothVectors

variable {𝔤 M G E E' : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  [TopologicalSpace M] (I : ModelWithCorners ℝ 𝔤 M)
  [Group G] [TopologicalSpace G] [ChartedSpace M G] [LieGroup I ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  (T : E ≃L[ℂ] E') (R : G →* (E →L[ℂ] E))

local notation "S" => transportRepresentation T R

omit [TopologicalSpace G] in
private theorem orbitMap_transport (v : E) : orbitMap S (T v) = T ∘ orbitMap R v := by
  funext g
  exact transportRepresentation_apply_image T R g v

omit [LieGroup I ∞ G] in
private theorem isSmoothVector_transport_iff (v : E) :
    IsSmoothVector I S (T v) ↔ IsSmoothVector I R v := by
  unfold IsSmoothVector
  rw [orbitMap_transport T R]
  constructor
  · intro hv
    have h := (T.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.comp hv
    change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => T.symm (T (orbitMap R v g))) at h
    simpa only [T.symm_apply_apply] using h
  · intro hv
    exact (T.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.comp hv

omit [LieGroup I ∞ G] in
private theorem lieDerivative_transport (X : 𝔤) {v : E} (hv : IsSmoothVector I R v) :
    lieDerivative I S X (T v) = T (lieDerivative I R X v) := by
  let P := T.toContinuousLinearMap.restrictScalars ℝ
  have hd : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap R v) 1 := hv.mdifferentiableAt (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') P (orbitMap R v 1) :=
    P.differentiableAt.mdifferentiableAt
  unfold lieDerivative
  rw [show orbitMap S (T v) = P ∘ orbitMap R v from orbitMap_transport T R v,
    mfderiv_comp 1 hP hd, ContinuousLinearMap.mfderiv_eq]
  rfl

omit [LieGroup I ∞ G] in
private def smoothVectorTransport : smoothVectors I R ≃ₗ[ℂ] smoothVectors I S where
  toFun v := ⟨T v, (isSmoothVector_transport_iff I T R v).2 v.2⟩
  invFun w := ⟨T.symm w, (isSmoothVector_transport_iff I T R (T.symm w)).1 (by
    rw [T.apply_symm_apply]
    exact w.2)⟩
  left_inv v := Subtype.ext (T.symm_apply_apply v)
  right_inv w := Subtype.ext (T.apply_symm_apply w)
  map_add' v w := Subtype.ext (T.map_add v w)
  map_smul' c v := Subtype.ext (T.map_smul c v)

/-- The transported equivalence on the carriers with the genuine derivative topology. -/
def derivativeSmoothTransport : DerivativeSmoothVectors I R ≃ₗ[ℂ] DerivativeSmoothVectors I S :=
  (DerivativeSmoothVectors.toSmooth I R).trans
    ((smoothVectorTransport I T R).trans (DerivativeSmoothVectors.toSmooth I S).symm)

open DerivativeSmoothVectors in
@[simp]
theorem derivativeSmoothTransport_representation (g : G) (v : DerivativeSmoothVectors I R) :
    derivativeSmoothTransport I T R (representation I R g v) =
      representation I S g (derivativeSmoothTransport I T R v) := by
  apply (toSmooth I S).injective
  apply Subtype.ext
  exact (transportRepresentation_apply_image T R g (toSmooth I R v)).symm

open DerivativeSmoothVectors in
@[simp]
theorem derivativeSmoothTransport_operator (X : 𝔤) (v : DerivativeSmoothVectors I R) :
    derivativeSmoothTransport I T R (operator I R X v) =
      operator I S X (derivativeSmoothTransport I T R v) := by
  apply (toSmooth I S).injective
  apply Subtype.ext
  exact (lieDerivative_transport I T R X (toSmooth I R v).2).symm

private theorem iteratedLieDerivative_transport (s : List 𝔤) (v : smoothVectors I R) :
    iteratedLieDerivative I S s (T v) = T (iteratedLieDerivative I R s v) := by
  induction s with
  | nil => rfl
  | cons X s ih =>
      rw [iteratedLieDerivative_cons, ih, iteratedLieDerivative_cons]
      have hv : IsSmoothVector I R (iteratedLieDerivative I R s v) := by
        rw [← smoothIteratedLieDerivative_apply]
        exact (smoothIteratedLieDerivative I R s v).2
      exact lieDerivative_transport I T R X hv

/-- The transported equivalence is continuous for the genuine word topology. -/
theorem continuous_derivativeSmoothTransport : Continuous (derivativeSmoothTransport I T R) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro s
  have h (v : DerivativeSmoothVectors I R) :
      DerivativeSmoothVectors.derivativeCoordinates I S (derivativeSmoothTransport I T R v) s =
        T (DerivativeSmoothVectors.derivativeCLM I R s v) := by
    simp only [DerivativeSmoothVectors.derivativeCoordinates_apply, DerivativeSmoothVectors.derivativeCLM_apply]
    exact iteratedLieDerivative_transport I T R s (DerivativeSmoothVectors.toSmooth I R v)
  simpa only [Function.comp_def, h] using
    T.continuous.comp (DerivativeSmoothVectors.derivativeCLM I R s).continuous

end SmoothVectors

section CompactFinite

variable (F : Type) [RCLike F] (n : ℕ) {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  (T : E ≃L[ℂ] E') (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

local notation "I" => matrixModel F n
local notation "S" => transportRepresentation T R

private def compactIntertwiningTransport :
    (smoothHilbertCompactRepresentation F n R).IntertwiningMap
      (smoothHilbertCompactRepresentation F n S) where
  toLinearMap := (derivativeSmoothTransport I T R).toLinearMap
  isIntertwining' k := by
    apply LinearMap.ext
    intro v
    exact derivativeSmoothTransport_representation I T R (Unitary.toUnits k) v

/-- The equivalence on smooth vectors restricts to the two compact-finite subspaces. -/
def smoothHilbertKFiniteTransport :
    smoothHilbertKFinite F n R ≃ₗ[ℂ] smoothHilbertKFinite F n S := by
  let A := compactIntertwiningTransport F n T R
  let B := derivativeSmoothTransport I T R
  have hA : Function.Injective A := B.injective
  apply LinearEquiv.ofBijective (FiniteVectors.map A).toLinearMap
  constructor
  · intro v w h
    exact Subtype.ext (hA (congrArg Subtype.val h))
  · intro w
    let v := B.symm w.1
    have hvw : A v = w.1 := B.apply_symm_apply w.1
    have hw : FiniteVectors.IsFiniteVector (smoothHilbertCompactRepresentation F n S) (A v) :=
      hvw.symm ▸ w.2
    have hv := (FiniteVectors.isFiniteVector_map_iff A hA v).1 hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩

@[simp]
theorem coe_smoothHilbertKFiniteTransport (v : smoothHilbertKFinite F n R) :
    (smoothHilbertKFiniteTransport F n T R v : DerivativeSmoothVectors I S) =
      derivativeSmoothTransport I T R v.1 := rfl

end CompactFinite

end Langlands.Archimedean
