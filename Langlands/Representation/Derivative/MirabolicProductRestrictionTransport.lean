import Langlands.Representation.Induction.Definitions

/-!
# Transport of compact induction along a topological group isomorphism

For an isomorphism of topological groups `φ : H ≃ₜ* H'` carrying a subgroup
`S` onto `S'`, and a linear equivalence `E : V ≃ V'` intertwining an action of
`S` with an action of `S'` through `φ`, the map `f' ↦ E⁻¹ ∘ f' ∘ φ` identifies
compact induction from `S'` pulled back along `φ` with compact induction from
`S`. The identification is natural in compatible coefficient maps.
-/

noncomputable section

namespace Langlands.Induction

universe uR uH uK uV uW

variable {R : Type uR} [CommRing R]
variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {H' : Type uK} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {V' : Type uW} [AddCommGroup V'] [Module R V']

/-- The map `S' \ H' → S \ H` induced by `φ⁻¹`. -/
def transportQuotient (φ : H ≃ₜ* H') (S : Subgroup H) (S' : Subgroup H')
    (hS : ∀ h, h ∈ S ↔ φ h ∈ S') : LeftQuotient S' → LeftQuotient S :=
  Quotient.map' (fun h' => φ.symm h') (by
    intro x y hxy
    have hxy' : y * x⁻¹ ∈ S' := QuotientGroup.rightRel_apply.mp hxy
    apply QuotientGroup.rightRel_apply.mpr
    rw [hS, map_mul, map_inv, φ.apply_symm_apply, φ.apply_symm_apply]
    exact hxy')

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
theorem transportQuotient_mk (φ : H ≃ₜ* H') (S : Subgroup H) (S' : Subgroup H')
    (hS : ∀ h, h ∈ S ↔ φ h ∈ S') (h' : H') :
    transportQuotient φ S S' hS (quotientMap S' h') = quotientMap S (φ.symm h') := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
theorem continuous_transportQuotient (φ : H ≃ₜ* H') (S : Subgroup H) (S' : Subgroup H')
    (hS : ∀ h, h ∈ S ↔ φ h ∈ S') : Continuous (transportQuotient φ S S' hS) :=
  φ.symm.continuous.quotient_map' _

variable (φ : H ≃ₜ* H') (S : Subgroup H) (S' : Subgroup H') (hS : ∀ h, h ∈ S ↔ φ h ∈ S')
  (τ : Representation R S V) (τ' : Representation R S' V') (E : V ≃ₗ[R] V')
  (hE : ∀ (s : S) (v : V), E (τ s v) = τ' ⟨φ s, (hS s).mp s.property⟩ (E v))

omit [IsTopologicalGroup H] in
include hE in
private theorem transport_cov (f' : CompactFunctions S' τ') (s : S) (x : H) :
    E.symm (eval S' τ' f'.1 (φ ((s : H) * x))) = τ s (E.symm (eval S' τ' f'.1 (φ x))) := by
  rw [map_mul]
  have hc := f'.1.1.2 ⟨φ s, (hS s).mp s.property⟩ (φ x)
  change eval S' τ' f'.1 (φ s * φ x) = τ' ⟨φ s, _⟩ (eval S' τ' f'.1 (φ x)) at hc
  rw [hc, LinearEquiv.symm_apply_eq, hE, LinearEquiv.apply_symm_apply]

omit [IsTopologicalGroup H] in
private theorem transport_support (f' : CompactFunctions S' τ') :
    quotientSupport S (fun h => E.symm (eval S' τ' f'.1 (φ h))) =
      transportQuotient φ S S' hS '' quotientSupport S' (eval S' τ' f'.1) := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨quotientMap S' (φ h), ⟨φ h, fun h0 => hh ?_, rfl⟩, ?_⟩
    · change E.symm (eval S' τ' f'.1 (φ h)) = 0
      rw [h0, map_zero]
    · rw [transportQuotient_mk, φ.symm_apply_apply]
  · rintro ⟨_, ⟨h', hh', rfl⟩, rfl⟩
    refine ⟨φ.symm h', fun h0 => hh' ?_, ?_⟩
    · change E.symm (eval S' τ' f'.1 (φ (φ.symm h'))) = 0 at h0
      rw [φ.apply_symm_apply, LinearEquiv.map_eq_zero_iff] at h0
      exact h0
    · rw [transportQuotient_mk]

/-- The transported compactly supported function `h ↦ E⁻¹ (f' (φ h))`. -/
def transportFunction (f' : CompactFunctions S' τ') : CompactFunctions S τ :=
  compactFunctionOf S τ (fun h => E.symm (eval S' τ' f'.1 (φ h)))
    (transport_cov φ S S' hS τ τ' E hE f')
    ((Classical.choose f'.1.2).comap φ.toMonoidHom φ.continuous)
    (fun k x => by
      rw [map_mul]
      have hk := Classical.choose_spec f'.1.2 ⟨φ k, k.property⟩
      exact congrArg (fun F : EquivariantFunctions S' τ' => E.symm (F.1 (φ x))) hk)
    (by
      rw [transport_support (φ := φ) (S := S) (S' := S') (hS := hS) (E := E) (f' := f')]
      exact f'.2.image (continuous_transportQuotient φ S S' hS))

@[simp]
theorem eval_transportFunction (f' : CompactFunctions S' τ') (h : H) :
    eval S τ (transportFunction φ S S' hS τ τ' E hE f').1 h =
      E.symm (eval S' τ' f'.1 (φ h)) := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
include hS in
private theorem hS_symm : ∀ h', h' ∈ S' ↔ φ.symm h' ∈ S := fun h' => by
  rw [hS, φ.apply_symm_apply]

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
include hE in
private theorem hE_symm : ∀ (s : S') (v : V'),
    E.symm (τ' s v) = τ ⟨φ.symm s, (hS_symm φ S S' hS s).mp s.property⟩ (E.symm v) := by
  intro s v
  have h := hE ⟨φ.symm s, (hS_symm φ S S' hS s).mp s.property⟩ (E.symm v)
  have hs : (⟨φ (φ.symm (s : H')), (hS _).mp ((hS_symm φ S S' hS s).mp s.property)⟩ : S') = s :=
    Subtype.ext (φ.apply_symm_apply _)
  rw [hs, LinearEquiv.apply_symm_apply] at h
  rw [← h, LinearEquiv.symm_apply_apply]

/-- Compact induction from `S'` pulled back along `φ` is compact induction from `S`. -/
def compactInducedTransport :
    Representation.Equiv ((compactInduced S' τ').comp φ.toMonoidHom) (compactInduced S τ) where
  toFun := transportFunction φ S S' hS τ τ' E hE
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext x
    exact map_add E.symm _ _
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext x
    exact map_smul E.symm _ _
  invFun := transportFunction φ.symm S' S (hS_symm φ S S' hS) τ' τ E.symm
    (hE_symm φ S S' hS τ τ' E hE)
  left_inv f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext x
    change E.symm.symm (E.symm (eval S' τ' f.1 (φ (φ.symm x)))) = eval S' τ' f.1 x
    rw [φ.apply_symm_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext x
    change E.symm (E.symm.symm (eval S τ f.1 (φ.symm (φ x)))) = eval S τ f.1 x
    rw [φ.symm_apply_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext x
    change E.symm (eval S' τ' f.1 (φ x * φ g)) = E.symm (eval S' τ' f.1 (φ (x * g)))
    rw [map_mul]

@[simp]
theorem eval_compactInducedTransport (f' : CompactFunctions S' τ') (h : H) :
    eval S τ (compactInducedTransport φ S S' hS τ τ' E hE f').1 h =
      E.symm (eval S' τ' f'.1 (φ h)) := rfl

/-- Transport commutes with compact induction of compatible coefficient maps. -/
theorem compactInducedTransport_natural {V₂ : Type uV} [AddCommGroup V₂] [Module R V₂]
    {V₂' : Type uW} [AddCommGroup V₂'] [Module R V₂']
    (τ₂ : Representation R S V₂) (τ₂' : Representation R S' V₂') (E₂ : V₂ ≃ₗ[R] V₂')
    (hE₂ : ∀ (s : S) (v : V₂), E₂ (τ₂ s v) = τ₂' ⟨φ s, (hS s).mp s.property⟩ (E₂ v))
    (T : τ.IntertwiningMap τ₂) (T' : τ'.IntertwiningMap τ₂')
    (hT : ∀ v, E₂ (T v) = T' (E v)) (f' : CompactFunctions S' τ') :
    compactInducedTransport φ S S' hS τ₂ τ₂' E₂ hE₂ (compactInducedMap S' T' f') =
      compactInducedMap S T (compactInducedTransport φ S S' hS τ τ' E hE f') := by
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  funext x
  change E₂.symm (T' (eval S' τ' f'.1 (φ x))) = T (E.symm (eval S' τ' f'.1 (φ x)))
  rw [LinearEquiv.symm_apply_eq, hT, LinearEquiv.apply_symm_apply]

end Langlands.Induction
