import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-!
# Affine root systems detected by pullback along a surjective affine map

Let `π : A → A'` be a surjective affine map of real affine spaces and let `Ψ ⊆ A*`,
`Ψ' ⊆ A'*` be sets of affine functionals such that `ψ' ∈ Ψ'` exactly when `ψ' ∘ π ∈ Ψ`. If `Ψ`
is an affine root system (in the rank-zero-admitting form of KP Definition 1.3.1) and the
derivatives of `Ψ'` span the dual of the translation space of `A'`, then `Ψ'` is an affine root
system. The derivatives of `Ψ'` are those linear forms whose pullback is a derivative of `Ψ`.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uV' uA'

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {V' : Type uV'} {A' : Type uA'} [AddCommGroup V'] [Module ℝ V'] [AddTorsor V' A']

section Pullback

variable (π : A →ᵃ[ℝ] A')

theorem comp_linear_eq (ψ : A' →ᵃ[ℝ] ℝ) : (ψ.comp π).linear = ψ.linear.comp π.linear :=
  rfl

variable {π}

/-- Pulling back affine functionals along a surjective affine map is injective. -/
theorem comp_injective_of_surjective (hπ : Function.Surjective π) :
    Function.Injective fun ψ : A' →ᵃ[ℝ] ℝ => ψ.comp π := by
  intro ψ η h
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  exact congrArg (fun f : A →ᵃ[ℝ] ℝ => f x) h

/-- Pulling back linear forms along a surjective linear part is injective. -/
theorem linear_comp_injective_of_surjective (hπ : Function.Surjective π) :
    Function.Injective fun f : Module.Dual ℝ V' => f.comp π.linear := by
  intro f g h
  ext v
  obtain ⟨w, rfl⟩ := (π.linear_surjective_iff.2 hπ) v
  exact LinearMap.congr_fun h w

variable (π) in
/-- An affine functional whose derivative factors through `π.linear` is a pullback. -/
theorem exists_comp_eq_of_linear_eq {ψ : A →ᵃ[ℝ] ℝ} {f : Module.Dual ℝ V'}
    (hf : ψ.linear = f.comp π.linear) :
    ∃ ψ' : A' →ᵃ[ℝ] ℝ, ψ'.linear = f ∧ ψ'.comp π = ψ := by
  obtain ⟨p⟩ : Nonempty A := inferInstance
  refine ⟨AffineMap.mk' (fun y => f (y -ᵥ π p) + ψ p) f (π p) (fun y => by simp), ?_, ?_⟩
  · exact AffineMap.mk'_linear _ _ _ _
  · ext x
    rw [AffineMap.comp_apply, AffineMap.coe_mk', ← AffineMap.linearMap_vsub,
      ← LinearMap.comp_apply, ← hf, AffineMap.linearMap_vsub, vsub_eq_sub, sub_add_cancel]

theorem sub_smul_comp (η ψ : A' →ᵃ[ℝ] ℝ) (c : ℝ) :
    (η - c • ψ).comp π = η.comp π - c • ψ.comp π := by
  ext x
  rfl

theorem smul_comp' (ψ : A' →ᵃ[ℝ] ℝ) (c : ℝ) : (c • ψ).comp π = c • ψ.comp π := by
  ext x
  rfl

/-- Uniqueness of coroot vectors (KP Remark 1.3.2(2)) from only the finiteness and spanning
parts of AR 1. -/
theorem isCoroot_unique_of_finite_of_span {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hfin : (derivativeRoots Ψ).Finite)
    (hspan : Submodule.span ℝ (derivativeRoots Ψ) = ⊤)
    {ψ : A →ᵃ[ℝ] ℝ} {v w : V} (hv : IsCoroot Ψ ψ v) (hw : IsCoroot Ψ ψ w) : v = w := by
  have hmaps : ∀ u : V, IsCoroot Ψ ψ u →
      Set.MapsTo (Module.preReflection ψ.linear (Module.Dual.eval ℝ V u))
        (derivativeRoots Ψ) (derivativeRoots Ψ) := by
    rintro u hu _ ⟨η, hη, rfl⟩
    refine ⟨η - η.linear u • ψ, hu.2 η hη, ?_⟩
    simp [Module.preReflection_apply]
  have h := Module.Dual.eq_of_preReflection_mapsTo hfin hspan (by simpa using hv.1)
    (hmaps v hv) (by simpa using hw.1) (hmaps w hw)
  exact Module.eval_apply_injective ℝ h

/-- A finite set of linear forms with trivial common kernel spans the dual space. -/
theorem span_eq_top_of_finite_of_forall_eq_zero {R : Set (Module.Dual ℝ V)} (hR : R.Finite)
    (h : ∀ v : V, (∀ f ∈ R, f v = 0) → v = 0) : Submodule.span ℝ R = ⊤ := by
  have : FiniteDimensional ℝ (Submodule.span ℝ R) := FiniteDimensional.span_of_finite ℝ hR
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℝ R)]
  have hbot : (Submodule.span ℝ R).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℝ).2 (h v fun f hf => hv f (Submodule.subset_span hf))
  rw [hbot, Submodule.dualAnnihilator_bot]

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Ψ' : Set (A' →ᵃ[ℝ] ℝ)}

/-- The derivatives of `Ψ'` are computed from those of `Ψ` when membership in `Ψ'` is detected
by pullback. -/
theorem derivativeRoots_eq_of_comp (hmem : ∀ ψ' : A' →ᵃ[ℝ] ℝ, ψ' ∈ Ψ' ↔ ψ'.comp π ∈ Ψ)
    {R : Set (Module.Dual ℝ V')} (hR : derivativeRoots Ψ' ⊆ R)
    (hcover : ∀ f ∈ R, f.comp π.linear ∈ derivativeRoots Ψ) :
    derivativeRoots Ψ' = R := by
  refine le_antisymm hR fun f hf => ?_
  obtain ⟨ψ, hψ, hψf⟩ := hcover f hf
  obtain ⟨ψ', hψ'f, rfl⟩ := exists_comp_eq_of_linear_eq π hψf
  exact ⟨ψ', (hmem ψ').2 hψ, hψ'f⟩

/-- An affine root system pulled back along a surjective affine map: if `Ψ` is an affine root
system, membership in `Ψ'` is detected by pullback to `Ψ`, and the derivatives of `Ψ'` span,
then `Ψ'` is an affine root system. -/
theorem isAffineRootSystemWithRankZero_of_comp (hπ : Function.Surjective π)
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hmem : ∀ ψ' : A' →ᵃ[ℝ] ℝ, ψ' ∈ Ψ' ↔ ψ'.comp π ∈ Ψ)
    (hspan : Submodule.span ℝ (derivativeRoots Ψ') = ⊤) :
    IsAffineRootSystemWithRankZero Ψ' := by
  have hfin : (derivativeRoots Ψ').Finite := by
    refine Set.Finite.of_finite_image (f := fun f : Module.Dual ℝ V' => f.comp π.linear) ?_
      (linear_comp_injective_of_surjective hπ).injOn
    refine hΨ.finite_derivativeRoots.subset ?_
    rintro _ ⟨_, ⟨ψ', hψ', rfl⟩, rfl⟩
    exact ⟨ψ'.comp π, (hmem ψ').1 hψ', rfl⟩
  have hcor : ∀ ψ' ∈ Ψ', ∀ v : V, IsCoroot Ψ (ψ'.comp π) v →
      IsCoroot Ψ' ψ' (π.linear v) := by
    intro ψ' _ v hv
    refine ⟨hv.1, fun η' hη' => (hmem _).2 ?_⟩
    rw [sub_smul_comp]
    exact hv.2 _ ((hmem η').1 hη')
  refine ⟨hspan, fun ψ' hψ' h0 => ?_, hfin, fun ψ' hψ' => ?_, ?_, ?_, ?_⟩
  · apply hΨ.linear_ne_zero _ ((hmem ψ').1 hψ')
    rw [comp_linear_eq, h0, LinearMap.zero_comp]
  · obtain ⟨v, hv⟩ := hΨ.exists_isCoroot _ ((hmem ψ').1 hψ')
    exact ⟨π.linear v, hcor ψ' hψ' v hv⟩
  · intro ψ' hψ' η' hη' w hw
    obtain ⟨v, hv⟩ := hΨ.exists_isCoroot _ ((hmem η').1 hη')
    have hw' : w = π.linear v := isCoroot_unique_of_finite_of_span hfin hspan hw
      (hcor η' hη' v hv)
    obtain ⟨n, hn⟩ := hΨ.coroot_integral _ ((hmem ψ').1 hψ') _ ((hmem η').1 hη') v hv
    exact ⟨n, by rw [hw']; exact hn⟩
  · intro ψ' hψ'
    refine Set.Infinite.of_image (fun η' : A' →ᵃ[ℝ] ℝ => η'.comp π)
      ((hΨ.infinite_fiber _ ((hmem ψ').1 hψ')).mono ?_)
    rintro η ⟨hη, hηl⟩
    obtain ⟨η', hη'l, rfl⟩ := exists_comp_eq_of_linear_eq π (f := ψ'.linear) hηl
    exact ⟨η', ⟨(hmem η').2 hη, hη'l⟩, rfl⟩
  · intro ψ' hψ' M
    refine ((hΨ.finite_bounded _ ((hmem ψ').1 hψ') M).preimage
      (comp_injective_of_surjective hπ).injOn).subset ?_
    rintro η' ⟨hη', hl, hb⟩
    exact ⟨(hmem η').1 hη', by rw [comp_linear_eq, comp_linear_eq, hl], fun x => hb (π x)⟩

end Pullback

end Langlands.Geometry.Building.AffineRootSystem
