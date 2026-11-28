import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.Representation.Compact.FiniteMean
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.FiniteQuotientProjection

/-! # Injectivity of Hecke means from a support condition

Let `J` be a compact open subgroup of a topological group `G`, `ρ` an irreducible smooth
finite-dimensional representation of `J`, `π` a smooth representation of `G` and
`Φ ∈ Hom_J(ρ, π)`. For `x ∈ G` and an intertwiner `Θ ∈ I_x(ρ)`, the Hecke mean of `Φ` is the
mean of the finite orbit of `π(x) ∘ Φ ∘ Θ` under `F ↦ π(j) ∘ F ∘ ρ(j)⁻¹`.

Let `ζ` be a type contraction (`IsTypeContraction`): `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)`, conjugation
by `ζ` and by `ζ⁻¹` maps `J ∩ M` into itself, `ζ⁻¹ U ζ ⊆ U`, `ζ (J ∩ U) ζ⁻¹ ⊆ J ∩ U`,
`ζ U⁻ ζ⁻¹ ⊆ U⁻` and `ζ⁻¹ (J ∩ U⁻) ζ ⊆ J ∩ U⁻`. Let `Θ ∈ I_ζ(ρ)` be nonzero and suppose all
orbits of `J` on linear maps `W → V` are finite. If every element `y ∈ U` with `ζ y ζ⁻¹ ∈ J`
that intertwines `ρ` lies in `J`, then the Hecke means of all powers `ζ^k` (with `Θ^k`) are
injective on `Hom_J(ρ, π)`
(`IsTypeContraction.heckeMean_injective`), and so are those of `(m ζ^e)^r` for `m ∈ J` commuting
with `ζ` (`IsTypeContraction.heckeMean_injective_translate`). The argument applies a
`J`-equivariant retraction `ψ` of `Φ` (`exists_equivariant_retraction`): `ψ ∘ π(x) ∘ Φ` lies in
`I_{x⁻¹}(ρ)` (`retractionIntertwiner`), so all orbit points except `π(ζ) ∘ Φ ∘ Θ` are killed,
and the remaining one gives `Θ`. Powers reduce to `ζ` by the composition formula
`heckeMean_comp`. The module also proves the double coset lemma `mem_of_mem_doubleCoset`: a Levi
element in `J x J` with `x ∈ U` lies in `J`. -/

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

open Langlands.Compact

universe uG uV uW

section Iwahori

variable {G : Type uG} [Group G]

/-- **Levi elements in a double coset of a unipotent element.** Suppose `J` has the factorization
`J = (J ∩ U)(J ∩ M)(J ∩ U⁻)`, that `M` normalizes `U` and `U⁻`, that `M ∩ U = 1`, and that an
element of `U⁻` lying in `M U` is trivial. If `d ∈ M` lies in `J x J` for some `x ∈ U`, then
`d ∈ J`. -/
theorem mem_of_mem_doubleCoset {J U M Ubar : Subgroup G}
    (hfac : ∀ j ∈ J, ∃ u ∈ J ⊓ U, ∃ m ∈ J ⊓ M, ∃ l ∈ J ⊓ Ubar, j = u * m * l)
    (hMU : ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U)
    (hMUbar : ∀ m ∈ M, ∀ l ∈ Ubar, m * l * m⁻¹ ∈ Ubar)
    (hMU1 : ∀ u ∈ U, u ∈ M → u = 1)
    (hUbar1 : ∀ l ∈ Ubar, ∀ m ∈ M, ∀ u ∈ U, l = m * u → l = 1)
    {d x j₁ j₂ : G} (hd : d ∈ M) (hx : x ∈ U) (hj₁ : j₁ ∈ J) (hj₂ : j₂ ∈ J)
    (hdx : d = j₁ * x * j₂) : d ∈ J := by
  -- `j₁ = l₁ m₁ u₁` and `j₂ = u₂ m₂ l₂`
  obtain ⟨u, hu, m, hm, l, hl, hj₁'⟩ := hfac j₁⁻¹ (J.inv_mem hj₁)
  obtain ⟨u₂, hu₂, m₂, hm₂, l₂, hl₂, hj₂'⟩ := hfac j₂ hj₂
  have hj₁e : j₁ = l⁻¹ * m⁻¹ * u⁻¹ := by
    rw [← inv_inv j₁, hj₁']; group
  -- `x' = u⁻¹ x u₂ ∈ U`
  set x' := u⁻¹ * x * u₂ with hx'
  have hx'U : x' ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu.2) hx) hu₂.2
  -- `d l₂⁻¹ (d⁻¹ l d) ... `
  have key : d * ((d⁻¹ * l * d) * l₂⁻¹) = (m⁻¹ * m₂) * (m₂⁻¹ * x' * m₂) := by
    rw [hdx, hj₁e, hj₂', hx']; group
  have hl0 : (d⁻¹ * l * d) * l₂⁻¹ ∈ Ubar := by
    refine Ubar.mul_mem ?_ (Ubar.inv_mem hl₂.2)
    have := hMUbar d⁻¹ (M.inv_mem hd) l hl.2
    simpa using this
  have hm0 : m⁻¹ * m₂ ∈ M := M.mul_mem (M.inv_mem hm.2) hm₂.2
  have hx0 : m₂⁻¹ * x' * m₂ ∈ U := by
    have := hMU m₂⁻¹ (M.inv_mem hm₂.2) x' hx'U
    simpa using this
  -- the `U⁻`-part is trivial
  have hl1 : (d⁻¹ * l * d) * l₂⁻¹ = 1 := by
    refine hUbar1 _ hl0 (d⁻¹ * (m⁻¹ * m₂)) (M.mul_mem (M.inv_mem hd) hm0) _ hx0 ?_
    calc (d⁻¹ * l * d) * l₂⁻¹ = d⁻¹ * (d * ((d⁻¹ * l * d) * l₂⁻¹)) := by group
      _ = d⁻¹ * (m⁻¹ * m₂) * (m₂⁻¹ * x' * m₂) := by rw [key]; group
  rw [hl1, mul_one] at key
  -- the `U`-part is trivial
  have hx1 : m₂⁻¹ * x' * m₂ = 1 := by
    refine hMU1 _ hx0 ?_
    have : m₂⁻¹ * x' * m₂ = (m⁻¹ * m₂)⁻¹ * d := by rw [key]; group
    rw [this]
    exact M.mul_mem (M.inv_mem hm0) hd
  rw [hx1, mul_one] at key
  rw [key]
  exact J.mul_mem (J.inv_mem hm.1) hm₂.1

end Iwahori

section Intertwining

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The map `ψ ∘ π(x) ∘ Φ` attached to a `J`-equivariant retraction `ψ`, as an element of the
intertwining space `I_{x⁻¹}(ρ)`. -/
def retractionIntertwiner {J : Subgroup G} (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (ψ : V →ₗ[ℂ] W)
    (hψ : ∀ j : J, ψ ∘ₗ π j = ρ j ∘ₗ ψ) (x : G) : intertwiningSpace ρ ρ x⁻¹ where
  toLinearMap := ψ ∘ₗ π x ∘ₗ Φ.toLinearMap
  isIntertwining' h := by
    obtain ⟨h, hh⟩ := h
    have hJ : x⁻¹ * h * x⁻¹⁻¹ ∈ J := ((mem_intertwiningDomain).mp hh).1
    have hJ' : h ∈ J := ((mem_intertwiningDomain).mp hh).2
    ext w
    change ψ (π x (Φ (ρ ⟨x⁻¹ * h * x⁻¹⁻¹, hJ⟩ w))) = ρ ⟨h, hJ'⟩ (ψ (π x (Φ w)))
    have h1 : Φ (ρ ⟨x⁻¹ * h * x⁻¹⁻¹, hJ⟩ w) = π (x⁻¹ * h * x⁻¹⁻¹) (Φ w) :=
      Φ.isIntertwining _ _ ⟨x⁻¹ * h * x⁻¹⁻¹, hJ⟩ w
    have h2 : π x (π (x⁻¹ * h * x⁻¹⁻¹) (Φ w)) = π h (π x (Φ w)) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (π h), ← map_mul]
      congr 2
      group
    rw [h1, h2]
    exact LinearMap.congr_fun (hψ ⟨h, hJ'⟩) (π x (Φ w))

theorem retractionIntertwiner_eq_zero {J : Subgroup G} (π : Representation ℂ G V)
    (ρ : Representation ℂ J W) (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (ψ : V →ₗ[ℂ] W)
    (hψ : ∀ j : J, ψ ∘ₗ π j = ρ j ∘ₗ ψ) {x : G}
    (hx : x⁻¹ ∉ representationSelfIntertwining ρ) :
    ψ ∘ₗ π x ∘ₗ Φ.toLinearMap = 0 := by
  by_contra hne
  apply hx
  refine ⟨retractionIntertwiner π ρ Φ ψ hψ x, fun h0 => hne ?_⟩
  have := congrArg Representation.IntertwiningMap.toLinearMap h0
  exact this

end Intertwining

section HeckeMean

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- For `d ∈ J` with `x⁻¹ d x ∈ J` and `Θ ∈ I_x(ρ)`, the map `π(x) ∘ Φ ∘ Θ` is fixed by `d` under
`F ↦ π(d) ∘ F ∘ ρ(d)⁻¹`. -/
theorem linHom_fixed {J : Subgroup G} (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (x : G) (Θ : intertwiningSpace ρ ρ x) (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (d : J)
    (hd : x⁻¹ * d * x ∈ J) :
    Representation.linHom ρ (π.comp J.subtype) d (π x ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap) =
      π x ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap := by
  rw [Representation.linHom_apply]
  ext w
  have hk : x⁻¹ * (d : G)⁻¹ * x ∈ intertwiningDomain J J x := by
    rw [mem_intertwiningDomain]
    refine ⟨?_, ?_⟩
    · have e : x * (x⁻¹ * (d : G)⁻¹ * x) * x⁻¹ = (d : G)⁻¹ := by group
      rw [e]
      exact J.inv_mem d.property
    · have e : x⁻¹ * (d : G)⁻¹ * x = (x⁻¹ * d * x)⁻¹ := by group
      rw [e]
      exact J.inv_mem hd
  have hΘ : Θ (ρ (intertwiningDomainConj J J x ⟨_, hk⟩) w) =
      ρ (intertwiningDomainIncl J J x ⟨_, hk⟩) (Θ w) :=
    Θ.isIntertwining _ _ ⟨_, hk⟩ w
  have e1 : intertwiningDomainConj J J x ⟨_, hk⟩ = d⁻¹ := by
    apply Subtype.ext
    simp only [coe_intertwiningDomainConj, InvMemClass.coe_inv]
    group
  rw [e1] at hΘ
  simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
  rw [hΘ]
  have hΦ := Φ.isIntertwining _ _ (intertwiningDomainIncl J J x ⟨_, hk⟩) (Θ w)
  rw [hΦ]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    coe_intertwiningDomainIncl]
  rw [← Module.End.mul_apply (π x), ← map_mul, ← Module.End.mul_apply (π (d : G)), ← map_mul]
  congr 2
  group

/-- The orbit of a translate is the orbit. -/
theorem orbit_apply_eq {H : Type*} [Group H] (τ : Representation ℂ H V) (h : H) (v : V) :
    orbit τ (τ h v) = orbit τ v := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * h, by simp [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k * h⁻¹, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (τ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- **Injectivity of a Hecke mean from a support condition.** Let `ψ` be a `J`-equivariant
retraction of `Φ ∈ Hom_J(ρ, π)`, and `ζ ∈ G` with `J = (J ∩ U)(J ∩ ζ J ζ⁻¹)` and `ζ⁻¹ U ζ ⊆ U`.
Suppose every `y ∈ U` with `ζ y ζ⁻¹ ∈ J` that intertwines `ρ` lies in `J`. Let `Θ ∈ I_ζ(ρ)` be
such that the `J`-orbit of `π(ζ) ∘ Φ ∘ Θ` is finite. If the mean of this orbit vanishes, then
`Θ = 0`. -/
theorem eq_zero_of_heckeMean_eq_zero {J U : Subgroup G} (π : Representation ℂ G V)
    (ρ : Representation ℂ J W) (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (ψ : V →ₗ[ℂ] W)
    (hψ : ∀ j : J, ψ ∘ₗ π j = ρ j ∘ₗ ψ) (hψΦ : ψ ∘ₗ Φ.toLinearMap = LinearMap.id)
    (ζ : G) (Θ : intertwiningSpace ρ ρ ζ)
    (hfac : ∀ j ∈ J, ∃ u ∈ J ⊓ U, ∃ d ∈ J, ζ⁻¹ * d * ζ ∈ J ∧ j = u * d)
    (hnorm : ∀ u ∈ U, ζ⁻¹ * u * ζ ∈ U)
    (hsupp : ∀ y ∈ U, ζ * y * ζ⁻¹ ∈ J → y ∈ representationSelfIntertwining ρ → y ∈ J)
    [hfin : Finite (orbit (Representation.linHom ρ (π.comp J.subtype))
      (π ζ ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap))]
    (h0 : orbitMean (Representation.linHom ρ (π.comp J.subtype))
      (π ζ ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap) = 0) :
    Θ = 0 := by
  classical
  set τ := Representation.linHom ρ (π.comp J.subtype) with hτ
  set F₀ := π ζ ∘ₗ Φ.toLinearMap ∘ₗ Θ.toLinearMap with hF₀
  let := Fintype.ofFinite (orbit τ F₀)
  -- the evaluation `F ↦ ψ ∘ π(ζ⁻¹) ∘ F`
  let Λ : (W →ₗ[ℂ] V) →ₗ[ℂ] (W →ₗ[ℂ] W) := LinearMap.llcomp ℂ W V W (ψ ∘ₗ π ζ⁻¹)
  have hΛ : ∀ F, Λ F = ψ ∘ₗ π ζ⁻¹ ∘ₗ F := fun F => rfl
  -- every orbit point other than `F₀` is killed by `Λ`
  have hvan : ∀ y : orbit τ F₀, y.val ≠ F₀ → Λ y.val = 0 := by
    intro y hy
    obtain ⟨j, hj'⟩ := y.property
    rw [← hj'] at hy ⊢
    change τ j F₀ ≠ F₀ at hy
    change Λ (τ j F₀) = 0
    obtain ⟨u, hu, d, hd, hdζ, hj⟩ := hfac j j.property
    have hjd : τ j F₀ = τ ⟨u, hu.1⟩ F₀ := by
      have hfix := linHom_fixed π ρ ζ Θ Φ ⟨d, hd⟩ hdζ
      have e : j = (⟨u, hu.1⟩ : J) * ⟨d, hd⟩ := Subtype.ext hj
      rw [e, map_mul, Module.End.mul_apply]
      exact congrArg _ hfix
    rw [hjd] at hy ⊢
    -- `x = ζ⁻¹ u ζ` is not in `J`
    have hx : ζ⁻¹ * u * ζ ∉ J := by
      intro hxJ
      exact hy (linHom_fixed π ρ ζ Θ Φ ⟨u, hu.1⟩ hxJ)
    have hxinv : (ζ⁻¹ * u * ζ)⁻¹ ∉ representationSelfIntertwining ρ := by
      intro hI
      have hyU : (ζ⁻¹ * u * ζ)⁻¹ ∈ U := by
        have := hnorm u⁻¹ (U.inv_mem hu.2)
        have e : (ζ⁻¹ * u * ζ)⁻¹ = ζ⁻¹ * u⁻¹ * ζ := by group
        rw [e]; exact this
      have hyJ : ζ * (ζ⁻¹ * u * ζ)⁻¹ * ζ⁻¹ ∈ J := by
        have e : ζ * (ζ⁻¹ * u * ζ)⁻¹ * ζ⁻¹ = u⁻¹ := by group
        rw [e]; exact J.inv_mem hu.1
      exact hx (by simpa using J.inv_mem (hsupp _ hyU hyJ hI))
    have hzero := retractionIntertwiner_eq_zero π ρ Φ ψ hψ hxinv
    rw [hΛ, Representation.linHom_apply]
    have e : ψ ∘ₗ π ζ⁻¹ ∘ₗ ((π.comp J.subtype) ⟨u, hu.1⟩ ∘ₗ F₀ ∘ₗ ρ ⟨u, hu.1⟩⁻¹) =
        (ψ ∘ₗ π (ζ⁻¹ * u * ζ) ∘ₗ Φ.toLinearMap) ∘ₗ (Θ.toLinearMap ∘ₗ ρ ⟨u, hu.1⟩⁻¹) := by
      rw [hF₀]
      ext v
      simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, map_mul, Module.End.mul_apply]
    rw [e, hzero, LinearMap.zero_comp]
  -- `Λ F₀ = Θ`
  have hF₀Λ : Λ F₀ = Θ.toLinearMap := by
    rw [hΛ, hF₀]
    ext w
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply (π ζ⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact LinearMap.congr_fun hψΦ _
  have hmem : F₀ ∈ orbit τ F₀ := ⟨1, by simp⟩
  have hsum : ∑ y : orbit τ F₀, Λ y.val = Θ.toLinearMap := by
    rw [Finset.sum_eq_single_of_mem (⟨F₀, hmem⟩ : orbit τ F₀) (Finset.mem_univ _)]
    · exact hF₀Λ
    · intro y _ hy
      exact hvan y (fun h => hy (Subtype.ext h))
  have hc : (Fintype.card (orbit τ F₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmean : Λ (orbitMean τ F₀) = (Fintype.card (orbit τ F₀) : ℂ)⁻¹ • Θ.toLinearMap := by
    rw [orbitMean_eq_finiteMean]
    change Λ ((Fintype.card (orbit τ F₀) : ℂ)⁻¹ • ∑ y : orbit τ F₀, y.val) = _
    rw [map_smul, map_sum, hsum]
  rw [h0, map_zero] at hmean
  have : Θ.toLinearMap = 0 := (smul_eq_zero.mp hmean.symm).resolve_left (inv_ne_zero hc)
  ext w
  exact LinearMap.congr_fun this w

end HeckeMean

section Composition

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The orbit mean as a linear map, when every orbit is finite. -/
def meanLin {H X : Type*} [Group H] [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ H X)
    (hfin : ∀ x, Finite (orbit τ x)) : X →ₗ[ℂ] X where
  toFun := orbitMean τ
  map_add' x y := by
    have := hfin x; have := hfin y; have := hfin (x + y)
    exact orbitMean_add τ x y
  map_smul' c x := by
    have := hfin x; have := hfin (c • x)
    exact orbitMean_smul τ c x

theorem meanLin_apply {H X : Type*} [Group H] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H X) (hfin : ∀ x, Finite (orbit τ x)) (x : X) :
    meanLin τ hfin x = orbitMean τ x := rfl

/-- The orbit mean of a translate is the orbit mean. -/
theorem orbitMean_apply_eq {H X : Type*} [Group H] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H X) (h : H) (x : X) : orbitMean τ (τ h x) = orbitMean τ x := by
  unfold orbitMean
  rw [orbit_apply_eq]

/-- **Composition of Hecke means.** Suppose all orbits of `J` on linear maps `W → V` are
finite, and every point of the `J`-orbit of
`F = π(ζ^r) ∘ Φ ∘ Θ'` is `u · F` for some `u ∈ J` with `ζ u ζ⁻¹ ∈ J`, and that
`Θ ∘ ρ(ζ u ζ⁻¹) = ρ(u) ∘ Θ` for such `u`. Then the Hecke mean of `ζ` and `Θ` applied to the
Hecke mean of `F` is the Hecke mean of `π(ζ^{r+1}) ∘ Φ ∘ (Θ' ∘ Θ)`. -/
theorem heckeMean_comp {J : Subgroup G} (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (Φ : W →ₗ[ℂ] V) (ζ : G) (Θ Θ' : W →ₗ[ℂ] W) (r : ℕ)
    (hfin : ∀ F, Finite (orbit (Representation.linHom ρ (π.comp J.subtype)) F))
    (horb : ∀ y ∈ orbit (Representation.linHom ρ (π.comp J.subtype)) (π (ζ ^ r) ∘ₗ Φ ∘ₗ Θ'),
      ∃ u : J, ∃ _ : ζ * u * ζ⁻¹ ∈ J,
        y = Representation.linHom ρ (π.comp J.subtype) u (π (ζ ^ r) ∘ₗ Φ ∘ₗ Θ'))
    (hΘ : ∀ (u : J) (hu : ζ * u * ζ⁻¹ ∈ J), Θ ∘ₗ ρ ⟨ζ * u * ζ⁻¹, hu⟩ = ρ u ∘ₗ Θ) :
    orbitMean (Representation.linHom ρ (π.comp J.subtype))
        (π ζ ∘ₗ orbitMean (Representation.linHom ρ (π.comp J.subtype))
          (π (ζ ^ r) ∘ₗ Φ ∘ₗ Θ') ∘ₗ Θ) =
      orbitMean (Representation.linHom ρ (π.comp J.subtype))
        (π (ζ ^ (r + 1)) ∘ₗ Φ ∘ₗ (Θ' ∘ₗ Θ)) := by
  classical
  set τ := Representation.linHom ρ (π.comp J.subtype) with hτ
  set F := π (ζ ^ r) ∘ₗ Φ ∘ₗ Θ' with hF
  set F' := π (ζ ^ (r + 1)) ∘ₗ Φ ∘ₗ (Θ' ∘ₗ Θ) with hF'
  have := hfin F
  let := Fintype.ofFinite (orbit τ F)
  let Ξ : (W →ₗ[ℂ] V) →ₗ[ℂ] (W →ₗ[ℂ] V) :=
    (LinearMap.llcomp ℂ W V V (π ζ)).comp ((LinearMap.llcomp ℂ W W V).flip Θ)
  have hΞ : ∀ G', Ξ G' = π ζ ∘ₗ G' ∘ₗ Θ := fun G' => rfl
  -- each orbit point contributes the mean of `F'`
  have hterm : ∀ y : orbit τ F, meanLin τ hfin (Ξ y.val) = orbitMean τ F' := by
    intro y
    obtain ⟨u, hu, hy⟩ := horb y.val y.property
    rw [meanLin_apply, hy, hΞ]
    have e : π ζ ∘ₗ τ u F ∘ₗ Θ = τ ⟨ζ * u * ζ⁻¹, hu⟩ F' := by
      rw [hτ, Representation.linHom_apply, Representation.linHom_apply, hF, hF']
      have hΘ' : ρ u⁻¹ ∘ₗ Θ = Θ ∘ₗ ρ ⟨ζ * u * ζ⁻¹, hu⟩⁻¹ := by
        have h1 := hΘ u hu
        ext w
        have h2 := LinearMap.congr_fun h1 (ρ ⟨ζ * u * ζ⁻¹, hu⟩⁻¹ w)
        simp only [LinearMap.comp_apply] at h2
        rw [← Module.End.mul_apply (ρ _), ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h2
        simp only [LinearMap.comp_apply]
        rw [h2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      ext w
      have h3 := LinearMap.congr_fun hΘ' w
      simp only [LinearMap.comp_apply] at h3
      simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype]
      rw [h3]
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [pow_succ']
      group
    rw [e]
    exact orbitMean_apply_eq τ _ F'
  have hc : (Fintype.card (orbit τ F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change meanLin τ hfin (Ξ (orbitMean τ F)) = orbitMean τ F'
  rw [orbitMean_eq_finiteMean]
  change meanLin τ hfin (Ξ ((Fintype.card (orbit τ F) : ℂ)⁻¹ • ∑ y : orbit τ F, y.val)) = _
  rw [map_smul, map_smul, map_sum, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

end Composition

section IntertwinerAt

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A linear map `T` with `T ∘ ρ(x h x⁻¹) = ρ(h) ∘ T` for all `h ∈ J` with `x h x⁻¹ ∈ J`: the
underlying map of an element of `I_x(ρ)`. -/
def IsIntertwinerAt {J : Subgroup G} (ρ : Representation ℂ J W) (x : G) (T : W →ₗ[ℂ] W) : Prop :=
  ∀ (h : J) (hh : x * h * x⁻¹ ∈ J), T ∘ₗ ρ ⟨x * h * x⁻¹, hh⟩ = ρ h ∘ₗ T

/-- The element of `I_x(ρ)` with underlying map `T`. -/
def IsIntertwinerAt.toSpace {J : Subgroup G} {ρ : Representation ℂ J W} {x : G}
    {T : W →ₗ[ℂ] W} (hT : IsIntertwinerAt ρ x T) : intertwiningSpace ρ ρ x where
  toLinearMap := T
  isIntertwining' h := by
    obtain ⟨h, hh⟩ := h
    have h1 := hT ⟨h, ((mem_intertwiningDomain).mp hh).2⟩ ((mem_intertwiningDomain).mp hh).1
    exact h1

theorem isIntertwinerAt_of_space {J : Subgroup G} {ρ : Representation ℂ J W} {x : G}
    (Θ : intertwiningSpace ρ ρ x) : IsIntertwinerAt ρ x Θ.toLinearMap := by
  intro h hh
  have hd : (h : G) ∈ intertwiningDomain J J x := (mem_intertwiningDomain).mpr ⟨hh, h.property⟩
  ext w
  exact Θ.isIntertwining _ _ ⟨h, hd⟩ w

/-- Translating by `m ∈ J`: if `T ∈ I_x(ρ)` then `T ∘ ρ(m)⁻¹ ∈ I_{m x}(ρ)`. -/
theorem IsIntertwinerAt.mul_left {J : Subgroup G} {ρ : Representation ℂ J W} {x : G}
    {T : W →ₗ[ℂ] W} (hT : IsIntertwinerAt ρ x T) (m : J) :
    IsIntertwinerAt ρ (m * x) (T ∘ₗ ρ m⁻¹) := by
  intro h hh
  have hh' : x * h * x⁻¹ ∈ J := by
    have e : x * (h : G) * x⁻¹ = (m : G)⁻¹ * (m * x * h * (m * x)⁻¹) * m := by group
    rw [e]
    exact J.mul_mem (J.mul_mem (J.inv_mem m.property) hh) m.property
  have h1 := hT h hh'
  have e : (⟨m * x * h * (m * x)⁻¹, hh⟩ : J) = m * ⟨x * h * x⁻¹, hh'⟩ * m⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  rw [e, map_mul, map_mul]
  ext w
  have h2 := LinearMap.congr_fun h1 (ρ m⁻¹ w)
  simp only [LinearMap.comp_apply, Module.End.mul_apply] at h2 ⊢
  rw [← Module.End.mul_apply (ρ m⁻¹) (ρ m), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, h2]

end IntertwinerAt

section Contraction

variable {G : Type uG} [Group G]

/-- An Iwahori factorization `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)` with an element `ζ` such that
conjugation by `ζ` and by `ζ⁻¹` maps `J ∩ M` into itself, `ζ⁻¹ U ζ ⊆ U`,
`ζ (J ∩ U) ζ⁻¹ ⊆ J ∩ U`, `ζ U⁻ ζ⁻¹ ⊆ U⁻` and `ζ⁻¹ (J ∩ U⁻) ζ ⊆ J ∩ U⁻`. The element `ζ` need not
commute with `J ∩ M`. -/
structure IsTypeContraction (J U M Ubar : Subgroup G) (ζ : G) : Prop where
  factor : ∀ j ∈ J, ∃ u ∈ J ⊓ U, ∃ m ∈ J ⊓ M, ∃ l ∈ J ⊓ Ubar, j = u * m * l
  levi : ∀ m ∈ J ⊓ M, ζ * m * ζ⁻¹ ∈ J ⊓ M ∧ ζ⁻¹ * m * ζ ∈ J ⊓ M
  upperNorm : ∀ x ∈ U, ζ⁻¹ * x * ζ ∈ U
  upper : ∀ u ∈ J ⊓ U, ζ * u * ζ⁻¹ ∈ J ⊓ U
  lowerNorm : ∀ l ∈ Ubar, ζ * l * ζ⁻¹ ∈ Ubar
  lower : ∀ l ∈ J ⊓ Ubar, ζ⁻¹ * l * ζ ∈ J ⊓ Ubar

namespace IsTypeContraction

variable {J U M Ubar : Subgroup G} {ζ : G} (h : IsTypeContraction J U M Ubar ζ)
include h

theorem upper_pow (k : ℕ) : ∀ u ∈ J ⊓ U, ζ ^ k * u * (ζ ^ k)⁻¹ ∈ J ⊓ U := by
  induction k with
  | zero => intro u hu; simpa using hu
  | succ k ih =>
    intro u hu
    have e : ζ ^ (k + 1) * u * (ζ ^ (k + 1))⁻¹ = ζ * (ζ ^ k * u * (ζ ^ k)⁻¹) * ζ⁻¹ := by group
    rw [e]
    exact h.upper _ (ih u hu)

theorem lower_pow (k : ℕ) : ∀ l ∈ J ⊓ Ubar, (ζ ^ k)⁻¹ * l * ζ ^ k ∈ J ⊓ Ubar := by
  induction k with
  | zero => intro l hl; simpa using hl
  | succ k ih =>
    intro l hl
    have e : (ζ ^ (k + 1))⁻¹ * l * ζ ^ (k + 1) = ζ⁻¹ * ((ζ ^ k)⁻¹ * l * ζ ^ k) * ζ := by group
    rw [e]
    exact h.lower _ (ih l hl)

theorem levi_pow (k : ℕ) : ∀ m ∈ J ⊓ M, (ζ ^ k)⁻¹ * m * ζ ^ k ∈ J ⊓ M := by
  induction k with
  | zero => intro m hm; simpa using hm
  | succ k ih =>
    intro m hm
    have e : (ζ ^ (k + 1))⁻¹ * m * ζ ^ (k + 1) = ζ⁻¹ * ((ζ ^ k)⁻¹ * m * ζ ^ k) * ζ := by group
    rw [e]
    exact (h.levi _ (ih m hm)).2

theorem levi_pow' (k : ℕ) : ∀ m ∈ J ⊓ M, ζ ^ k * m * (ζ ^ k)⁻¹ ∈ J ⊓ M := by
  induction k with
  | zero => intro m hm; simpa using hm
  | succ k ih =>
    intro m hm
    have e : ζ ^ (k + 1) * m * (ζ ^ (k + 1))⁻¹ = ζ * (ζ ^ k * m * (ζ ^ k)⁻¹) * ζ⁻¹ := by group
    rw [e]
    exact (h.levi _ (ih m hm)).1

theorem lowerNorm_pow (k : ℕ) : ∀ l ∈ Ubar, ζ ^ k * l * (ζ ^ k)⁻¹ ∈ Ubar := by
  induction k with
  | zero => intro l hl; simpa using hl
  | succ k ih =>
    intro l hl
    have e : ζ ^ (k + 1) * l * (ζ ^ (k + 1))⁻¹ = ζ * (ζ ^ k * l * (ζ ^ k)⁻¹) * ζ⁻¹ := by group
    rw [e]
    exact h.lowerNorm _ (ih l hl)

/-- Elements of `J ∩ ζ⁻ⁿ J ζⁿ` stay in `J` under conjugation by `ζ^t` for every `t ≤ n`. -/
theorem convex {n t : ℕ} (htn : t ≤ n) {x : G} (hx : x ∈ J) (hxn : ζ ^ n * x * (ζ ^ n)⁻¹ ∈ J) :
    ζ ^ t * x * (ζ ^ t)⁻¹ ∈ J := by
  obtain ⟨u, hu, m, hm, l, hl, rfl⟩ := h.factor x hx
  have hl' : ζ ^ n * l * (ζ ^ n)⁻¹ ∈ J ⊓ Ubar := by
    refine ⟨?_, h.lowerNorm_pow n l hl.2⟩
    have e : ζ ^ n * l * (ζ ^ n)⁻¹ = (ζ ^ n * m * (ζ ^ n)⁻¹)⁻¹ * (ζ ^ n * u * (ζ ^ n)⁻¹)⁻¹ *
        (ζ ^ n * (u * m * l) * (ζ ^ n)⁻¹) := by group
    rw [e]
    exact J.mul_mem (J.mul_mem (J.inv_mem (h.levi_pow' n m hm).1)
      (J.inv_mem (h.upper_pow n u hu).1)) hxn
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le htn
  have hlt : ζ ^ t * l * (ζ ^ t)⁻¹ ∈ J := by
    have e : ζ ^ t * l * (ζ ^ t)⁻¹ =
        (ζ ^ s)⁻¹ * (ζ ^ (t + s) * l * (ζ ^ (t + s))⁻¹) * ζ ^ s := by
      rw [pow_add]; group
    rw [e]
    exact (h.lower_pow s _ hl').1
  have e : ζ ^ t * (u * m * l) * (ζ ^ t)⁻¹ =
      (ζ ^ t * u * (ζ ^ t)⁻¹) * (ζ ^ t * m * (ζ ^ t)⁻¹) * (ζ ^ t * l * (ζ ^ t)⁻¹) := by group
  rw [e]
  exact J.mul_mem (J.mul_mem (h.upper_pow t u hu).1 (h.levi_pow' t m hm).1) hlt

/-- Every `j ∈ J` is `u d` with `u ∈ J ∩ U` and `ζ^{-k} d ζ^k ∈ J`. -/
theorem factor_stab (k : ℕ) {j : G} (hj : j ∈ J) :
    ∃ u ∈ J ⊓ U, ∃ d ∈ J, (ζ ^ k)⁻¹ * d * ζ ^ k ∈ J ∧ j = u * d := by
  obtain ⟨u, hu, m, hm, l, hl, rfl⟩ := h.factor j hj
  refine ⟨u, hu, m * l, J.mul_mem hm.1 hl.1, ?_, by group⟩
  have e : (ζ ^ k)⁻¹ * (m * l) * ζ ^ k = ((ζ ^ k)⁻¹ * m * ζ ^ k) * ((ζ ^ k)⁻¹ * l * ζ ^ k) := by
    group
  rw [e]
  exact J.mul_mem (h.levi_pow k m hm).1 (h.lower_pow k l hl).1

end IsTypeContraction

end Contraction

section Powers

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An orbit mean over a finite orbit is fixed by the group. -/
theorem orbitMean_fixed {H X : Type*} [Group H] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H X) (x : X) [Finite (orbit τ x)] (h : H) :
    τ h (orbitMean τ x) = orbitMean τ x := by
  classical
  let := Fintype.ofFinite (orbit τ x)
  rw [orbitMean_eq_finiteMean]
  change τ h ((Fintype.card (orbit τ x) : ℂ)⁻¹ • ∑ y : orbit τ x, y.val) =
    (Fintype.card (orbit τ x) : ℂ)⁻¹ • ∑ y : orbit τ x, y.val
  rw [map_smul, map_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (orbit τ x)) (fun y => y.val)

/-- The orbit mean of a fixed vector is the vector. -/
theorem orbitMean_of_fixed {H X : Type*} [Group H] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H X) (x : X) (hx : ∀ h, τ h x = x) : orbitMean τ x = x := by
  have horb : orbit τ x = {x} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩; exact hx h
    · intro hy; rw [Set.mem_singleton_iff] at hy; exact ⟨1, by simp [hy]⟩
  unfold orbitMean
  rw [horb]
  simp only [Nat.card_unique, Nat.cast_one, inv_one, one_smul]
  rw [finsum_eq_single (fun y : ({x} : Set X) => (y : X)) ⟨x, rfl⟩]
  intro y hy
  exact absurd (Subtype.ext (Set.mem_singleton_iff.mp y.property)) hy

/-- A linear map fixed by `F ↦ π(j) ∘ F ∘ ρ(j)⁻¹` for all `j` is `J`-equivariant. -/
theorem equivariant_of_fixed {J : Subgroup G} (π : Representation ℂ G V)
    (ρ : Representation ℂ J W) (F : W →ₗ[ℂ] V)
    (hF : ∀ j, Representation.linHom ρ (π.comp J.subtype) j F = F) (j : J) :
    F ∘ₗ ρ j = π j ∘ₗ F := by
  have h1 := hF j
  rw [Representation.linHom_apply] at h1
  conv_lhs => rw [← h1]
  ext w
  simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  rw [← Module.End.mul_apply (ρ j⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The intertwining map with underlying map an equivariant `F`. -/
def intertwiningOfEquivariant {J : Subgroup G} (π : Representation ℂ G V)
    (ρ : Representation ℂ J W) (F : W →ₗ[ℂ] V) (hF : ∀ j : J, F ∘ₗ ρ j = π j ∘ₗ F) :
    ρ.IntertwiningMap (π.comp J.subtype) where
  toLinearMap := F
  isIntertwining' j := hF j

variable {J U M Ubar : Subgroup G} {ζ : G}

/-- If `Θ ∈ I_ζ(ρ)` then `Θ^k ∈ I_{ζ^k}(ρ)`. -/
theorem IsTypeContraction.pow_intertwiner (h : IsTypeContraction J U M Ubar ζ)
    {ρ : Representation ℂ J W} {Θ : W →ₗ[ℂ] W} (hΘ : IsIntertwinerAt ρ ζ Θ) (k : ℕ) :
    IsIntertwinerAt ρ (ζ ^ k) (Θ ^ k) := by
  induction k with
  | zero =>
    intro x hx
    have e : (⟨ζ ^ 0 * x * (ζ ^ 0)⁻¹, hx⟩ : J) = x := Subtype.ext (by simp)
    rw [e, pow_zero, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
  | succ k ih =>
    intro x hx
    have hk : ζ ^ k * x * (ζ ^ k)⁻¹ ∈ J := h.convex (Nat.le_succ k) x.property hx
    have hk1 : ζ * (ζ ^ k * x * (ζ ^ k)⁻¹) * ζ⁻¹ ∈ J := by
      have e : ζ * (ζ ^ k * x * (ζ ^ k)⁻¹) * ζ⁻¹ = ζ ^ (k + 1) * x * (ζ ^ (k + 1))⁻¹ := by
        rw [pow_succ']; group
      rw [e]; exact hx
    have h1 := hΘ ⟨_, hk⟩ hk1
    have h2 := ih x hk
    have e : (⟨ζ ^ (k + 1) * x * (ζ ^ (k + 1))⁻¹, hx⟩ : J) =
        ⟨ζ * (ζ ^ k * x * (ζ ^ k)⁻¹) * ζ⁻¹, hk1⟩ := Subtype.ext (by
          change ζ ^ (k + 1) * x * (ζ ^ (k + 1))⁻¹ = ζ * (ζ ^ k * x * (ζ ^ k)⁻¹) * ζ⁻¹
          rw [pow_succ']; group)
    rw [e, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc,
      h2, LinearMap.comp_assoc]

/-- **Powers of a Hecke mean.** Suppose all orbits of `J` on linear maps `W → V` are finite and
`Θ ∈ I_ζ(ρ)`. For an intertwiner `Φ`, the `(k+1)`-fold iterate of `F ↦ mean(π(ζ) ∘ F ∘ Θ)` is
the Hecke mean of `π(ζ^{k+1}) ∘ Φ ∘ Θ^{k+1}`. -/
theorem IsTypeContraction.iterate_heckeMean (h : IsTypeContraction J U M Ubar ζ)
    (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (hfin : ∀ F, Finite (orbit (Representation.linHom ρ (π.comp J.subtype)) F))
    (Φ : ρ.IntertwiningMap (π.comp J.subtype)) {Θ : W →ₗ[ℂ] W} (hΘ : IsIntertwinerAt ρ ζ Θ)
    (k : ℕ) :
    (fun F => orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π ζ ∘ₗ F ∘ₗ Θ))^[k + 1]
        Φ.toLinearMap =
      orbitMean (Representation.linHom ρ (π.comp J.subtype))
        (π (ζ ^ (k + 1)) ∘ₗ Φ.toLinearMap ∘ₗ Θ ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hcomp := heckeMean_comp π ρ Φ.toLinearMap ζ Θ (Θ ^ (k + 1)) (k + 1) hfin ?_
      (fun u hu => hΘ u hu)
    · rw [hcomp, pow_succ Θ (k + 1), Module.End.mul_eq_comp]
    · intro y hy
      obtain ⟨j, rfl⟩ := hy
      obtain ⟨u, hu, d, hd, hdζ, hj⟩ := h.factor_stab (k + 1) j.property
      refine ⟨⟨u, hu.1⟩, (h.upper u hu).1, ?_⟩
      have hfix := linHom_fixed π ρ (ζ ^ (k + 1)) (h.pow_intertwiner hΘ (k + 1)).toSpace Φ
        ⟨d, hd⟩ hdζ
      have e : j = (⟨u, hu.1⟩ : J) * ⟨d, hd⟩ := Subtype.ext hj
      change Representation.linHom ρ (π.comp J.subtype) j _ = _
      rw [e, map_mul, Module.End.mul_apply]
      exact congrArg _ hfix

/-- Suppose all orbits of `J` on linear maps `W → V` are finite and `Θ ∈ I_ζ(ρ)`. If the Hecke
mean of `ζ` and `Θ` is injective on equivariant maps, so is the Hecke mean of `ζ^k` and `Θ^k` on
intertwiners, for every `k`. -/
theorem IsTypeContraction.heckeMean_pow_eq_zero (h : IsTypeContraction J U M Ubar ζ)
    (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (hfin : ∀ F, Finite (orbit (Representation.linHom ρ (π.comp J.subtype)) F))
    {Θ : W →ₗ[ℂ] W} (hΘ : IsIntertwinerAt ρ ζ Θ)
    (hinj : ∀ F : W →ₗ[ℂ] V, (∀ j : J, F ∘ₗ ρ j = π j ∘ₗ F) →
      orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π ζ ∘ₗ F ∘ₗ Θ) = 0 → F = 0)
    (k : ℕ) (Φ : ρ.IntertwiningMap (π.comp J.subtype))
    (h0 : orbitMean (Representation.linHom ρ (π.comp J.subtype))
      (π (ζ ^ k) ∘ₗ Φ.toLinearMap ∘ₗ Θ ^ k) = 0) : Φ = 0 := by
  set τ := Representation.linHom ρ (π.comp J.subtype) with hτ
  have hΦfix : ∀ j : J, τ j Φ.toLinearMap = Φ.toLinearMap := by
    intro j
    rw [hτ, Representation.linHom_apply]
    ext w
    have := Φ.isIntertwining _ _ j⁻¹ w
    change (π.comp J.subtype) j (Φ (ρ j⁻¹ w)) = Φ w
    rw [this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let T : (W →ₗ[ℂ] V) → (W →ₗ[ℂ] V) := fun F => orbitMean τ (π ζ ∘ₗ F ∘ₗ Θ)
  have hTeq : ∀ F, ∀ j : J, T F ∘ₗ ρ j = π j ∘ₗ T F := fun F j =>
    equivariant_of_fixed π ρ (T F) (fun j' => by
      have := hfin (π ζ ∘ₗ F ∘ₗ Θ)
      exact orbitMean_fixed τ _ j') j
  have hiter : ∀ n, T^[n] Φ.toLinearMap = 0 → Φ = 0 := by
    intro n
    induction n with
    | zero =>
      intro hz
      ext w
      exact LinearMap.congr_fun hz w
    | succ n ih =>
      intro hz
      rw [Function.iterate_succ_apply'] at hz
      apply ih
      refine hinj _ ?_ hz
      cases n with
      | zero => exact fun j => Φ.isIntertwining' j
      | succ n =>
        rw [Function.iterate_succ_apply']
        exact hTeq _
  cases k with
  | zero =>
    apply hiter 0
    rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearMap.comp_id, map_one,
      Module.End.one_eq_id, LinearMap.id_comp, orbitMean_of_fixed τ _ hΦfix] at h0
    exact h0
  | succ k =>
    apply hiter (k + 1)
    rw [h.iterate_heckeMean π ρ hfin Φ hΘ k]
    exact h0

end Powers

section Retraction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Equivariant retraction.** An injective intertwiner from a smooth finite-dimensional
representation of a compact open subgroup `J` into a smooth representation of `G` has a
`J`-equivariant linear left inverse. -/
theorem exists_equivariant_retraction {J : Subgroup G} (hJo : IsOpen (J : Set G))
    (hJc : IsCompact (J : Set G)) (π : Representation ℂ G V) (hπ : IsSmooth π)
    (ρ : Representation ℂ J W) [FiniteDimensional ℂ W] (hρ : IsSmooth ρ)
    (Φ : ρ.IntertwiningMap (π.comp J.subtype)) (hinj : Function.Injective Φ) :
    ∃ ψ : V →ₗ[ℂ] W, (∀ j : J, ψ ∘ₗ π j = ρ j ∘ₗ ψ) ∧ ψ ∘ₗ Φ.toLinearMap = LinearMap.id := by
  classical
  -- the kernel of `ρ` is open in `J`
  let K₀ : Subgroup J := ρ.ker
  let b := Module.finBasis ℂ W
  choose O hO using fun i => hρ (b i)
  let K' : Subgroup J := ⨅ i, (O i).toSubgroup
  have hK'o : IsOpen (K' : Set J) := by
    simp only [K', Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => (O i).isOpen
  have hK'le : K' ≤ K₀ := by
    intro k hk
    have hk' : ∀ i, k ∈ (O i).toSubgroup := Subgroup.mem_iInf.mp hk
    rw [MonoidHom.mem_ker]
    exact b.ext fun i => hO i ⟨k, hk' i⟩
  have hK₀o : IsOpen (K₀ : Set J) := Subgroup.isOpen_mono hK'le hK'o
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJc
  have : Finite (J ⧸ K₀) := Subgroup.quotient_finite_of_isOpen _ hK₀o
  let := Fintype.ofFinite (J ⧸ K₀)
  let : Invertible (Fintype.card (J ⧸ K₀) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- the image of `K₀` in `G` as a compact open subgroup
  let K : Subgroup G := K₀.map J.subtype
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = Subtype.val '' (K₀ : Set J) := by
      ext x; simp [K]
    rw [this]
    exact hJo.isOpenMap_subtype_val _ hK₀o
  have hKc : IsCompact (K : Set G) := by
    have : (K : Set G) = Subtype.val '' (K₀ : Set J) := by
      ext x; simp [K]
    rw [this]
    exact ((Subgroup.isClosed_of_isOpen _ hK₀o).isCompact).image continuous_subtype_val
  let KO : OpenSubgroup G := ⟨K, hKo⟩
  let e := Compact.averageMap π hπ KO hKc
  -- a linear left inverse composed with the average
  obtain ⟨ψ₀, hψ₀⟩ := LinearMap.exists_leftInverse_of_injective Φ.toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  have hfix : ∀ w, Φ w ∈ fixedVectors π KO.toSubgroup := by
    rintro w ⟨k, hk⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
    change π n (Φ w) = Φ w
    have h1 := Φ.isIntertwining _ _ n w
    have h2 : ρ n = 1 := hn
    rw [h2, Module.End.one_apply] at h1
    exact h1.symm
  let p : Representation.IntertwiningMap ((π.comp J.subtype).comp K₀.subtype)
      (ρ.comp K₀.subtype) :=
    { toLinearMap := ψ₀ ∘ₗ e
      isIntertwining' := fun n => by
        ext v
        have h2 : ρ n = 1 := n.property
        simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
          Subgroup.coe_subtype, h2, Module.End.one_apply]
        congr 1
        have hn : ((n : J) : G) ∈ KO.toSubgroup := Subgroup.mem_map_of_mem _ n.property
        exact orbitMean_apply_eq (π.comp KO.toSubgroup.subtype) ⟨_, hn⟩ v }
  have hp : Function.LeftInverse p Φ := by
    intro w
    change ψ₀ (e (Φ w)) = w
    rw [Compact.averageMap_id π hπ KO hKc _ (hfix w)]
    exact LinearMap.congr_fun hψ₀ w
  let ψ := Langlands.FiniteQuotientAveraging.intertwinerAverage (π.comp J.subtype) ρ K₀ p
  refine ⟨ψ.toLinearMap, fun j => ψ.isIntertwining' j, ?_⟩
  ext w
  exact Langlands.FiniteQuotientAveraging.intertwinerAverage_leftInverse
    (π.comp J.subtype) ρ K₀ p Φ hp w

end Retraction

section Package

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Translating the Hecke element by `m ∈ J` moves `ρ(m)` into the intertwiner. -/
theorem heckeMean_mul_left {J : Subgroup G} (π : Representation ℂ G V) (ρ : Representation ℂ J W)
    (F : W →ₗ[ℂ] V) (m : J) (x : G) (T : W →ₗ[ℂ] W) :
    orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π (m * x) ∘ₗ F ∘ₗ T) =
      orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π x ∘ₗ F ∘ₗ (T ∘ₗ ρ m)) := by
  have e : π (m * x) ∘ₗ F ∘ₗ T =
      Representation.linHom ρ (π.comp J.subtype) m (π x ∘ₗ F ∘ₗ (T ∘ₗ ρ m)) := by
    rw [Representation.linHom_apply]
    ext w
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ m), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e]
  exact orbitMean_apply_eq _ _ _

variable {J U M Ubar : Subgroup G} {ζ : G}

/-- **Injectivity of all Hecke means of powers of a type contraction.** Let `ρ` be an irreducible
smooth finite-dimensional representation of a compact open subgroup `J`, `π` a smooth
representation of `G` such that all orbits of `J` on linear maps `W → V` are finite, `ζ` a type
contraction, and `Θ ∈ I_ζ(ρ)` nonzero. Suppose every `y ∈ U` with `ζ y ζ⁻¹ ∈ J` that intertwines
`ρ` lies in `J`. Then for every `k` the Hecke mean of `ζ^k` and `Θ^k` is injective on
`Hom_J(ρ, π)`. -/
theorem IsTypeContraction.heckeMean_injective (h : IsTypeContraction J U M Ubar ζ)
    (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G))
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    (ρ : Representation ℂ J W) [FiniteDimensional ℂ W] (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hfin : ∀ F, Finite (orbit (Representation.linHom ρ (π.comp J.subtype)) F))
    (hsupp : ∀ y ∈ U, ζ * y * ζ⁻¹ ∈ J → y ∈ representationSelfIntertwining ρ → y ∈ J)
    {Θ : W →ₗ[ℂ] W} (hΘ : IsIntertwinerAt ρ ζ Θ) (hΘ0 : Θ ≠ 0)
    (k : ℕ) (Φ : ρ.IntertwiningMap (π.comp J.subtype))
    (h0 : orbitMean (Representation.linHom ρ (π.comp J.subtype))
      (π (ζ ^ k) ∘ₗ Φ.toLinearMap ∘ₗ Θ ^ k) = 0) : Φ = 0 := by
  refine h.heckeMean_pow_eq_zero π ρ hfin hΘ ?_ k Φ h0
  intro F hF hT
  by_contra hF0
  let Φ' := intertwiningOfEquivariant π ρ F hF
  have hΦ'0 : Φ' ≠ 0 := fun h' => hF0 (congrArg Representation.IntertwiningMap.toLinearMap h')
  have hinj : Function.Injective Φ' :=
    (Representation.IsIrreducible.injective_or_eq_zero Φ').resolve_right hΦ'0
  obtain ⟨ψ, hψ, hψΦ⟩ := exists_equivariant_retraction hJo hJc π hπ ρ hρ Φ' hinj
  have hfac : ∀ j ∈ J, ∃ u ∈ J ⊓ U, ∃ d ∈ J, ζ⁻¹ * d * ζ ∈ J ∧ j = u * d := by
    intro j hj
    obtain ⟨u, hu, d, hd, hdζ, hjd⟩ := h.factor_stab 1 hj
    exact ⟨u, hu, d, hd, by simpa using hdζ, hjd⟩
  have := hfin (π ζ ∘ₗ Φ'.toLinearMap ∘ₗ hΘ.toSpace.toLinearMap)
  have hzero := eq_zero_of_heckeMean_eq_zero π ρ Φ' ψ hψ hψΦ ζ hΘ.toSpace hfac
    h.upperNorm hsupp hT
  exact hΘ0 (congrArg Representation.IntertwiningMap.toLinearMap hzero)

/-- **Hecke injectivity for a translated power.** With the hypotheses of
`IsTypeContraction.heckeMean_injective`, let `m ∈ J` commute with `ζ` and put
`ζ' = m ζ^e`. For every `r` there is `Θ' ∈ I_{ζ'^r}(ρ)` whose Hecke mean is injective on
`Hom_J(ρ, π)`. -/
theorem IsTypeContraction.heckeMean_injective_translate (h : IsTypeContraction J U M Ubar ζ)
    (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G))
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    (ρ : Representation ℂ J W) [FiniteDimensional ℂ W] (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hfin : ∀ F, Finite (orbit (Representation.linHom ρ (π.comp J.subtype)) F))
    (hsupp : ∀ y ∈ U, ζ * y * ζ⁻¹ ∈ J → y ∈ representationSelfIntertwining ρ → y ∈ J)
    {Θ : W →ₗ[ℂ] W} (hΘ : IsIntertwinerAt ρ ζ Θ) (hΘ0 : Θ ≠ 0)
    (m : J) (hm : Commute (m : G) ζ) (e r : ℕ) :
    ∃ Θ' : intertwiningSpace ρ ρ (((m : G) * ζ ^ e) ^ r),
      ∀ Φ : ρ.IntertwiningMap (π.comp J.subtype),
        orbitMean (Representation.linHom ρ (π.comp J.subtype))
          (π (((m : G) * ζ ^ e) ^ r) ∘ₗ Φ.toLinearMap ∘ₗ Θ'.toLinearMap) = 0 → Φ = 0 := by
  have hpow : ((m : G) * ζ ^ e) ^ r = ((m ^ r : J) : G) * ζ ^ (e * r) := by
    rw [(hm.pow_right e).mul_pow, ← pow_mul]
    simp
  have hI : IsIntertwinerAt ρ (((m ^ r : J) : G) * ζ ^ (e * r))
      ((Θ ^ (e * r) : Module.End ℂ W) ∘ₗ ρ (m ^ r)⁻¹) :=
    (h.pow_intertwiner hΘ (e * r)).mul_left (m ^ r)
  rw [← hpow] at hI
  refine ⟨hI.toSpace, fun Φ h0 => ?_⟩
  change orbitMean _ (π (((m : G) * ζ ^ e) ^ r) ∘ₗ Φ.toLinearMap ∘ₗ
    ((Θ ^ (e * r) : Module.End ℂ W) ∘ₗ ρ (m ^ r)⁻¹)) = 0 at h0
  have hρm : ((Θ ^ (e * r) : Module.End ℂ W) ∘ₗ ρ (m ^ r)⁻¹) ∘ₗ ρ (m ^ r) = Θ ^ (e * r) := by
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp (ρ (m ^ r)⁻¹), ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_eq_id, LinearMap.comp_id]
  rw [hpow, heckeMean_mul_left, hρm] at h0
  exact h.heckeMean_injective hJo hJc π hπ ρ hρ hfin hsupp hΘ hΘ0 (e * r) Φ h0

end Package

end Langlands.BushnellKutzko.SplitTypeJacquet
