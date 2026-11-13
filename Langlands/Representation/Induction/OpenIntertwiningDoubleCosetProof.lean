import Langlands.Representation.Induction.OpenIntertwiningStatement
import Mathlib.Tactic.Group

/-!
# Double-coset parametrization of compact-induction intertwining kernels: proof

For a compact open subgroup `H` of a topological group `G`, a smooth representation `σ`
of `H` and any representation `τ` of `H`, restriction to a system of double-coset
representatives `s` is a bijection from intertwining kernels to local intertwiner
families (Vignéras 1996, I.8.5 with `K = H`). This file proves
`CompactInductionDoubleCosetStatement`.

The finiteness inputs are:

* `finite_range_quotientMap_mul`: for compact open `H`, the double coset `H x H` meets
  only finitely many right cosets `H g` (its image in the discrete space `H \ G` is the
  compact image of `H`);
* `finite_range_apply_of_isSmooth`: for smooth `σ` and compact `H`, every orbit
  `σ(H) v` is finite.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV uW

section Finiteness

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a compact open subgroup `H`, the right cosets `H (x b)` with `b ∈ H` (the right
cosets contained in the double coset `H x H`) form a finite set. -/
theorem finite_range_quotientMap_mul {H : Subgroup G} (hHo : IsOpen (H : Set G))
    (hHc : IsCompact (H : Set G)) (x : G) :
    (Set.range fun b : H => quotientMap H (x * (b : G))).Finite := by
  have := discreteTopology_leftQuotient H hHo
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  apply IsCompact.finite_of_discrete
  apply isCompact_range
  exact continuous_quotient_mk'.comp (continuous_const.mul continuous_subtype_val)

/-- For a smooth representation `σ` of a compact subgroup `H`, every orbit `σ(H) v` is
finite: an open subgroup of `H` fixes `v` and has finite index. -/
theorem finite_range_apply_of_isSmooth {R : Type uR} {V : Type uV} [CommRing R]
    [AddCommGroup V] [Module R V] {H : Subgroup G} (hHc : IsCompact (H : Set G))
    {σ : Representation R H V} (hσ : IsSmooth σ) (v : V) :
    (Set.range fun b : H => σ b v).Finite := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  obtain ⟨K, hK⟩ := hσ v
  have hfix : ∀ k : H, k ∈ K.toSubgroup → σ k v = v := fun k hk =>
    (Representation.mem_invariants _ v).mp hK ⟨k, hk⟩
  let f : H ⧸ K.toSubgroup → V :=
    Quotient.lift (s := QuotientGroup.leftRel K.toSubgroup) (fun b => σ b v) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ K.toSubgroup := QuotientGroup.leftRel_apply.mp hab
      have hb : b = a * (a⁻¹ * b) := by group
      show σ a v = σ b v
      rw [hb, map_mul, Module.End.mul_apply, hfix _ hab'])
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨(b : H ⧸ K.toSubgroup), rfl⟩

end Finiteness

section Kernels

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W]
  [Module R W]

/-- A covariant function `Φ` satisfies, at every point `x`, the local intertwining identity
for the elements `h ∈ H` with `x h x⁻¹ ∈ H`. -/
theorem comp_eq_comp_of_covariant {H : Subgroup G} {σ : Representation R H V}
    {τ : Representation R H W} {Φ : G → V →ₗ[R] W}
    (hcov : ∀ (h h' : H) (g : G), Φ ((h : G) * g * (h' : G)) = τ h ∘ₗ Φ g ∘ₗ σ h')
    (x : G) (h : H) (hx : x * (h : G) * x⁻¹ ∈ H) :
    Φ x ∘ₗ σ h = τ ⟨x * (h : G) * x⁻¹, hx⟩ ∘ₗ Φ x := by
  have h1 := hcov 1 h x
  have h2 := hcov ⟨x * (h : G) * x⁻¹, hx⟩ 1 x
  have he : ((1 : H) : G) * x * (h : G) =
      ((⟨x * (h : G) * x⁻¹, hx⟩ : H) : G) * x * ((1 : H) : G) := by
    simp [mul_assoc]
  rw [he, h2] at h1
  ext v
  have h3 := LinearMap.congr_fun h1 v
  simpa using h3.symm

/-- If `ψ` satisfies the local intertwining identity at `x`, then
`τ a ∘ ψ ∘ σ b` depends only on the product `a x b`. -/
theorem comp_comp_eq_of_mul_eq {H : Subgroup G} {σ : Representation R H V}
    {τ : Representation R H W} {x : G} {ψ : V →ₗ[R] W}
    (hψ : ∀ (h : H) (hx : x * (h : G) * x⁻¹ ∈ H),
      ψ ∘ₗ σ h = τ ⟨x * (h : G) * x⁻¹, hx⟩ ∘ₗ ψ)
    {a₁ b₁ a₂ b₂ : H} (he : (a₁ : G) * x * b₁ = a₂ * x * b₂) :
    τ a₁ ∘ₗ ψ ∘ₗ σ b₁ = τ a₂ ∘ₗ ψ ∘ₗ σ b₂ := by
  have hk : x * ((b₂ * b₁⁻¹ : H) : G) * x⁻¹ = ((a₂⁻¹ * a₁ : H) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * ((b₂ : G) * (b₁ : G)⁻¹) * x⁻¹
        = (a₂ : G)⁻¹ * ((a₂ : G) * x * b₂) * (b₁ : G)⁻¹ * x⁻¹ := by group
      _ = (a₂ : G)⁻¹ * ((a₁ : G) * x * b₁) * (b₁ : G)⁻¹ * x⁻¹ := by rw [he]
      _ = (a₂ : G)⁻¹ * a₁ := by group
  have hx : x * ((b₂ * b₁⁻¹ : H) : G) * x⁻¹ ∈ H := hk ▸ (a₂⁻¹ * a₁).2
  have hloc := hψ (b₂ * b₁⁻¹) hx
  have hc : (⟨x * ((b₂ * b₁⁻¹ : H) : G) * x⁻¹, hx⟩ : H) = a₂⁻¹ * a₁ := Subtype.ext hk
  rw [hc] at hloc
  have hb : b₂ = (b₂ * b₁⁻¹) * b₁ := by group
  ext v
  have h3 := LinearMap.congr_fun hloc (σ b₁ v)
  simp only [LinearMap.comp_apply] at h3 ⊢
  rw [hb, map_mul, Module.End.mul_apply, h3, ← Module.End.mul_apply (τ a₂), ← map_mul,
    mul_inv_cancel_left]

end Kernels

/-- **Double-coset parametrization of intertwining kernels** (Vignéras 1996, I.8.5 with
`K = H`). For a compact open subgroup `H`, a smooth `σ`, any `τ` and a choice `s` of
double-coset representatives, `Φ ↦ (q ↦ Φ (s q))` sends intertwining kernels to local
intertwiner families, and every local intertwiner family is the restriction of exactly
one intertwining kernel. -/
theorem compactInductionDoubleCoset : CompactInductionDoubleCosetStatement.{uR, uG, uV, uW} := by
  intro R _ G _ _ _ H hHo hHc V W _ _ _ _ σ τ hσ s hs
  -- `q ↦ H (s q)` is injective.
  have hinj : ∀ q q', quotientMap H (s q) = quotientMap H (s q') → q = q' := by
    intro q q' hqq
    rw [quotientMap_eq_iff] at hqq
    rw [← hs q, ← hs q', DoubleCoset.eq]
    exact ⟨s q' * (s q)⁻¹, hqq, 1, H.one_mem, by group⟩
  refine ⟨fun Φ hΦ => ?_, fun φ hφ => ?_⟩
  · -- Restriction of an intertwining kernel.
    obtain ⟨hcov, hfin⟩ := hΦ
    refine ⟨fun q h hq => comp_eq_comp_of_covariant hcov (s q) h hq, fun v => ?_⟩
    apply Set.Finite.of_finite_image (f := fun q => quotientMap H (s q))
    · apply (hfin v).subset
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨s q, hq, rfl⟩
    · intro q _ q' _ h
      exact hinj q q' h
  · -- Extension of a local intertwiner family.
    obtain ⟨hloc, hfinφ⟩ := hφ
    have hdec : ∀ g : G, ∃ a b : H, g = (a : G) * s (DoubleCoset.mk H H g) * b := by
      intro g
      obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.eq.mp (hs (DoubleCoset.mk H H g))
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
    choose a b hab using hdec
    let Φ : G → V →ₗ[R] W := fun g => τ (a g) ∘ₗ φ (DoubleCoset.mk H H g) ∘ₗ σ (b g)
    have hΦ : ∀ (q : DoubleCoset.Quotient (H : Set G) (H : Set G)) (a' b' : H) (g : G),
        g = (a' : G) * s q * b' → Φ g = τ a' ∘ₗ φ q ∘ₗ σ b' := by
      intro q a' b' g hg
      have hq : DoubleCoset.mk H H g = q := by
        rw [hg, DoubleCoset.mk_mul_mem, DoubleCoset.mk_mem_mul, hs]
      have h1 := hab g
      show τ (a g) ∘ₗ φ (DoubleCoset.mk H H g) ∘ₗ σ (b g) = _
      rw [hq] at h1 ⊢
      exact comp_comp_eq_of_mul_eq (hloc q) (h1.symm.trans hg)
    have hΦs : ∀ q, Φ (s q) = φ q := by
      intro q
      rw [hΦ q 1 1 (s q) (by simp)]
      ext v
      simp
    have hcov : ∀ (h h' : H) (g : G),
        Φ ((h : G) * g * (h' : G)) = τ h ∘ₗ Φ g ∘ₗ σ h' := by
      intro h h' g
      have e : (h : G) * g * h' =
          ((h * a g : H) : G) * s (DoubleCoset.mk H H g) * ((b g * h' : H) : G) := by
        calc (h : G) * g * h'
            = h * ((a g : G) * s (DoubleCoset.mk H H g) * b g) * h' := by rw [← hab g]
          _ = _ := by simp only [Subgroup.coe_mul, mul_assoc]
      rw [hΦ _ _ _ _ e]
      ext v
      simp [Φ, map_mul]
    have hfinΦ : ∀ v : V, (quotientSupport H (fun g => Φ g v)).Finite := by
      intro v
      have hS : (⋃ w ∈ Set.range (fun c : H => σ c v), {q | φ q w ≠ 0}).Finite :=
        (finite_range_apply_of_isSmooth hHc hσ v).biUnion fun w _ => hfinφ w
      refine (hS.biUnion fun q _ => finite_range_quotientMap_mul hHo hHc (s q)).subset ?_
      rintro _ ⟨g, hg, rfl⟩
      have hg' : τ (a g) (φ (DoubleCoset.mk H H g) (σ (b g) v)) ≠ 0 := hg
      have hne : φ (DoubleCoset.mk H H g) (σ (b g) v) ≠ 0 := fun h0 =>
        hg' (by rw [h0, map_zero])
      have heq : quotientMap H (s (DoubleCoset.mk H H g) * (b g : G)) = quotientMap H g := by
        rw [quotientMap_eq_iff]
        have e : g * (s (DoubleCoset.mk H H g) * (b g : G))⁻¹ = a g := by
          calc g * (s (DoubleCoset.mk H H g) * (b g : G))⁻¹
              = ((a g : G) * s (DoubleCoset.mk H H g) * b g) *
                  (s (DoubleCoset.mk H H g) * (b g : G))⁻¹ := by rw [← hab g]
            _ = a g := by group
        rw [e]
        exact (a g).2
      exact Set.mem_biUnion (Set.mem_biUnion ⟨b g, rfl⟩ hne) ⟨b g, heq⟩
    refine ⟨Φ, ⟨⟨hcov, hfinΦ⟩, hΦs⟩, ?_⟩
    intro Ψ hΨ
    obtain ⟨⟨hΨcov, -⟩, hΨs⟩ := hΨ
    funext g
    have h1 := hΨcov (a g) (b g) (s (DoubleCoset.mk H H g))
    rw [← hab g, hΨs] at h1
    exact h1

end Langlands.Induction
