import Langlands.Representation.Induction.OpenIntertwiningStatement

/-! # The finite-type support criterion for compact-induction intertwining kernels: proof

Vignéras 1996, I.8.5 a), for `K = H` compact open and `σ` finitely generated over
`R[H]`. If `Φ` is an intertwining kernel, a nonzero value `Φ g` is nonzero at some
translate `σ h v_i` of a generator, so `g h` lies in the right-coset support of
`x ↦ Φ x v_i`; the double cosets of the support of `Φ` are therefore images of the
finitely many right cosets in these supports. Conversely, the support of `Φ` lies in
finitely many double cosets `H g H`; their union is compact, so its image in the
discrete space `H \ G` is finite.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV uW

section DoubleCosetLift

variable {G : Type uG} [Group G]

/-- The double coset `H g H` depends only on the right coset `H g`: the induced map
`H \ G → H \ G / H`. -/
def leftQuotientToDoubleCoset (H : Subgroup G) :
    LeftQuotient H → DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  Quotient.lift (DoubleCoset.mk H H) (by
    intro a b hab
    have hba : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    calc DoubleCoset.mk H H a = DoubleCoset.mk H H (((⟨b * a⁻¹, hba⟩ : H) : G) * a) :=
          (DoubleCoset.mk_mem_mul _ _).symm
      _ = DoubleCoset.mk H H b := by simp)

theorem leftQuotientToDoubleCoset_quotientMap (H : Subgroup G) (g : G) :
    leftQuotientToDoubleCoset H (quotientMap H g) = DoubleCoset.mk H H g :=
  rfl

end DoubleCosetLift

section Generation

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] {H : Subgroup G}
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An `R`-linear map that vanishes on every translate `σ h s` of a generating set `S` of
`σ.asModule` over `R[H]` is zero. -/
theorem eq_zero_of_forall_translate_generators (σ : Representation R H V)
    (S : Set σ.asModule) (hS : Submodule.span (MonoidAlgebra R H) S = ⊤)
    (f : V →ₗ[R] W) (hf : ∀ s ∈ S, ∀ h : H, f (σ h (σ.asModuleEquiv s)) = 0) : f = 0 := by
  have key : ∀ x : σ.asModule, ∀ h : H, f (σ h (σ.asModuleEquiv x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span (MonoidAlgebra R H) S := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact hf x hx
    | zero => intro h; simp
    | add x y _ _ hx hy => intro h; simp [map_add, hx h, hy h]
    | smul a x _ hx =>
      intro h
      rw [Representation.asModuleEquiv_map_smul]
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | single h' r =>
        rw [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, map_smul]
        have hmul : σ h (σ h' (σ.asModuleEquiv x)) = σ (h * h') (σ.asModuleEquiv x) := by
          rw [map_mul, Module.End.mul_apply]
        rw [hmul, hx (h * h'), smul_zero]
  ext v
  simpa using key (σ.asModuleEquiv.symm v) 1

/-- Forward direction: the support of an intertwining kernel of a finitely generated
representation meets only finitely many double cosets `H g H`. -/
theorem finite_doubleCoset_support_of_isIntertwiningKernel
    [TopologicalSpace G] [IsTopologicalGroup G]
    (σ : Representation R H V) (τ : Representation R H W)
    (hσ : Module.Finite (MonoidAlgebra R H) σ.asModule) (Φ : G → V →ₗ[R] W)
    (hΦ : IsIntertwiningKernel H σ τ Φ) :
    (DoubleCoset.mk H H '' Function.support Φ).Finite := by
  obtain ⟨S, hS⟩ := hσ.fg_top
  refine Set.Finite.subset (S.finite_toSet.biUnion fun s _ =>
    (hΦ.2 (σ.asModuleEquiv s)).image (leftQuotientToDoubleCoset H)) ?_
  rintro _ ⟨g, hg, rfl⟩
  have hex : ∃ s ∈ (S : Set σ.asModule), ∃ h : H, Φ g (σ h (σ.asModuleEquiv s)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (eq_zero_of_forall_translate_generators σ S hS (Φ g) hcon)
  obtain ⟨s, hs, h, hne⟩ := hex
  refine Set.mem_biUnion hs ⟨quotientMap H (g * h), ⟨g * h, ?_, rfl⟩, ?_⟩
  · have hcov := LinearMap.congr_fun (hΦ.1 1 h g) (σ.asModuleEquiv s)
    simp only [OneMemClass.coe_one, one_mul, map_one, LinearMap.comp_apply,
      Module.End.one_apply] at hcov
    change Φ (g * h) (σ.asModuleEquiv s) ≠ 0
    rw [hcov]
    exact hne
  · rw [leftQuotientToDoubleCoset_quotientMap]
    exact DoubleCoset.mk_mul_mem h g

/-- Reverse direction: if the support of `Φ` meets only finitely many double cosets of a
compact open subgroup `H`, then for every vector `v` only finitely many right cosets `H g`
have `Φ g v ≠ 0`. -/
theorem finite_quotientSupport_of_finite_doubleCoset_support
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) (Φ : G → V →ₗ[R] W)
    (hfin : (DoubleCoset.mk H H '' Function.support Φ).Finite) (v : V) :
    (quotientSupport H (fun g => Φ g v)).Finite := by
  have := discreteTopology_leftQuotient H hHo
  have hC : IsCompact (⋃ q ∈ DoubleCoset.mk H H '' Function.support Φ,
      DoubleCoset.quotToDoubleCoset H H q) :=
    hfin.isCompact_biUnion fun q _ => (hHc.mul isCompact_singleton).mul hHc
  have hcont : Continuous (quotientMap H) := continuous_quot_mk
  refine ((hC.image hcont).finite_of_discrete).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  have hg' : g ∈ Function.support Φ := fun h0 => hg (by simp [h0])
  exact Set.mem_biUnion ⟨g, hg', rfl⟩ ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).mpr rfl)

end Generation

/-- **Vignéras I.8.5 a) for `K = H`.** For a compact open subgroup `H` and a representation
`σ` finitely generated over `R[H]`, a function `Φ : G → Hom_R(V, W)` is an intertwining
kernel exactly when it has the covariance `Φ (h g h') = τ h ∘ Φ g ∘ σ h'` and its support
meets only finitely many double cosets `H g H`. -/
theorem compactInductionFiniteTypeKernel :
    CompactInductionFiniteTypeKernelStatement.{uR, uG, uV, uW} := by
  intro R _ G _ _ _ H hHo hHc V W _ _ _ _ σ τ hσ Φ
  constructor
  · intro hΦ
    exact ⟨hΦ.1, finite_doubleCoset_support_of_isIntertwiningKernel σ τ hσ Φ hΦ⟩
  · rintro ⟨hcov, hfin⟩
    exact ⟨hcov, finite_quotientSupport_of_finite_doubleCoset_support hHo hHc Φ hfin⟩

end Langlands.Induction
