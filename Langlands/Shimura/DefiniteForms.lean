import Langlands.Shimura.Coefficients.Algebraic
import Langlands.Shimura.EquivariantFormsTwist

/-!
# Harris's spaces of automorphic forms on the similitude group of an algebra with involution

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra `A`, with rational similitude group
`σ.similitudes` and finite adelic points `σ.FiniteAdelicPoints`, and let `ρ` be an algebraic
representation of the scalar extension of the similitude group to a field `L` on an `L`-vector
space `W`. This file specializes the generic modules `forms` and `twistedForms` of
`Langlands.Shimura.EquivariantForms` to the spaces of Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, 1999, §3, (3.2), (3.3) and (3.5), for the group of
`σ` (Harris's `GJ`), embedded diagonally by `σ.finiteAdelicDiagonal`.

## Main definitions

* `rationalRep σ ρ S`: the action `γ ↦ ρ(γ)` of the rational points on `W(S) = S ⊗_L W`, for an
  `L`-algebra `S`.
* `finiteForms σ ρ S K`: Harris's `𝒜_f(GJ, ρ, K)(S)` (3.2), the functions
  `f : GJ(𝔸_f) → W(S)` with `f (γ g) = ρ(γ) (f g)` for rational `γ` and `f (g k) = f g` for
  `k ∈ K`; `finiteTranslate` and `finiteFormsPresheaf` make it a presheaf on compact open
  levels by right translation.
* `ellAdicRep σ ρ ℓ φ`: for a finite place `ℓ` of `ℚ` and a `ℚ`-algebra map
  `φ : ℚ_ℓ → S` to an `L`-algebra `S` (the data of an `L ⊗ ℚ_ℓ`-algebra), the action
  `g ↦ ρ(g_ℓ)` of `GJ(𝔸_f)` on `W(S)` through the `ℓ`-component.
* `ellAdicForms σ ρ ℓ φ K`: Harris's `𝒜_ℓ(GJ, ρ, K)(S)` (3.3), the functions
  `f : GJ(𝔸_f) → W(S)` with `f (γ g) = f g` for rational `γ` and `f (g k) = ρ(k_ℓ)⁻¹ (f g)`.
* `resEll σ ρ ℓ φ K`: Harris's isomorphism `res_ℓ : 𝒜_ℓ ≅ 𝒜_f` (3.5),
  `f ↦ (g ↦ ρ(g_ℓ) (f g))`; `resEllIso` makes it natural in the level, for the transport
  `f ↦ (x ↦ ρ(a_ℓ) (f (x a)))` on `𝒜_ℓ` and right translation on `𝒜_f`.
-/

noncomputable section

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory Langlands.Global Langlands.Shimura.EquivariantForms
open scoped TensorProduct

universe u v w uS

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)
variable {L : Type u} [Field L] [Algebra ℚ L] {W : Type w} [AddCommGroup W] [Module L W]
variable (ρ : (σ.baseChange L).AlgebraicRepresentation W)

section Rational

variable (S : Type uS) [CommRing S] [Algebra L S]

/-- The action `γ ↦ ρ(γ)` of the rational points of the similitude group on
`W(S) = S ⊗_L W`, for an `L`-algebra `S`: the scalar extension to `S` of the action
`ρ.rationalAction` of the `L`-points, along the diagonal map `σ.diagonalPoints L`. -/
def rationalRep : Representation S σ.similitudes (S ⊗[L] W) :=
  (Module.End.baseChangeHom L S W).toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.rationalAction.comp (σ.diagonalPoints L)))

lemma rationalRep_apply (γ : σ.similitudes) :
    rationalRep σ ρ S γ =
      ((ρ.rationalAction (σ.diagonalPoints L γ)).baseChange L S W W).toLinearMap :=
  rfl

/-- Harris's `𝒜_f(GJ, ρ, K)(S)` (1999, (3.2)) for an `L`-algebra `S` and a subgroup `K` of
the finite adelic points: the `S`-module of functions `f : GJ(𝔸_f) → W(S)` with
`f (γ g) = ρ(γ) (f g)` for rational `γ` and `f (g k) = f g` for `k ∈ K`. -/
def finiteForms (K : Subgroup σ.FiniteAdelicPoints) :
    Submodule S (σ.FiniteAdelicPoints → S ⊗[L] W) where
  carrier := {f | (∀ (γ : σ.similitudes) (g : σ.FiniteAdelicPoints),
      f (σ.finiteAdelicDiagonal γ * g) = rationalRep σ ρ S γ (f g)) ∧
    ∀ (g : σ.FiniteAdelicPoints) (k : K), f (g * k) = f g}
  add_mem' {f₁ f₂} hf₁ hf₂ := ⟨fun γ g => by simp [hf₁.1 γ g, hf₂.1 γ g],
    fun g k => by simp [hf₁.2 g k, hf₂.2 g k]⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => rfl⟩
  smul_mem' r f hf := ⟨fun γ g => by simp [hf.1 γ g], fun g k => by simp [hf.2 g k]⟩

variable {σ ρ S} in
lemma mem_finiteForms {K : Subgroup σ.FiniteAdelicPoints}
    {f : σ.FiniteAdelicPoints → S ⊗[L] W} :
    f ∈ finiteForms σ ρ S K ↔
      (∀ (γ : σ.similitudes) (g : σ.FiniteAdelicPoints),
        f (σ.finiteAdelicDiagonal γ * g) = rationalRep σ ρ S γ (f g)) ∧
      ∀ (g : σ.FiniteAdelicPoints) (k : K), f (g * k) = f g :=
  Iff.rfl

/-- Right translation `f ↦ (x ↦ f (x * g))` from level `K'` to level `K`, for `g` with
`g⁻¹ * k * g ∈ K'` for all `k ∈ K`. -/
def finiteTranslate {K K' : Subgroup σ.FiniteAdelicPoints} (g : σ.FiniteAdelicPoints)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ K') :
    finiteForms σ ρ S K' →ₗ[S] finiteForms σ ρ S K :=
  (LinearMap.funLeft S (S ⊗[L] W) (· * g)).restrict fun f hf =>
    ⟨fun γ x => by simp [mul_assoc, hf.1 γ (x * g)], fun x k => by
      have hx : x * k * g = x * g * ((⟨g⁻¹ * k * g, hg k k.2⟩ : K') : σ.FiniteAdelicPoints) := by
        simp [mul_assoc]
      change f (x * k * g) = f (x * g)
      rw [hx, hf.2]⟩

@[simp]
lemma finiteTranslate_apply_coe {K K' : Subgroup σ.FiniteAdelicPoints}
    (g : σ.FiniteAdelicPoints) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ K') (f : finiteForms σ ρ S K')
    (x : σ.FiniteAdelicPoints) :
    (finiteTranslate σ ρ S g hg f).1 x = f.1 (x * g) :=
  rfl

/-- The spaces `𝒜_f(GJ, ρ, K)(S)` of all compact open levels `K`, as a presheaf on the
category of levels with right translation `finiteTranslate` on arrows. -/
def finiteFormsPresheaf :
    (CompactOpenLevel σ.FiniteAdelicPoints)ᵒᵖ ⥤ ModuleCat.{max v uS w} S where
  obj K := ModuleCat.of S (finiteForms σ ρ S K.unop.subgroup)
  map a := ModuleCat.ofHom (finiteTranslate σ ρ S a.unop.element a.unop.respects)
  map_id K := by
    ext f x
    simp
  map_comp a b := by
    ext f x
    simp [mul_assoc]

@[simp]
lemma finiteFormsPresheaf_map_apply_coe {K K' : (CompactOpenLevel σ.FiniteAdelicPoints)ᵒᵖ}
    (a : K ⟶ K') (f : (finiteFormsPresheaf σ ρ S).obj K) (x : σ.FiniteAdelicPoints) :
    (((finiteFormsPresheaf σ ρ S).map a).hom f).1 x = f.1 (x * a.unop.element) :=
  rfl

end Rational

section Ell

variable [Module.Finite ℚ A] (ℓ : FinitePlace ℚ) {S : Type u} [CommRing S] [Algebra ℚ S]
  [Algebra L S] (φ : FiniteCompletion ℚ ℓ →ₐ[ℚ] S)

/-- The action `g ↦ ρ(g_ℓ)` of the finite adelic points on `W(S) = S ⊗_L W` through their
component at `ℓ`, for an `L`-algebra `S` with a `ℚ`-algebra map `φ : ℚ_ℓ → S`. -/
def ellAdicRep : Representation S σ.FiniteAdelicPoints (S ⊗[L] W) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.finiteAdelicVia ℓ φ)

lemma ellAdicRep_apply (g : σ.FiniteAdelicPoints) :
    ellAdicRep σ ρ ℓ φ g = (ρ.finiteAdelicVia ℓ φ g).toLinearMap :=
  rfl

/-- On rational points the `ℓ`-adic action is the rational action. -/
lemma ellAdicRep_diagonal (γ : σ.similitudes) :
    ellAdicRep σ ρ ℓ φ (σ.finiteAdelicDiagonal γ) = rationalRep σ ρ S γ := by
  rw [ellAdicRep_apply, rationalRep_apply, ρ.finiteAdelicVia_diagonal]

/-- Elements with trivial component at `ℓ` act trivially. -/
lemma ellAdicRep_eq_one {g : σ.FiniteAdelicPoints} (hg : σ.finiteLocalMap ℓ g = 1) :
    ellAdicRep σ ρ ℓ φ g = 1 := by
  rw [ellAdicRep_apply, AlgebraInvolution.AlgebraicRepresentation.finiteAdelicVia,
    MonoidHom.comp_apply]
  erw [hg]
  rw [map_one]
  rfl

/-- Harris's `𝒜_ℓ(GJ, ρ, K)(S)` (1999, (3.3)): the `S`-module of functions
`f : GJ(𝔸_f) → W(S)` with `f (γ g) = f g` for rational `γ` and `f (g k) = ρ(k_ℓ)⁻¹ (f g)`
for `k ∈ K`; the generic `forms` for `ellAdicRep` restricted to `K`. -/
abbrev ellAdicForms (K : Subgroup σ.FiniteAdelicPoints) :
    Submodule S (σ.FiniteAdelicPoints → S ⊗[L] W) :=
  forms σ.finiteAdelicDiagonal K ((ellAdicRep σ ρ ℓ φ).comp K.subtype)

lemma mem_ellAdicForms {K : Subgroup σ.FiniteAdelicPoints}
    {f : σ.FiniteAdelicPoints → S ⊗[L] W} :
    f ∈ ellAdicForms σ ρ ℓ φ K ↔
      (∀ (γ : σ.similitudes) (g : σ.FiniteAdelicPoints),
        f (σ.finiteAdelicDiagonal γ * g) = f g) ∧
      ∀ (g : σ.FiniteAdelicPoints) (k : K),
        f (g * k) = ρ.finiteAdelicVia ℓ φ (k : σ.FiniteAdelicPoints)⁻¹ (f g) :=
  Iff.rfl

/-- Elements of `K` with trivial `ℓ`-component act trivially on `𝒜_ℓ(GJ, ρ, K)(S)`. -/
lemma ellAdicForms_mul_of_local_eq_one {K : Subgroup σ.FiniteAdelicPoints}
    {f : σ.FiniteAdelicPoints → S ⊗[L] W} (hf : f ∈ ellAdicForms σ ρ ℓ φ K)
    (g : σ.FiniteAdelicPoints) (k : K) (hk : σ.finiteLocalMap ℓ k = 1) :
    f (g * k) = f g := by
  rw [hf.2 g k]
  have hk' : σ.finiteLocalMap ℓ ((k⁻¹ : K) : σ.FiniteAdelicPoints) = 1 := by
    rw [Subgroup.coe_inv, map_inv, hk, inv_one]
  change ellAdicRep σ ρ ℓ φ ((k⁻¹ : K) : σ.FiniteAdelicPoints) (f g) = f g
  rw [ellAdicRep_eq_one σ ρ ℓ φ hk']
  rfl

/-- The twisted forms for `ellAdicRep` are exactly `𝒜_f(GJ, ρ, K)(S)`. -/
lemma twistedForms_eq_finiteForms (K : Subgroup σ.FiniteAdelicPoints) :
    twistedForms σ.finiteAdelicDiagonal K (ellAdicRep σ ρ ℓ φ) = finiteForms σ ρ S K := by
  ext f
  rw [mem_twistedForms, mem_finiteForms]
  simp only [ellAdicRep_diagonal]

/-- Harris's isomorphism `res_ℓ : 𝒜_ℓ(GJ, ρ, K)(S) ≅ 𝒜_f(GJ, ρ, K)(S)` (1999, (3.5)),
`f ↦ (g ↦ ρ(g_ℓ) (f g))`: the generic `twistEquiv` for `ellAdicRep`. -/
def resEll (K : Subgroup σ.FiniteAdelicPoints) :
    ellAdicForms σ ρ ℓ φ K ≃ₗ[S] finiteForms σ ρ S K :=
  (twistEquiv σ.finiteAdelicDiagonal K (ellAdicRep σ ρ ℓ φ)).trans
    (LinearEquiv.ofEq _ _ (twistedForms_eq_finiteForms σ ρ ℓ φ K))

@[simp]
lemma resEll_apply_coe (K : Subgroup σ.FiniteAdelicPoints) (f : ellAdicForms σ ρ ℓ φ K)
    (g : σ.FiniteAdelicPoints) :
    (resEll σ ρ ℓ φ K f).1 g = ρ.finiteAdelicVia ℓ φ g (f.1 g) :=
  rfl

@[simp]
lemma resEll_symm_apply_coe (K : Subgroup σ.FiniteAdelicPoints) (f : finiteForms σ ρ S K)
    (g : σ.FiniteAdelicPoints) :
    ((resEll σ ρ ℓ φ K).symm f).1 g = ρ.finiteAdelicVia ℓ φ g⁻¹ (f.1 g) :=
  rfl

/-- Along a level arrow whose element has trivial `ℓ`-component, the generic transport of
`𝒜_ℓ` is plain right translation. -/
lemma levelTransport_of_local_eq_one
    {K K' : CompactOpenLevel σ.FiniteAdelicPoints} (a : K ⟶ K')
    (ha : σ.finiteLocalMap ℓ a.element = 1)
    (f : ellAdicForms σ ρ ℓ φ K'.subgroup) (x : σ.FiniteAdelicPoints) :
    (levelTransport S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) a f).1 x =
      f.1 (x * a.element) := by
  rw [levelTransport_apply_coe, ellAdicRep_eq_one σ ρ ℓ φ ha]
  rfl

/-- The isomorphisms `res_ℓ` of all compact open levels, as an isomorphism from the presheaf
`levelPresheaf` of `𝒜_ℓ` (with transport `f ↦ (x ↦ ρ(a_ℓ) (f (x a)))`) to the presheaf
`finiteFormsPresheaf` of `𝒜_f` (with right translation). -/
def resEllIso :
    levelPresheaf S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) ≅ finiteFormsPresheaf σ ρ S :=
  NatIso.ofComponents (fun K => (resEll σ ρ ℓ φ K.unop.subgroup).toModuleIso) fun a => by
    ext f : 2
    refine Subtype.ext (funext fun x => ?_)
    change ρ.finiteAdelicVia ℓ φ x
        (ellAdicRep σ ρ ℓ φ a.unop.element (f.1 (x * a.unop.element))) =
      ρ.finiteAdelicVia ℓ φ (x * a.unop.element) (f.1 (x * a.unop.element))
    rw [ellAdicRep_apply, map_mul, LinearEquiv.mul_apply]
    rfl

@[simp]
lemma resEllIso_hom_app_apply_coe (K : (CompactOpenLevel σ.FiniteAdelicPoints)ᵒᵖ)
    (f : ellAdicForms σ ρ ℓ φ K.unop.subgroup) (g : σ.FiniteAdelicPoints) :
    (((resEllIso σ ρ ℓ φ).hom.app K).hom f).1 g = ρ.finiteAdelicVia ℓ φ g (f.1 g) :=
  rfl

/-- Under `res_ℓ`, the Hecke operator `[K g K']` of `𝒜_ℓ` has the untwisted formula
`x ↦ ∑ f (x * k * g)`, summed over representatives `k` of `K ⧸ (K ∩ g K' g⁻¹)`. -/
lemma resEll_heckeOperator (K K' : CompactOpenLevel σ.FiniteAdelicPoints)
    (g : σ.FiniteAdelicPoints)
    [Fintype (K.subgroup ⧸ (CompactOpenLevel.heckeLevel K K' g).subgroup.subgroupOf K.subgroup)]
    (f : ellAdicForms σ ρ ℓ φ K'.subgroup) (x : σ.FiniteAdelicPoints) :
    (resEll σ ρ ℓ φ K.subgroup
        (heckeOperator S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) K K' g f)).1 x =
      ∑ q : K.subgroup ⧸ (CompactOpenLevel.heckeLevel K K' g).subgroup.subgroupOf K.subgroup,
        (resEll σ ρ ℓ φ K'.subgroup f).1 (x * q.out * g) :=
  twistEquiv_heckeOperator S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) K K' g f x

end Ell

section LocallyConstant

variable [Module.Finite ℚ A] (S : Type uS) [CommRing S] [Algebra L S]

/-- For an open subgroup `K`, every element of `𝒜_f(GJ, ρ, K)(S)` is locally constant: it is
constant on each open coset `g K`. -/
lemma finiteForms_isLocallyConstant {K : Subgroup σ.FiniteAdelicPoints}
    (hK : IsOpen (K : Set σ.FiniteAdelicPoints)) {f : σ.FiniteAdelicPoints → S ⊗[L] W}
    (hf : f ∈ finiteForms σ ρ S K) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : σ.FiniteAdelicPoints | x⁻¹ * y ∈ K} :=
    hK.preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp)] with y hy
  have := hf.2 x ⟨x⁻¹ * y, hy⟩
  simpa using this

end LocallyConstant

end Langlands.Shimura.DefiniteForms
