import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RepresentationTheory.Intertwining
import Langlands.Shimura.EquivariantForms

/-!
# Forms with trivial coefficients tensored with a coefficient module

Let `ι : Γ →* G` be a group homomorphism and `K` a subgroup of `G`. For trivial
representations `τ` of `K` on `R` and `σ` of `K` on `W`, the forms of `EquivariantForms` for
`τ` are the `R`-valued functions on `G` that are left invariant under `ι Γ` and right invariant
under `K`, and those for `σ` are the `W`-valued such functions. Multiplying values gives an
`R`-linear map `forms ι K τ ⊗[R] W → forms ι K σ`, which is an isomorphism when `W` is finite
free.

For `K' ≤ K` with `K'` normal in `K` and a representation `ρ` of `K` that is trivial on `K'`,
this map intertwines the tensor product of the level actions of `K` on the forms of level `K'`
with trivial coefficients and on the coefficients with the level action on the forms of level
`K'` for `ρ`. Combined with `levelInvariantsEquiv`, it identifies the `K`-invariants of the
tensor product with the forms of level `K` for `ρ`. This is a generic algebraic form of
Harris's isomorphism `𝒜_ℓ(GJ, 𝓛, K) ≅ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}` (Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, 1999, (3.8)); no group, level
or coefficient system of Harris is specialized here.

## Main definitions

* `tensorForms ι K τ σ`: the map `f ⊗ w ↦ (g ↦ f g • w)`.
* `tensorFormsEquiv ι K τ σ`: for finite free `W`, the inverse is
  `F ↦ ∑ i, (g ↦ b.coord i (F g)) ⊗ b i` for a basis `b` of `W`.
* `invariantsEquivOfEquiv e`: an equivalence of representations restricts to the invariants.
* `tensorLevelEquiv ι ρ hle`: `tensorFormsEquiv` at level `K'` as an equivalence between the
  tensor product of `levelAction ι (trivial R K R) hle` and `ρ`, and `levelAction ι ρ hle`.
* `tensorInvariantsEquiv ι ρ hle`: the `K`-invariants of that tensor product are the forms of
  level `K` for `ρ`.
* `tensorQuotientAction ι ρ hle` and `tensorQuotientInvariantsEquiv ι ρ hle`: the same with the
  tensor product action descended to `K ⧸ K'`.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open TensorProduct

universe t uR uΓ uG

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

section Tensor

variable (ι : Γ →* G) (K : Subgroup G) (τ : Representation R K R) [τ.IsTrivial]
  {W : Type t} [AddCommGroup W] [Module R W] (σ : Representation R K W) [σ.IsTrivial]

/-- The bilinear map `(f, w) ↦ (g ↦ f g • w)` from forms for the trivial representation `τ` on
`R` and `W` to forms for the trivial representation `σ` on `W`. -/
def tensorFormsBilin : forms ι K τ →ₗ[R] W →ₗ[R] forms ι K σ :=
  LinearMap.mk₂ R (fun f w => ⟨fun g => f.1 g • w, fun γ g => by simp [f.2.1 γ g], fun g k => by
      change f.1 (g * k) • w = σ k⁻¹ (f.1 g • w)
      rw [f.2.2 g k, Representation.isTrivial_apply, Representation.isTrivial_apply]⟩)
    (fun f₁ f₂ w => by ext g; simp [add_smul])
    (fun r f w => by ext g; simp [mul_smul])
    (fun f w₁ w₂ => by ext g; simp [smul_add])
    (fun r f w => by ext g; simp [smul_comm (f.1 g) r w])

/-- The `R`-linear map `forms ι K τ ⊗[R] W → forms ι K σ`, `f ⊗ w ↦ (g ↦ f g • w)`. -/
def tensorForms : forms ι K τ ⊗[R] W →ₗ[R] forms ι K σ :=
  TensorProduct.lift (tensorFormsBilin ι K τ σ)

@[simp]
lemma tensorForms_tmul_coe (f : forms ι K τ) (w : W) (g : G) :
    (tensorForms ι K τ σ (f ⊗ₜ w)).1 g = f.1 g • w :=
  rfl

/-- Composition with an `R`-linear form `c` on `W` sends forms for `σ` to forms for `τ`. -/
def coordForms (c : W →ₗ[R] R) : forms ι K σ →ₗ[R] forms ι K τ :=
  (c.compLeft G).restrict fun F hF => ⟨fun γ g => by simp [hF.1 γ g], fun g k => by
    simp only [LinearMap.compLeft_apply, Function.comp_apply]
    rw [hF.2 g k, Representation.isTrivial_apply, Representation.isTrivial_apply]⟩

@[simp]
lemma coordForms_apply_coe (c : W →ₗ[R] R) (F : forms ι K σ) (g : G) :
    (coordForms ι K τ σ c F).1 g = c (F.1 g) :=
  rfl

variable [Module.Free R W] [Module.Finite R W]

/-- For finite free `W`, `tensorForms` is an isomorphism. With `b` Mathlib's chosen basis of
`W`, the inverse sends `F` to `∑ i, (g ↦ b.coord i (F g)) ⊗ b i`. -/
def tensorFormsEquiv : forms ι K τ ⊗[R] W ≃ₗ[R] forms ι K σ :=
  let b := Module.Free.chooseBasis R W
  LinearEquiv.ofLinearMap (tensorForms ι K τ σ)
    (∑ i, (TensorProduct.mk R (forms ι K τ) W).flip (b i) ∘ₗ coordForms ι K τ σ (b.coord i))
    (by
      ext F g
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Submodule.coe_sum,
        Finset.sum_apply, LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.id_apply,
        tensorForms_tmul_coe, coordForms_apply_coe, Module.Basis.coord_apply]
      exact b.sum_repr (F.1 g))
    (by
      refine TensorProduct.ext' fun f w => ?_
      have hc : ∀ i, coordForms ι K τ σ (b.coord i) (tensorForms ι K τ σ (f ⊗ₜ w)) =
          b.coord i w • f := fun i => by
        ext g
        simp [mul_comm]
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply, LinearMap.id_apply, hc, TensorProduct.smul_tmul,
        ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr])

@[simp]
lemma tensorFormsEquiv_apply (x : forms ι K τ ⊗[R] W) :
    tensorFormsEquiv ι K τ σ x = tensorForms ι K τ σ x :=
  rfl

end Tensor

section Invariants

variable {H : Type*} [Group H] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W]
  [Module R W] {σ₁ : Representation R H V} {σ₂ : Representation R H W}

/-- An equivalence of representations restricts to an `R`-linear equivalence of invariants. -/
def invariantsEquivOfEquiv (e : σ₁.Equiv σ₂) : σ₁.invariants ≃ₗ[R] σ₂.invariants where
  toFun x := ⟨e x.1, fun h => by
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap h x.1
    rw [x.2 h] at this
    exact this.symm⟩
  invFun y := ⟨e.symm y.1, fun h => by
    have := Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap h y.1
    rw [y.2 h] at this
    exact this.symm⟩
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul e r x.1)
  left_inv x := Subtype.ext (e.toLinearEquiv.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.toLinearEquiv.apply_symm_apply y.1)

@[simp]
lemma invariantsEquivOfEquiv_apply_coe (e : σ₁.Equiv σ₂) (x : σ₁.invariants) :
    (invariantsEquivOfEquiv e x).1 = e x.1 :=
  rfl

/-- The invariants of a representation descended to a quotient group are those of the original
representation. -/
lemma invariants_ofQuotient (σ : Representation R H V) (S : Subgroup H) [S.Normal]
    [Representation.IsTrivial (σ.comp S.subtype)] : (σ.ofQuotient S).invariants = σ.invariants := by
  ext x
  refine ⟨fun hx h => hx (h : H ⧸ S), fun hx q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H h => exact hx h

end Invariants

section Level

/-- The restriction of the trivial representation is trivial. This instance is local: it is
used to form the forms of a smaller level with trivial coefficients. -/
local instance isTrivial_trivial_comp {H H' : Type*} [Group H] [Group H'] (f : H →* H') :
    Representation.IsTrivial ((Representation.trivial R H' R).comp f) where
  out h := Representation.isTrivial_def (Representation.trivial R H' R) (f h)

variable (ι : Γ →* G) {K K' : Subgroup G} {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) (hle : K' ≤ K) [(K'.subgroupOf K).Normal]
  [Representation.IsTrivial (ρ.comp (Subgroup.inclusion hle))]

/-- `tensorForms` at level `K'` intertwines the tensor product of the level actions of `K` on
the forms with trivial coefficients and on `V` with the level action on the forms for `ρ`:
`ρ k (f (g * k) • v) = f (g * k) • ρ k v`. -/
lemma tensorForms_levelAction (k : K) :
    tensorForms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle))
        (ρ.comp (Subgroup.inclusion hle)) ∘ₗ
        ((levelAction ι (Representation.trivial R K R) hle).tprod ρ) k =
      levelAction ι ρ hle k ∘ₗ
        tensorForms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle))
          (ρ.comp (Subgroup.inclusion hle)) := by
  refine TensorProduct.ext' fun f v => ?_
  ext g
  simp [Representation.tprod_apply]

/-- The tensor product action is trivial on `K'`. -/
instance : Representation.IsTrivial
    (((levelAction ι (Representation.trivial R K R) hle).tprod ρ).comp
      (K'.subgroupOf K).subtype) where
  out k := by
    have hk : (k : K).1 ∈ K' := Subgroup.mem_subgroupOf.1 k.2
    have h₁ := Representation.isTrivial_def
      ((levelAction ι (Representation.trivial R K R) hle).comp (K'.subgroupOf K).subtype) k
    have h₂ : ρ ((K'.subgroupOf K).subtype k) = LinearMap.id :=
      Representation.isTrivial_def (ρ.comp (Subgroup.inclusion hle)) ⟨_, hk⟩
    change TensorProduct.map _ _ = _
    rw [MonoidHom.comp_apply] at h₁
    rw [h₁, h₂, TensorProduct.map_id]

/-- The tensor product action descended to `K ⧸ K'`. -/
def tensorQuotientAction :
    Representation R (K ⧸ K'.subgroupOf K)
      (forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V) :=
  ((levelAction ι (Representation.trivial R K R) hle).tprod ρ).ofQuotient (K'.subgroupOf K)

/-- The `K ⧸ K'`-invariants of `tensorQuotientAction` are the `K`-invariants of the tensor
product action. -/
lemma tensorQuotientAction_invariants :
    Representation.invariants (k := R) (G := K ⧸ K'.subgroupOf K) (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
        (tensorQuotientAction ι ρ hle) =
      Representation.invariants (k := R) (G := K) (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
        ((levelAction ι (Representation.trivial R K R) hle).tprod ρ) :=
  invariants_ofQuotient _ _

variable [Module.Free R V] [Module.Finite R V]

/-- For finite free `V`, `tensorFormsEquiv` at level `K'` as an equivalence of representations
of `K` between the tensor product of `levelAction ι (trivial R K R) hle` and `ρ`, and
`levelAction ι ρ hle`. -/
def tensorLevelEquiv :
    ((levelAction ι (Representation.trivial R K R) hle).tprod ρ).Equiv (levelAction ι ρ hle) :=
  Representation.Equiv.mk
    (tensorFormsEquiv ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle))
      (ρ.comp (Subgroup.inclusion hle)))
    (tensorForms_levelAction ι ρ hle)

/-- For finite free `V`, the `K`-invariants of the tensor product of the forms of level `K'`
with trivial coefficients and `V` are the forms of level `K` for `ρ`: `tensorLevelEquiv` on
invariants followed by `levelInvariantsEquiv`. -/
def tensorInvariantsEquiv :
    Representation.invariants (k := R) (G := K)
        (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
        ((levelAction ι (Representation.trivial R K R) hle).tprod ρ) ≃ₗ[R]
      forms ι K ρ :=
  (invariantsEquivOfEquiv (tensorLevelEquiv ι ρ hle)).trans (levelInvariantsEquiv ι ρ hle)

@[simp]
lemma tensorInvariantsEquiv_apply_coe
    (x : Representation.invariants (k := R) (G := K)
      (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
      ((levelAction ι (Representation.trivial R K R) hle).tprod ρ)) :
    (tensorInvariantsEquiv ι ρ hle x).1 =
      (tensorForms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle))
        (ρ.comp (Subgroup.inclusion hle)) x.1).1 :=
  rfl

/-- For finite free `V`, the `K ⧸ K'`-invariants of the tensor product are the forms of
level `K` for `ρ`. -/
def tensorQuotientInvariantsEquiv :
    Representation.invariants (k := R) (G := K ⧸ K'.subgroupOf K)
        (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
        (tensorQuotientAction ι ρ hle) ≃ₗ[R]
      forms ι K ρ :=
  (LinearEquiv.ofEq _ _ (tensorQuotientAction_invariants ι ρ hle)).trans
    (tensorInvariantsEquiv ι ρ hle)

@[simp]
lemma tensorQuotientInvariantsEquiv_apply_coe
    (x : Representation.invariants (k := R) (G := K ⧸ K'.subgroupOf K)
      (V := forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V)
      (tensorQuotientAction ι ρ hle)) :
    (tensorQuotientInvariantsEquiv ι ρ hle x).1 =
      (tensorForms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle))
        (ρ.comp (Subgroup.inclusion hle)) x.1).1 :=
  rfl

end Level

end Langlands.Shimura.EquivariantForms
