import Langlands.Theta.Heisenberg.Representation
import Mathlib.Analysis.Complex.Circle
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The metaplectic group of a model of the Heisenberg representation

GKT §2.1.2 (p. 48). Let `B` be a bilinear form on a module `W` over a commutative ring `R` with `2`
invertible, `ρ` a representation of `HeisenbergGroup B` on a complex vector space `S`, and let the
isometry group `Sp(W) = LinearMap.BilinForm.isometryGroup B` act on the Heisenberg group by
`g · (w, t) = (g w, t)` (GKT (2.1), `HeisenbergGroup.isometryAction`).

* `MetaplecticGroup ρ` is the group of pairs `(g, M) ∈ Sp(W) × GL(S)` with
  `M ∘ ρ(h) = ρ(g · h) ∘ M` for all `h` (GKT (2.2) and Lemma 2.1): the book's
  `Mp(W)^{ℂˣ}_{ψ,S}` when `ρ` is the Heisenberg representation with central character `ψ`.
* `MetaplecticGroup.proj ρ : MetaplecticGroup ρ →* Sp(W)`, `(g, M) ↦ g`, is the canonical
  projection, and `MetaplecticGroup.weil ρ`, `(g, M) ↦ M`, the Weil representation `ω_{ψ,S}`
  (GKT (2.3)); `weil_normalizes`: `ω_{ψ,S}` normalizes `ρ` along the projection.
* `MetaplecticGroup.scalar ρ : ℂˣ →* MetaplecticGroup ρ`, `z ↦ (1, z)`, lands in the centre.
* `MetaplecticGroup.unitary ρ inner`: the pairs whose operator preserves a sesquilinear form on
  `S` (GKT p. 49, `Mp(W)^{ℂ¹}_{ψ,S}` for the invariant Hermitian form), and
  `MetaplecticGroup.circle ρ inner : Circle →* unitary ρ inner`.
* `MetaplecticGroup.lift ρ ι ω h`: a representation `ω` of a group `G` normalizing `ρ` along a
  homomorphism `ι : G →* Sp(W)` is a homomorphism `G →* MetaplecticGroup ρ` over `ι`.
* `MetaplecticGroup.congr e`: an isomorphism of models `e : ρ ≃ ρ'` carries `(g, M)` to
  `(g, e M e⁻¹)` (GKT Proposition 6.8 (1); that the result does not depend on `e` is
  `MetaplecticGroup.congr_eq` of `Langlands.Theta.Metaplectic.Exact`, by Schur's lemma).
* `MetaplecticGroup.Splitting ρ ι`: a homomorphism `G →* MetaplecticGroup ρ` over `ι`; its Weil
  representation `ω_ψ ∘ s` (GKT Definition 13.15); every representation normalizing `ρ` is the Weil
  representation of a splitting (`Splitting.ofNormalizes`), and a splitting can be twisted by a
  character (`Splitting.twist`).

Nothing here needs a topology or a field: the exactness of
`1 → ℂˣ → MetaplecticGroup ρ → Sp(W) → 1` over a nonarchimedean local field is in
`Langlands.Theta.Metaplectic.Exact`.
-/

noncomputable section

namespace Langlands.Theta

open HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {W : Type v} [AddCommGroup W] [Module R W]
  {B : LinearMap.BilinForm R W} {S : Type w} [AddCommGroup S] [Module ℂ S]

/-- The relation (2.2) of GKT for a pair `(g, M)`: `M ∘ ρ(h) = ρ(g · h) ∘ M` for all `h`. -/
def IsMetaplecticPair (ρ : Representation ℂ (HeisenbergGroup B) S) (g : isometryGroup B)
    (M : S ≃ₗ[ℂ] S) : Prop :=
  ∀ h : HeisenbergGroup B, M.toLinearMap ∘ₗ ρ h = ρ (isometryAction B g h) ∘ₗ M.toLinearMap

/-- **The metaplectic group of a model** (GKT §2.1.2, Lemma 2.1, p. 48): the pairs `(g, M)` of an
isometry `g` of `(W, B)` and a linear automorphism `M` of the space of `ρ` with
`M ∘ ρ(h) = ρ(g · h) ∘ M` for all `h` in the Heisenberg group. For the Heisenberg representation
`ρ` with central character `ψ` this is `Mp(W)^{ℂˣ}_{ψ,S}`. -/
def MetaplecticGroup (ρ : Representation ℂ (HeisenbergGroup B) S) :
    Subgroup (isometryGroup B × (S ≃ₗ[ℂ] S)) where
  carrier := {x | IsMetaplecticPair ρ x.1 x.2}
  mul_mem' {x y} hx hy h := LinearMap.ext fun v => by
    have h1 := LinearMap.congr_fun (hy h) v
    have h2 := LinearMap.congr_fun (hx (isometryAction B y.1 h)) (y.2 v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1 h2 ⊢
    change x.2 (y.2 (ρ h v)) = ρ (isometryAction B (x.1 * y.1) h) (x.2 (y.2 v))
    rw [h1, h2, map_mul]
    rfl
  one_mem' h := LinearMap.ext fun v => by
    simp only [Prod.fst_one, Prod.snd_one, map_one, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rfl
  inv_mem' {x} hx h := LinearMap.ext fun v => by
    have key := LinearMap.congr_fun (hx (isometryAction B x.1⁻¹ h)) (x.2⁻¹ v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at key ⊢
    have e1 : isometryAction B x.1 (isometryAction B x.1⁻¹ h) = h := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have e2 : x.2 (x.2⁻¹ v) = v := by
      change (x.2 * x.2⁻¹) v = v
      rw [mul_inv_cancel]; rfl
    rw [e1, e2] at key
    change x.2⁻¹ (ρ h v) = ρ (isometryAction B x.1⁻¹ h) (x.2⁻¹ v)
    rw [← key]
    change (x.2⁻¹ * x.2) _ = _
    rw [inv_mul_cancel]; rfl

namespace MetaplecticGroup

variable (ρ : Representation ℂ (HeisenbergGroup B) S)

/-- Membership in the metaplectic group is the relation (2.2). -/
theorem mem_iff {x : isometryGroup B × (S ≃ₗ[ℂ] S)} :
    x ∈ MetaplecticGroup ρ ↔ IsMetaplecticPair ρ x.1 x.2 :=
  Iff.rfl

/-- The relation (2.2) on vectors. -/
theorem apply_apply (x : MetaplecticGroup ρ) (h : HeisenbergGroup B) (v : S) :
    x.1.2 (ρ h v) = ρ (isometryAction B x.1.1 h) (x.1.2 v) :=
  LinearMap.congr_fun (x.2 h) v

/-- Two elements are equal when their isometries and their operators are. -/
@[ext] theorem ext {x y : MetaplecticGroup ρ} (h1 : x.1.1 = y.1.1) (h2 : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

/-- **The canonical projection** `p : (g, M) ↦ g` (GKT (2.3), p. 48). -/
def proj : MetaplecticGroup ρ →* isometryGroup B :=
  (MonoidHom.fst _ _).comp (MetaplecticGroup ρ).subtype

@[simp] theorem proj_apply (x : MetaplecticGroup ρ) : proj ρ x = x.1.1 := rfl

/-- **The Weil representation** `ω_{ψ,S} : (g, M) ↦ M` of the metaplectic group on the space of the
model (GKT (2.3), p. 48). -/
def weil : Representation ℂ (MetaplecticGroup ρ) S where
  toFun x := x.1.2.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem weil_apply (x : MetaplecticGroup ρ) (v : S) : weil ρ x v = x.1.2 v := rfl

/-- The Weil representation normalizes `ρ` along the projection:
`ω(g, M) ∘ ρ(h) = ρ(g · h) ∘ ω(g, M)` (GKT (2.2)). -/
theorem weil_normalizes :
    Normalizes ρ ((isometryAction B).comp (proj ρ)) (weil ρ) :=
  fun x h => x.2 h

/-- The pair `(1, z)` of a non-zero scalar. -/
def scalar : ℂˣ →* MetaplecticGroup ρ where
  toFun z := ⟨(1, LinearEquiv.smulOfUnit z), fun h => LinearMap.ext fun v => by
    simp [LinearEquiv.smulOfUnit, Units.smul_def]⟩
  map_one' := by ext <;> simp [LinearEquiv.smulOfUnit]
  map_mul' z z' := by
    ext v
    · simp
    · change ((z * z' : ℂˣ) : ℂ) • v = (z : ℂ) • ((z' : ℂ) • v)
      rw [Units.val_mul, mul_smul]

@[simp] theorem proj_scalar (z : ℂˣ) : proj ρ (scalar ρ z) = 1 := rfl

@[simp] theorem weil_scalar (z : ℂˣ) (v : S) : weil ρ (scalar ρ z) v = (z : ℂ) • v := rfl

/-- The scalars are central. -/
theorem scalar_mem_center (z : ℂˣ) : scalar ρ z ∈ Subgroup.center (MetaplecticGroup ρ) := by
  rw [Subgroup.mem_center_iff]
  intro x
  ext v
  · simp [scalar]
  · change x.1.2 ((z : ℂ) • v) = (z : ℂ) • x.1.2 v
    exact map_smul _ _ _

/-- The scalars commute with every element. -/
theorem scalar_mul_comm (z : ℂˣ) (x : MetaplecticGroup ρ) : scalar ρ z * x = x * scalar ρ z :=
  (Subgroup.mem_center_iff.1 (scalar_mem_center ρ z) x).symm

/-- The scalar map is injective as soon as the space is non-zero. -/
theorem scalar_injective [Nontrivial S] : Function.Injective (scalar ρ) := by
  intro z z' h
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  have := congrArg (fun x : MetaplecticGroup ρ => weil ρ x v) h
  simp only [weil_scalar] at this
  exact Units.ext (smul_left_injective ℂ hv this)

section Unitary

variable (inner : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ)

/-- The pairs whose operator preserves a sesquilinear form on `S`: for the invariant Hermitian
form of the Heisenberg representation this is the book's `Mp(W)^{ℂ¹}_{ψ,S}` (GKT p. 49). -/
def unitary : Subgroup (MetaplecticGroup ρ) where
  carrier := {x | ∀ v w, inner (x.1.2 v) (x.1.2 w) = inner v w}
  mul_mem' {x y} hx hy v w := by
    change inner (x.1.2 (y.1.2 v)) (x.1.2 (y.1.2 w)) = inner v w
    rw [hx, hy]
  one_mem' _ _ := rfl
  inv_mem' {x} hx v w := by
    have e : ∀ u, x.1.2 ((x⁻¹).1.2 u) = u := fun u => by
      change ((x * x⁻¹).1.2) u = u
      rw [mul_inv_cancel]; rfl
    rw [← hx ((x⁻¹).1.2 v) ((x⁻¹).1.2 w), e, e]

/-- Membership in the unitary subgroup. -/
theorem mem_unitary_iff {x : MetaplecticGroup ρ} :
    x ∈ unitary ρ inner ↔ ∀ v w, inner (x.1.2 v) (x.1.2 w) = inner v w :=
  Iff.rfl

/-- The scalars of modulus one, as elements of the unitary subgroup. -/
def circle : Circle →* unitary ρ inner where
  toFun z := ⟨scalar ρ (Circle.toUnits z), fun v w => by
    change inner ((z : ℂ) • v) ((z : ℂ) • w) = inner v w
    rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_smul]
    have hz : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    rw [hz, one_smul]⟩
  map_one' := Subtype.ext (show scalar ρ (Circle.toUnits 1) = 1 by rw [map_one, map_one])
  map_mul' z z' := Subtype.ext (show scalar ρ (Circle.toUnits (z * z')) =
    scalar ρ (Circle.toUnits z) * scalar ρ (Circle.toUnits z') by rw [map_mul, map_mul])

end Unitary

section Lift

variable {G : Type*} [Group G]

/-- The linear automorphism `ω g` of a representation of a group. -/
def _root_.Langlands.Theta.reprLinearEquiv (ω : Representation ℂ G S) (g : G) : S ≃ₗ[ℂ] S where
  toLinearMap := ω g
  invFun := ω g⁻¹
  left_inv v := by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; exact
    Representation.inv_self_apply ω g v
  right_inv v := by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; exact
    Representation.self_inv_apply ω g v

/-- **A representation normalizing `ρ` is a lift to the metaplectic group**: for `ι : G →* Sp(W)`
and a representation `ω` of `G` with `ω g ∘ ρ(h) = ρ(ι g · h) ∘ ω g`, the map
`g ↦ (ι g, ω g)` is a homomorphism `G →* MetaplecticGroup ρ`. -/
def lift (ι : G →* isometryGroup B) (ω : Representation ℂ G S)
    (h : Normalizes ρ ((isometryAction B).comp ι) ω) : G →* MetaplecticGroup ρ where
  toFun g := ⟨(ι g, reprLinearEquiv ω g), h g⟩
  map_one' := by ext v <;> simp [reprLinearEquiv]
  map_mul' g g' := by ext v <;> simp [reprLinearEquiv]

variable {ρ} {ι : G →* isometryGroup B} {ω : Representation ℂ G S}
  (h : Normalizes ρ ((isometryAction B).comp ι) ω)

@[simp] theorem proj_comp_lift : (proj ρ).comp (lift ρ ι ω h) = ι := rfl

@[simp] theorem weil_comp_lift : (weil ρ).comp (lift ρ ι ω h) = ω := rfl

@[simp] theorem proj_lift (g : G) : proj ρ (lift ρ ι ω h g) = ι g := rfl

@[simp] theorem weil_lift (g : G) : weil ρ (lift ρ ι ω h g) = ω g := rfl

end Lift

section Congr

variable {ρ} {S' : Type*} [AddCommGroup S'] [Module ℂ S']
  {ρ' : Representation ℂ (HeisenbergGroup B) S'}

/-- The operator `e M e⁻¹`. -/
private def conjOp (e : Representation.Equiv ρ ρ') (M : S ≃ₗ[ℂ] S) : S' ≃ₗ[ℂ] S' :=
  (e.toLinearEquiv.symm.trans M).trans e.toLinearEquiv

private theorem conjOp_apply (e : Representation.Equiv ρ ρ') (M : S ≃ₗ[ℂ] S) (v : S') :
    conjOp e M v = e (M (e.symm v)) := rfl

/-- The relation (2.2) is carried along an isomorphism of models. -/
private theorem isMetaplecticPair_conjOp (e : Representation.Equiv ρ ρ') (x : MetaplecticGroup ρ) :
    IsMetaplecticPair ρ' x.1.1 (conjOp e x.1.2) := fun h => LinearMap.ext fun v => by
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conjOp_apply]
  have h1 : e.symm (ρ' h v) = ρ h (e.symm v) :=
    Representation.IntertwiningMap.isIntertwining ρ' ρ e.symm.toIntertwiningMap h v
  rw [h1, apply_apply]
  exact Representation.IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap _ _

/-- **Change of model** (GKT Proposition 6.8 (1)): an isomorphism `e : ρ ≃ ρ'` of representations of
the Heisenberg group carries `(g, M)` to `(g, e M e⁻¹)`. -/
def congr (e : Representation.Equiv ρ ρ') : MetaplecticGroup ρ ≃* MetaplecticGroup ρ' where
  toFun x := ⟨(x.1.1, conjOp e x.1.2), isMetaplecticPair_conjOp e x⟩
  invFun y := ⟨(y.1.1, conjOp e.symm y.1.2), isMetaplecticPair_conjOp e.symm y⟩
  left_inv x := by ext v <;> simp [conjOp_apply]
  right_inv y := by ext v <;> simp [conjOp_apply]
  map_mul' x y := by ext v <;> simp [conjOp_apply]

@[simp] theorem proj_congr (e : Representation.Equiv ρ ρ') (x : MetaplecticGroup ρ) :
    proj ρ' (congr e x) = proj ρ x := rfl

/-- The Weil representations of two models correspond through the isomorphism (GKT
Proposition 9.2). -/
theorem weil_congr (e : Representation.Equiv ρ ρ') (x : MetaplecticGroup ρ) (v : S) :
    weil ρ' (congr e x) (e v) = e (weil ρ x v) := by
  simp [congr, conjOp_apply]

end Congr

/-! ### Splittings -/

/-- **A splitting** of `ι : G →* Sp(W)` in the metaplectic group of the model `ρ`: a homomorphism
`G →* MetaplecticGroup ρ` lifting `ι` (GKT Remark 2.20 and the opening of chapter 7). -/
structure Splitting {G : Type*} [Group G] (ι : G →* isometryGroup B) where
  /-- The homomorphism to the metaplectic group. -/
  toMonoidHom : G →* MetaplecticGroup ρ
  /-- It lifts `ι`. -/
  proj_comp : (proj ρ).comp toMonoidHom = ι

namespace Splitting

variable {ρ} {G : Type*} [Group G] {ι : G →* isometryGroup B}

/-- Two splittings with the same homomorphism are equal. -/
@[ext] theorem ext {s s' : Splitting ρ ι} (h : s.toMonoidHom = s'.toMonoidHom) : s = s' := by
  cases s; cases s'; congr

@[simp] theorem proj_apply (s : Splitting ρ ι) (g : G) : proj ρ (s.toMonoidHom g) = ι g :=
  DFunLike.congr_fun s.proj_comp g

/-- **The Weil representation of a splitting** `ω_{ψ,s} = ω_ψ ∘ s` (GKT Definition 13.15). -/
def weil (s : Splitting ρ ι) : Representation ℂ G S :=
  (MetaplecticGroup.weil ρ).comp s.toMonoidHom

theorem weil_apply (s : Splitting ρ ι) (g : G) (v : S) :
    s.weil g v = (s.toMonoidHom g).1.2 v := rfl

/-- The Weil representation of a splitting normalizes `ρ` along `ι`. -/
theorem weil_normalizes (s : Splitting ρ ι) :
    Normalizes ρ ((isometryAction B).comp ι) s.weil := fun g h => by
  have key := (s.toMonoidHom g).2 h
  have e : ι g = (s.toMonoidHom g).1.1 := (s.proj_apply g).symm
  change _ = ρ (isometryAction B (ι g) h) ∘ₗ _
  rw [e]
  exact key

/-- The splitting given by a representation normalizing `ρ` along `ι` (`MetaplecticGroup.lift`). -/
def ofNormalizes (ω : Representation ℂ G S) (h : Normalizes ρ ((isometryAction B).comp ι) ω) :
    Splitting ρ ι :=
  ⟨lift ρ ι ω h, proj_comp_lift h⟩

/-- The Weil representation of `ofNormalizes ω h` is `ω`. -/
@[simp] theorem weil_ofNormalizes (ω : Representation ℂ G S)
    (h : Normalizes ρ ((isometryAction B).comp ι) ω) : (ofNormalizes ω h).weil = ω :=
  weil_comp_lift h

/-- A splitting is determined by its Weil representation. -/
theorem ext_weil {s s' : Splitting ρ ι} (h : s.weil = s'.weil) : s = s' := by
  ext g v
  · have h1 := s.proj_apply g
    have h2 := s'.proj_apply g
    rw [MetaplecticGroup.proj_apply] at h1 h2
    rw [h1, h2]
  · exact LinearMap.congr_fun (DFunLike.congr_fun h g) v

/-- The splitting `g ↦ α(g) · s(g)` of a splitting twisted by a character `α` of `G` (GKT
§12.2.1). -/
def twist (s : Splitting ρ ι) (α : G →* ℂˣ) : Splitting ρ ι where
  toMonoidHom :=
    { toFun := fun g => scalar ρ (α g) * s.toMonoidHom g
      map_one' := by simp
      map_mul' := fun g g' => by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (s.toMonoidHom g), ← scalar_mul_comm, mul_assoc] }
  proj_comp := MonoidHom.ext fun g => by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, map_mul,
      proj_scalar, one_mul]
    exact proj_apply s g

@[simp] theorem weil_twist (s : Splitting ρ ι) (α : G →* ℂˣ) (g : G) (v : S) :
    (s.twist α).weil g v = (α g : ℂ) • s.weil g v := rfl

/-- The splitting `s ∘ f` of `ι ∘ f`, for a homomorphism `f : G' →* G`. -/
def comp {G' : Type*} [Group G'] (s : Splitting ρ ι) (f : G' →* G) : Splitting ρ (ι.comp f) where
  toMonoidHom := s.toMonoidHom.comp f
  proj_comp := by rw [← MonoidHom.comp_assoc, s.proj_comp]

@[simp] theorem weil_comp {G' : Type*} [Group G'] (s : Splitting ρ ι) (f : G' →* G) :
    (s.comp f).weil = s.weil.comp f := rfl

end Splitting

end MetaplecticGroup

end Langlands.Theta
