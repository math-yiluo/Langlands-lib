import Langlands.Shimura.PEL.InvariantOrbits

/-! # Transport of invariant right orbits -/

universe u v w x y z t

namespace Langlands.Shimura.PEL

variable {G : Type u} [Group G]
variable {X : Type v} {Y : Type w} {Z : Type x}
variable [MulAction Gᵐᵒᵖ X] [MulAction Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Z]

namespace RightOrbit

/-- A right-equivariant map induces a map on right level orbits. -/
def map (U : Subgroup G) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g) : RightOrbit X U → RightOrbit Y U :=
  Quotient.map f (by
    rintro x y ⟨g, hg, rfl⟩
    exact ⟨g, hg, hf x g⟩)

@[simp] theorem map_mk (U : Subgroup G) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g) (x : X) :
    map U f hf (mk U x) = mk U (f x) := rfl

@[simp] theorem map_id (U : Subgroup G) (q : RightOrbit X U) :
    map U id (fun _ _ => rfl) q = q := by
  induction q using Quotient.inductionOn with
  | h x => rfl

theorem map_comp (U : Subgroup G) (f : X → Y) (k : Y → Z)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ y (g : G), k (right y g) = right (k y) g) (q : RightOrbit X U) :
    map U k hk (map U f hf q) =
      map U (k ∘ f) (fun x g => by simp only [Function.comp_apply, hf, hk]) q := by
  induction q using Quotient.inductionOn with
  | h x => rfl

theorem map_congr (U : Subgroup G) (f k : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ x (g : G), k (right x g) = right (k x) g)
    (h : ∀ x, f x = k x) (q : RightOrbit X U) : map U f hf q = map U k hk q := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (mk U) (h x)

theorem map_translate {U V : Subgroup G} (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (q : RightOrbit X U) :
    map V f hf (translate g hg q) = translate g hg (map U f hf q) := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (mk V) (hf x g)

variable {Γ : Type y} {Δ : Type z} [Group Γ] [Group Δ]
variable [MulAction Γ X] [MulAction Δ Y]
variable [SMulCommClass Γ Gᵐᵒᵖ X] [SMulCommClass Δ Gᵐᵒᵖ Y]

theorem map_smul (U : Subgroup G) (α : Γ →* Δ) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x) (γ : Γ) (q : RightOrbit X U) :
    map U f hf (γ • q) = α γ • map U f hf q := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (mk U) (hΓ γ x)

/-- If representative maps differ by a target left action, so do their quotient maps. -/
theorem map_eq_smul (U : Subgroup G) (f k : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ x (g : G), k (right x g) = right (k x) g)
    (δ : Δ) (h : ∀ x, k x = δ • f x) (q : RightOrbit X U) :
    map U k hk q = δ • map U f hf q := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (mk U) (h x)

end RightOrbit

namespace InvariantOrbit

variable {Γ : Type y} {Δ : Type z} {Θ : Type t}
variable [Group Γ] [Group Δ] [Group Θ]
variable [MulAction Γ X] [MulAction Δ Y] [MulAction Θ Z]
variable [SMulCommClass Γ Gᵐᵒᵖ X] [SMulCommClass Δ Gᵐᵒᵖ Y]
variable [SMulCommClass Θ Gᵐᵒᵖ Z]

/-- Transport fixed orbits across an isomorphism of the left acting groups. -/
def map (U : Subgroup G) (α : Γ ≃* Δ) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x) :
    InvariantOrbit (X := X) Γ U → InvariantOrbit (X := Y) Δ U := fun q =>
  ⟨RightOrbit.map U f hf q.1, fun δ => by
    have h := RightOrbit.map_smul U α.toMonoidHom f hf hΓ (α.symm δ) q.1
    rw [q.2] at h
    simpa using h.symm⟩

@[simp] theorem map_val (U : Subgroup G) (α : Γ ≃* Δ) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x) (q : InvariantOrbit (X := X) Γ U) :
    (map U α f hf hΓ q).1 = RightOrbit.map U f hf q.1 := rfl

@[simp] theorem map_id (U : Subgroup G) (q : InvariantOrbit (X := X) Γ U) :
    map U (MulEquiv.refl Γ) id (fun _ _ => rfl) (fun _ _ => rfl) q = q :=
  Subtype.ext (RightOrbit.map_id U q.1)

theorem map_comp (U : Subgroup G) (α : Γ ≃* Δ) (β : Δ ≃* Θ)
    (f : X → Y) (k : Y → Z)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ y (g : G), k (right y g) = right (k y) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x)
    (hΔ : ∀ δ y, k (δ • y) = β δ • k y) (q : InvariantOrbit (X := X) Γ U) :
    map U β k hk hΔ (map U α f hf hΓ q) =
      map U (α.trans β) (k ∘ f)
        (fun x g => by simp only [Function.comp_apply, hf, hk])
        (fun γ x => by simp only [Function.comp_apply, hΓ, hΔ, MulEquiv.trans_apply]) q :=
  Subtype.ext (RightOrbit.map_comp U f k hf hk q.1)

/-- The quotient map does not retain the choice of group isomorphism or equivariance proofs. -/
theorem map_congr (U : Subgroup G) (α β : Γ ≃* Δ) (f k : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ x (g : G), k (right x g) = right (k x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x)
    (hΓ' : ∀ γ x, k (γ • x) = β γ • k x)
    (h : ∀ x, f x = k x) (q : InvariantOrbit (X := X) Γ U) :
    map U α f hf hΓ q = map U β k hk hΓ' q :=
  Subtype.ext (RightOrbit.map_congr U f k hf hk h q.1)

theorem map_translate {U V : Subgroup G} (α : Γ ≃* Δ) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x)
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (q : InvariantOrbit (X := X) Γ U) :
    map V α f hf hΓ (translate g hg q) = translate g hg (map U α f hf hΓ q) :=
  Subtype.ext (RightOrbit.map_translate f hf g hg q.1)

theorem map_forget {U V : Subgroup G} (α : Γ ≃* Δ) (f : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x)
    (hUV : U ≤ V) (q : InvariantOrbit (X := X) Γ U) :
    map V α f hf hΓ (forget hUV q) = forget hUV (map U α f hf hΓ q) :=
  map_translate α f hf hΓ 1 _ q

/-- A difference by target monodromy disappears on fixed orbit classes. -/
theorem map_eq_of_left (U : Subgroup G) (α β : Γ ≃* Δ) (f k : X → Y)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hk : ∀ x (g : G), k (right x g) = right (k x) g)
    (hΓ : ∀ γ x, f (γ • x) = α γ • f x)
    (hΓ' : ∀ γ x, k (γ • x) = β γ • k x)
    (δ : Δ) (h : ∀ x, k x = δ • f x) (q : InvariantOrbit (X := X) Γ U) :
    map U β k hk hΓ' q = map U α f hf hΓ q := by
  apply Subtype.ext
  exact (RightOrbit.map_eq_smul U f k hf hk δ h q.1).trans ((map U α f hf hΓ q).2 δ)

/-- A biequivariant equivalence induces an equivalence of fixed orbit sets. -/
def equiv (U : Subgroup G) (α : Γ ≃* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) :
    InvariantOrbit (X := X) Γ U ≃ InvariantOrbit (X := Y) Δ U where
  toFun := map U α e he hΓ
  invFun := map U α.symm e.symm
    (fun y g => by
      apply e.injective
      simp only [Equiv.apply_symm_apply, he])
    (fun δ y => by
      apply e.injective
      simp only [Equiv.apply_symm_apply, hΓ, MulEquiv.apply_symm_apply])
  left_inv q := by
    apply Subtype.ext
    simp only [map_val]
    induction q.1 using Quotient.inductionOn with
    | h x => exact congrArg (RightOrbit.mk U) (e.symm_apply_apply x)
  right_inv q := by
    apply Subtype.ext
    simp only [map_val]
    induction q.1 using Quotient.inductionOn with
    | h y => exact congrArg (RightOrbit.mk U) (e.apply_symm_apply y)

@[simp] theorem equiv_apply (U : Subgroup G) (α : Γ ≃* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) (q : InvariantOrbit (X := X) Γ U) :
    equiv U α e he hΓ q = map U α e he hΓ q := rfl

/-- Equality of the equivalences when their representative maps differ by a left action. -/
theorem equiv_eq_of_left (U : Subgroup G) (α β : Γ ≃* Δ) (e f : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hf : ∀ x (g : G), f (right x g) = right (f x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x)
    (hΓ' : ∀ γ x, f (γ • x) = β γ • f x)
    (δ : Δ) (h : ∀ x, f x = δ • e x) :
    equiv U β f hf hΓ' = equiv U α e he hΓ := by
  ext q
  exact map_eq_of_left U α β e f he hf hΓ hΓ' δ h q

end InvariantOrbit
end Langlands.Shimura.PEL
