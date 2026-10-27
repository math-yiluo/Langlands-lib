import Langlands.Algebra.NonUnitalModule
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Compatible nonunital algebra actions and actual linear endomorphisms

Renard (9 July 2026): module conventions on printed pp. 5–6, the final sentence of A.III.1
example 5 on printed p. 252, and the final proposition of C.II on printed p. 279. A compatible
action of a possibly nonunital `k`-algebra `B` on a `k`-module `V` is an actual homomorphism
`B →ₙₐ[k] Module.End k V`. It corresponds to the published ambient `NonUnitalModule B V`
together with `IsScalarTower k B V` and `SMulCommClass k B V`; `k`-linear intertwiners
correspond to the published additive `NonUnitalModuleHom` together with a separately supplied
`k`-linearity. No unit, unit law or global action instance is introduced.
-/

namespace Langlands.Algebra

universe u v w x y z

namespace NonUnitalModule

section Conversions

variable {k : Type u} {B : Type v} {V : Type w}
  [CommSemiring k] [NonUnitalRing B] [Module k B] [AddCommGroup V] [Module k V]

/-- Two ambient actions with the same scalar multiplication are equal. -/
theorem ext {h₁ h₂ : NonUnitalModule B V}
    (H : ∀ (b : B) (v : V), (letI := h₁; b • v) = (letI := h₂; b • v)) : h₁ = h₂ :=
  equivEndHom.injective (NonUnitalRingHom.ext fun b => AddMonoidHom.ext fun v => H b v)

/-- The ambient action `b • v = ρ b v` of an actual nonunital `k`-algebra homomorphism. -/
abbrev ofLinearEndHom (ρ : B →ₙₐ[k] Module.End k V) : NonUnitalModule B V where
  smul b v := ρ b v
  smul_zero b := (ρ b).map_zero
  smul_add b := (ρ b).map_add
  mul_smul b c v := by
    change ρ (b * c) v = (ρ b * ρ c) v
    exact congrArg (fun f : Module.End k V => f v) (map_mul ρ b c)
  add_smul b c v := by
    change ρ (b + c) v = (ρ b + ρ c) v
    exact congrArg (fun f : Module.End k V => f v) (map_add ρ b c)
  zero_smul v := by
    change ρ 0 v = 0
    exact congrArg (fun f : Module.End k V => f v) (map_zero ρ)

/-- The action formula of `ofLinearEndHom`. -/
theorem ofLinearEndHom_smul (ρ : B →ₙₐ[k] Module.End k V) (b : B) (v : V) :
    (letI := ofLinearEndHom ρ; b • v) = ρ b v := rfl

/-- Scalars of `k` pass through the algebra: `(c • b) • v = c • (b • v)`. -/
theorem ofLinearEndHom_smul_assoc (ρ : B →ₙₐ[k] Module.End k V) (c : k) (b : B) (v : V) :
    (letI := ofLinearEndHom ρ; (c • b) • v) = c • (letI := ofLinearEndHom ρ; b • v) :=
  congrArg (fun f : Module.End k V => f v) (map_smul ρ c b)

/-- Each algebra element acts `k`-linearly: `b • (c • v) = c • (b • v)`. -/
theorem ofLinearEndHom_smul_comm (ρ : B →ₙₐ[k] Module.End k V) (c : k) (b : B) (v : V) :
    (letI := ofLinearEndHom ρ; b • (c • v)) = c • (letI := ofLinearEndHom ρ; b • v) :=
  (ρ b).map_smul c v

/-- The scalar-tower structure of `ofLinearEndHom`, as a named adapter. -/
theorem ofLinearEndHom_isScalarTower (ρ : B →ₙₐ[k] Module.End k V) :
    letI := ofLinearEndHom ρ
    IsScalarTower k B V :=
  letI := ofLinearEndHom ρ
  ⟨ofLinearEndHom_smul_assoc ρ⟩

/-- The commuting-action structure of `ofLinearEndHom`, as a named adapter. -/
theorem ofLinearEndHom_smulCommClass (ρ : B →ₙₐ[k] Module.End k V) :
    letI := ofLinearEndHom ρ
    SMulCommClass k B V :=
  letI := ofLinearEndHom ρ
  ⟨fun c b v => (ofLinearEndHom_smul_comm ρ c b v).symm⟩

variable (k) in
/-- The actual nonunital `k`-algebra homomorphism of a compatible ambient action. -/
def toLinearEndHom [h : NonUnitalModule B V] [hT : IsScalarTower k B V]
    [hC : SMulCommClass k B V] : B →ₙₐ[k] Module.End k V where
  toFun b :=
    { toFun := (b • ·)
      map_add' := smul_add b
      map_smul' c v := (smul_comm c b v).symm }
  map_zero' := by
    ext v
    exact NonUnitalModule.zero_smul v
  map_add' b c := by
    ext v
    exact NonUnitalModule.add_smul b c v
  map_mul' b c := by
    ext v
    exact mul_smul b c v
  map_smul' c b := by
    ext v
    exact smul_assoc c b v

/-- The application formula of `toLinearEndHom`. -/
@[simp] theorem toLinearEndHom_apply [NonUnitalModule B V] [IsScalarTower k B V]
    [SMulCommClass k B V] (b : B) (v : V) :
    toLinearEndHom k (B := B) (V := V) b v = b • v := rfl

/-- Homomorphism round trip: equality of actual nonunital algebra homomorphisms. -/
theorem toLinearEndHom_ofLinearEndHom (ρ : B →ₙₐ[k] Module.End k V) :
    toLinearEndHom k (h := ofLinearEndHom ρ) (hT := ofLinearEndHom_isScalarTower ρ)
      (hC := ofLinearEndHom_smulCommClass ρ) = ρ := by
  ext b v
  rfl

/-- Action round trip: equality of the retained ambient action structure. -/
theorem ofLinearEndHom_toLinearEndHom [h : NonUnitalModule B V] [IsScalarTower k B V]
    [SMulCommClass k B V] : ofLinearEndHom (toLinearEndHom k (B := B) (V := V)) = h :=
  ext fun _ _ => rfl

/-- The published additive description of `ofLinearEndHom ρ` evaluates `ρ`. -/
theorem toEndHom_ofLinearEndHom_apply (ρ : B →ₙₐ[k] Module.End k V) (b : B) (v : V) :
    toEndHom (ofLinearEndHom ρ) b v = ρ b v := rfl

variable (k B V) in
/-- Compatible ambient actions correspond exactly to actual nonunital algebra homomorphisms. -/
def equivLinearEndHom :
    {h : NonUnitalModule B V // letI := h; IsScalarTower k B V ∧ SMulCommClass k B V} ≃
      (B →ₙₐ[k] Module.End k V) where
  toFun h := toLinearEndHom k (h := h.1) (hT := h.2.1) (hC := h.2.2)
  invFun ρ := ⟨ofLinearEndHom ρ, ofLinearEndHom_isScalarTower ρ, ofLinearEndHom_smulCommClass ρ⟩
  left_inv _ := Subtype.ext (ext fun _ _ => rfl)
  right_inv ρ := toLinearEndHom_ofLinearEndHom ρ

@[simp] theorem equivLinearEndHom_apply
    (h : {h : NonUnitalModule B V // letI := h; IsScalarTower k B V ∧ SMulCommClass k B V})
    (b : B) (v : V) : equivLinearEndHom k B V h b v = (letI := h.1; b • v) := rfl

@[simp] theorem equivLinearEndHom_symm_apply_coe (ρ : B →ₙₐ[k] Module.End k V) :
    ((equivLinearEndHom k B V).symm ρ : NonUnitalModule B V) = ofLinearEndHom ρ := rfl

/-! ### The zero action -/

/-- The zero homomorphism gives exactly the published zero action. -/
theorem ofLinearEndHom_zero :
    ofLinearEndHom (0 : B →ₙₐ[k] Module.End k V) = NonUnitalModule.zero :=
  ext fun _ _ => rfl

/-- The published zero action has the scalar-tower structure. -/
theorem isScalarTower_zero :
    letI : NonUnitalModule B V := NonUnitalModule.zero
    IsScalarTower k B V :=
  letI : NonUnitalModule B V := NonUnitalModule.zero
  ⟨fun c _ _ => (smul_zero c).symm⟩

omit [Module k B] in
/-- The published zero action commutes with the scalar action. -/
theorem smulCommClass_zero :
    letI : NonUnitalModule B V := NonUnitalModule.zero
    SMulCommClass k B V :=
  letI : NonUnitalModule B V := NonUnitalModule.zero
  ⟨fun c _ _ => smul_zero c⟩

/-- The published zero action corresponds to the zero homomorphism. -/
theorem toLinearEndHom_zero :
    toLinearEndHom k (h := (NonUnitalModule.zero : NonUnitalModule B V))
      (hT := isScalarTower_zero) (hC := smulCommClass_zero) = 0 := by
  ext b v
  rfl

end Conversions

section NonzeroZeroAction

/-- On a nonzero space, the zero compatible action of a unital algebra is not unital. -/
theorem not_isUnitalModule_ofLinearEndHom_zero {k : Type u} {B : Type v} {V : Type w}
    [CommSemiring k] [Ring B] [Module k B] [AddCommGroup V] [Module k V] [Nontrivial V] :
    letI := ofLinearEndHom (0 : B →ₙₐ[k] Module.End k V)
    ¬ IsUnitalModule B V := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (h v).symm

/-- On the nonzero space `K` over a field `K`, notation selects the specified zero action,
not the multiplication of `K`. -/
theorem ofLinearEndHom_zero_self_smul {K : Type u} [Field K] (c d : K) :
    (letI := ofLinearEndHom (0 : K →ₙₐ[K] Module.End K K); c • d) = 0 := rfl

/-- The zero compatible action of `K` on itself differs from the ordinary unital action. -/
theorem ofLinearEndHom_zero_ne_ofModule {K : Type u} [Field K] :
    ofLinearEndHom (0 : K →ₙₐ[K] Module.End K K) ≠ NonUnitalModule.ofModule K K := by
  intro h
  have h₁ : (letI := NonUnitalModule.ofModule K K; (1 : K) • (1 : K)) = 1 := mul_one 1
  have h₂ := congrArg (fun h : NonUnitalModule K K => (letI := h; (1 : K) • (1 : K))) h
  exact zero_ne_one (h₂.trans h₁)

end NonzeroZeroAction

section Unital

variable (k : Type u) (B : Type v) (V : Type w) [CommSemiring k] [Ring B] [Algebra k B]
  [AddCommGroup V] [Module k V] [Module B V] [IsScalarTower k B V]

/-- The ordinary action of a unital `k`-algebra on a unital module with compatible scalars,
as a nonunital homomorphism. This is a named definition, not an instance. -/
def unitalLinearEndHom : B →ₙₐ[k] Module.End k V :=
  (Algebra.lsmul k k V).toNonUnitalAlgHom

@[simp] theorem unitalLinearEndHom_apply (b : B) (v : V) :
    unitalLinearEndHom k B V b v = b • v := rfl

/-- The unital specialization sends the unit of `B` to the identity. -/
theorem unitalLinearEndHom_one : unitalLinearEndHom k B V 1 = 1 :=
  (Algebra.lsmul k k V).map_one

/-- The scalar-tower structure of the published unital adapter `ofModule`. -/
theorem ofModule_isScalarTower :
    letI := NonUnitalModule.ofModule B V
    IsScalarTower k B V :=
  letI := NonUnitalModule.ofModule B V
  ⟨fun c b v => smul_assoc (α := V) c b v⟩

/-- The commuting-action structure of the published unital adapter `ofModule`. -/
theorem ofModule_smulCommClass :
    letI := NonUnitalModule.ofModule B V
    SMulCommClass k B V :=
  letI := NonUnitalModule.ofModule B V
  ⟨fun c b v => smul_comm (α := V) c b v⟩

/-- The unital specialization retains exactly the ordinary module action. -/
theorem ofLinearEndHom_unitalLinearEndHom :
    ofLinearEndHom (unitalLinearEndHom k B V) = NonUnitalModule.ofModule B V :=
  ext fun _ _ => rfl

/-- The published unital adapter corresponds to the unital specialization. -/
theorem toLinearEndHom_ofModule :
    toLinearEndHom k (h := NonUnitalModule.ofModule B V) (hT := ofModule_isScalarTower k B V)
      (hC := ofModule_smulCommClass k B V) = unitalLinearEndHom k B V := by
  ext b v
  rfl

/-- The unital specialization is a unital ambient action. -/
theorem isUnitalModule_ofLinearEndHom_unitalLinearEndHom :
    letI := ofLinearEndHom (unitalLinearEndHom k B V)
    IsUnitalModule B V :=
  fun v => one_smul B v

end Unital

end NonUnitalModule

section Intertwiners

variable {k : Type u} {B : Type v} {V : Type w} {W : Type x} {P : Type y}
  [CommSemiring k] [NonUnitalRing B] [Module k B]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup P] [Module k P]

/-- Actual `k`-linear maps intertwining two compatible actions. -/
structure LinearIntertwiner (ρ : B →ₙₐ[k] Module.End k V) (σ : B →ₙₐ[k] Module.End k W)
    extends V →ₗ[k] W where
  map_action' (b : B) (v : V) : toLinearMap (ρ b v) = σ b (toLinearMap v)

namespace LinearIntertwiner

variable {ρ : B →ₙₐ[k] Module.End k V} {σ : B →ₙₐ[k] Module.End k W}
  {τ : B →ₙₐ[k] Module.End k P}

instance : FunLike (LinearIntertwiner ρ σ) V W where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (LinearIntertwiner ρ σ) k V W where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

@[ext] theorem ext {f g : LinearIntertwiner ρ σ} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

@[simp] theorem coe_toLinearMap (f : LinearIntertwiner ρ σ) : ⇑f.toLinearMap = f := rfl

@[simp] theorem coe_mk (f : V →ₗ[k] W) (hf : ∀ (b : B) (v : V), f (ρ b v) = σ b (f v)) :
    ⇑(⟨f, hf⟩ : LinearIntertwiner ρ σ) = f := rfl

/-- The intertwining equation. -/
@[simp] theorem map_action (f : LinearIntertwiner ρ σ) (b : B) (v : V) :
    f (ρ b v) = σ b (f v) := f.map_action' b v

/-- The intertwining equation as an equality of linear maps. -/
theorem toLinearMap_comp_action (f : LinearIntertwiner ρ σ) (b : B) :
    f.toLinearMap ∘ₗ ρ b = σ b ∘ₗ f.toLinearMap :=
  LinearMap.ext (f.map_action b)

/-- The identity intertwiner. -/
def id (ρ : B →ₙₐ[k] Module.End k V) : LinearIntertwiner ρ ρ where
  toLinearMap := LinearMap.id
  map_action' _ _ := rfl

/-- Composition of intertwiners. -/
def comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ) : LinearIntertwiner ρ τ where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_action' b v := by
    change g (f (ρ b v)) = τ b (g (f v))
    rw [f.map_action, g.map_action]

@[simp] theorem id_apply (v : V) : id ρ v = v := rfl

@[simp] theorem comp_apply (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ) (v : V) :
    g.comp f v = g (f v) := rfl

@[simp] theorem toLinearMap_id : (id ρ).toLinearMap = LinearMap.id := rfl

@[simp] theorem toLinearMap_comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := rfl

@[simp] theorem id_comp (f : LinearIntertwiner ρ σ) : (id σ).comp f = f := rfl

@[simp] theorem comp_id (f : LinearIntertwiner ρ σ) : f.comp (id ρ) = f := rfl

theorem comp_assoc {Q : Type z} [AddCommGroup Q] [Module k Q] {π : B →ₙₐ[k] Module.End k Q}
    (h : LinearIntertwiner τ π) (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- The actual additive ambient intertwiner of a linear intertwiner. -/
def toNonUnitalModuleHom (f : LinearIntertwiner ρ σ) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := NonUnitalModule.ofLinearEndHom σ
    NonUnitalModuleHom B V W :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  letI := NonUnitalModule.ofLinearEndHom σ
  { toAddMonoidHom := f.toLinearMap.toAddMonoidHom
    map_smul' := f.map_action }

@[simp] theorem toNonUnitalModuleHom_apply (f : LinearIntertwiner ρ σ) (v : V) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := NonUnitalModule.ofLinearEndHom σ
    f.toNonUnitalModuleHom v = f v := rfl

/-- A `k`-linear ambient intertwiner; its `k`-linearity is supplied separately. -/
def ofNonUnitalModuleHom
    (f : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      NonUnitalModuleHom B V W)
    (hf : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      ∀ (c : k) (v : V), f (c • v) = c • f v) :
    LinearIntertwiner ρ σ :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  letI := NonUnitalModule.ofLinearEndHom σ
  { toFun := f
    map_add' := f.map_add
    map_smul' := hf
    map_action' := f.map_smul }

@[simp] theorem ofNonUnitalModuleHom_apply
    (f : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      NonUnitalModuleHom B V W)
    (hf : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      ∀ (c : k) (v : V), f (c • v) = c • f v) (v : V) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := NonUnitalModule.ofLinearEndHom σ
    ofNonUnitalModuleHom f hf v = f v := rfl

/-- Underlying-map round trip starting from a linear intertwiner. -/
@[simp] theorem ofNonUnitalModuleHom_toNonUnitalModuleHom (f : LinearIntertwiner ρ σ) :
    ofNonUnitalModuleHom f.toNonUnitalModuleHom (fun c v => map_smul f c v) = f := rfl

/-- Underlying-map round trip starting from an ambient intertwiner. -/
@[simp] theorem toNonUnitalModuleHom_ofNonUnitalModuleHom
    (f : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      NonUnitalModuleHom B V W)
    (hf : letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      ∀ (c : k) (v : V), f (c • v) = c • f v) :
    (ofNonUnitalModuleHom f hf).toNonUnitalModuleHom = f := rfl

variable (ρ σ) in
/-- Linear intertwiners are exactly the ambient intertwiners that are `k`-linear. -/
def equivNonUnitalModuleHom :
    LinearIntertwiner ρ σ ≃
      letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      {f : NonUnitalModuleHom B V W // ∀ (c : k) (v : V), f (c • v) = c • f v} where
  toFun f := ⟨f.toNonUnitalModuleHom, fun c v => map_smul f c v⟩
  invFun f := ofNonUnitalModuleHom f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identity linear intertwiner gives the published identity intertwiner. -/
@[simp] theorem toNonUnitalModuleHom_id :
    letI := NonUnitalModule.ofLinearEndHom ρ
    (id ρ).toNonUnitalModuleHom = NonUnitalModuleHom.id B V := rfl

/-- Composition of linear intertwiners gives the published composition. -/
@[simp] theorem toNonUnitalModuleHom_comp (g : LinearIntertwiner σ τ)
    (f : LinearIntertwiner ρ σ) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := NonUnitalModule.ofLinearEndHom σ
    letI := NonUnitalModule.ofLinearEndHom τ
    (g.comp f).toNonUnitalModuleHom = g.toNonUnitalModuleHom.comp f.toNonUnitalModuleHom :=
  rfl

end LinearIntertwiner

namespace NonUnitalModuleHom

variable (k) [NonUnitalModule B V] [NonUnitalModule B W] [NonUnitalModule B P]
  [IsScalarTower k B V] [SMulCommClass k B V] [IsScalarTower k B W] [SMulCommClass k B W]
  [IsScalarTower k B P] [SMulCommClass k B P]

/-- An existing ambient intertwiner between compatible actions, given its `k`-linearity. -/
def toLinearIntertwiner (f : NonUnitalModuleHom B V W)
    (hf : ∀ (c : k) (v : V), f (c • v) = c • f v) :
    LinearIntertwiner (NonUnitalModule.toLinearEndHom k (B := B) (V := V))
      (NonUnitalModule.toLinearEndHom k (B := B) (V := W)) :=
  LinearIntertwiner.ofNonUnitalModuleHom f hf

@[simp] theorem toLinearIntertwiner_apply (f : NonUnitalModuleHom B V W)
    (hf : ∀ (c : k) (v : V), f (c • v) = c • f v) (v : V) :
    f.toLinearIntertwiner k hf v = f v := rfl

/-- Forgetting the supplied linearity recovers the original ambient intertwiner. -/
@[simp] theorem toNonUnitalModuleHom_toLinearIntertwiner (f : NonUnitalModuleHom B V W)
    (hf : ∀ (c : k) (v : V), f (c • v) = c • f v) :
    (f.toLinearIntertwiner k hf).toNonUnitalModuleHom = f := rfl

variable {k} in
/-- A linear intertwiner between the homomorphisms of existing compatible actions, as an ambient
intertwiner of those same actions. -/
def ofLinearIntertwiner
    (f : LinearIntertwiner (NonUnitalModule.toLinearEndHom k (B := B) (V := V))
      (NonUnitalModule.toLinearEndHom k (B := B) (V := W))) : NonUnitalModuleHom B V W where
  toAddMonoidHom := f.toLinearMap.toAddMonoidHom
  map_smul' := f.map_action

variable {k} in
@[simp] theorem ofLinearIntertwiner_apply
    (f : LinearIntertwiner (NonUnitalModule.toLinearEndHom k (B := B) (V := V))
      (NonUnitalModule.toLinearEndHom k (B := B) (V := W))) (v : V) :
    ofLinearIntertwiner f v = f v := rfl

/-- Underlying-map round trip starting from an ambient intertwiner. -/
@[simp] theorem ofLinearIntertwiner_toLinearIntertwiner (f : NonUnitalModuleHom B V W)
    (hf : ∀ (c : k) (v : V), f (c • v) = c • f v) :
    ofLinearIntertwiner (f.toLinearIntertwiner k hf) = f := rfl

/-- Underlying-map round trip starting from a linear intertwiner. -/
@[simp] theorem toLinearIntertwiner_ofLinearIntertwiner
    (f : LinearIntertwiner (NonUnitalModule.toLinearEndHom k (B := B) (V := V))
      (NonUnitalModule.toLinearEndHom k (B := B) (V := W))) :
    (ofLinearIntertwiner f).toLinearIntertwiner k (fun c v => _root_.map_smul f c v) = f :=
    rfl

/-- The identity ambient intertwiner gives the identity linear intertwiner. -/
theorem toLinearIntertwiner_id :
    (NonUnitalModuleHom.id B V).toLinearIntertwiner k (fun _ _ => rfl) =
      LinearIntertwiner.id (NonUnitalModule.toLinearEndHom k (B := B) (V := V)) := rfl

/-- Composition of ambient intertwiners gives composition of linear intertwiners. -/
theorem toLinearIntertwiner_comp (g : NonUnitalModuleHom B W P) (f : NonUnitalModuleHom B V W)
    (hg : ∀ (c : k) (w : W), g (c • w) = c • g w)
    (hf : ∀ (c : k) (v : V), f (c • v) = c • f v) :
    (g.comp f).toLinearIntertwiner k (fun c v => by
        rw [comp_apply, comp_apply, hf, hg]) =
      (g.toLinearIntertwiner k hg).comp (f.toLinearIntertwiner k hf) := rfl

end NonUnitalModuleHom

end Intertwiners

/-! ### Source-facing field specialization

A field `K`, a possibly noncommutative and nonunital associative `K`-algebra `A` with bilinear
multiplication, and `K`-vector spaces of arbitrary dimension in independent universes. -/

section FieldInterface

variable {K : Type u} {A : Type v} {V : Type w} {W : Type x}
  [Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The target `Module.End K V` carries the bilinear multiplication of the interface. -/
example : IsScalarTower K (Module.End K V) (Module.End K V) ∧
    SMulCommClass K (Module.End K V) (Module.End K V) :=
  ⟨inferInstance, inferInstance⟩

/-- Item 1 at a field: action formula and both compatibility laws. -/
example (ρ : A →ₙₐ[K] Module.End K V) (c : K) (b : A) (v : V) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    b • v = ρ b v ∧ (c • b) • v = c • (b • v) ∧ b • (c • v) = c • (b • v) :=
  ⟨rfl, NonUnitalModule.ofLinearEndHom_smul_assoc ρ c b v,
    NonUnitalModule.ofLinearEndHom_smul_comm ρ c b v⟩

/-- Item 2 at a field: both round trips and the exact correspondence. -/
example (ρ : A →ₙₐ[K] Module.End K V) :
    NonUnitalModule.toLinearEndHom K (h := NonUnitalModule.ofLinearEndHom ρ)
      (hT := NonUnitalModule.ofLinearEndHom_isScalarTower ρ)
      (hC := NonUnitalModule.ofLinearEndHom_smulCommClass ρ) = ρ ∧
    NonUnitalModule.equivLinearEndHom K A V ((NonUnitalModule.equivLinearEndHom K A V).symm ρ) =
      ρ :=
  ⟨NonUnitalModule.toLinearEndHom_ofLinearEndHom ρ, Equiv.apply_symm_apply _ ρ⟩

example [h : NonUnitalModule A V] [IsScalarTower K A V] [SMulCommClass K A V] :
    NonUnitalModule.ofLinearEndHom (NonUnitalModule.toLinearEndHom K (B := A) (V := V)) = h :=
  NonUnitalModule.ofLinearEndHom_toLinearEndHom

/-- Item 3 at a field: both intertwiner round trips. -/
example (ρ : A →ₙₐ[K] Module.End K V) (σ : A →ₙₐ[K] Module.End K W)
    (f : LinearIntertwiner ρ σ) :
    LinearIntertwiner.ofNonUnitalModuleHom f.toNonUnitalModuleHom
      (fun c v => map_smul f c v) = f :=
  LinearIntertwiner.ofNonUnitalModuleHom_toNonUnitalModuleHom f

example [NonUnitalModule A V] [IsScalarTower K A V] [SMulCommClass K A V]
    [NonUnitalModule A W] [IsScalarTower K A W] [SMulCommClass K A W]
    (f : NonUnitalModuleHom A V W) (hf : ∀ (c : K) (v : V), f (c • v) = c • f v) :
    NonUnitalModuleHom.ofLinearIntertwiner (f.toLinearIntertwiner K hf) = f :=
  NonUnitalModuleHom.ofLinearIntertwiner_toLinearIntertwiner K f hf

/-- Item 4 at a field: on a nonzero vector space the zero action is compatible and kills a
nonzero vector. -/
example [Nontrivial V] :
    letI := NonUnitalModule.ofLinearEndHom (0 : A →ₙₐ[K] Module.End K V)
    (IsScalarTower K A V ∧ SMulCommClass K A V) ∧ ∃ v : V, v ≠ 0 ∧ ∀ b : A, b • v = 0 :=
  ⟨⟨NonUnitalModule.ofLinearEndHom_isScalarTower 0,
      NonUnitalModule.ofLinearEndHom_smulCommClass 0⟩,
    (exists_ne (0 : V)).imp fun _ hv => ⟨hv, fun _ => rfl⟩⟩

/-- Item 4 at a field: for a unital algebra the zero action on a nonzero space is not unital. -/
example {R : Type y} [Ring R] [Algebra K R] [Nontrivial V] :
    letI := NonUnitalModule.ofLinearEndHom (0 : R →ₙₐ[K] Module.End K V)
    ¬ IsUnitalModule R V :=
  NonUnitalModule.not_isUnitalModule_ofLinearEndHom_zero

/-- Item 4 at a field: the unital specialization retains the ordinary module action. -/
example {R : Type y} [Ring R] [Algebra K R] [Module R V] [IsScalarTower K R V] :
    NonUnitalModule.ofLinearEndHom (NonUnitalModule.unitalLinearEndHom K R V) =
      NonUnitalModule.ofModule R V :=
  NonUnitalModule.ofLinearEndHom_unitalLinearEndHom K R V

end FieldInterface

end Langlands.Algebra
