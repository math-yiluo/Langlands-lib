import Langlands.Algebra.CompatibleNonUnitalAction
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Basic.Complex.Basic

/-!
# The unitized action of a compatible nonunital algebra action

Renard (9 July 2026), I.2.1 on printed p. 14 and the opening of B.II on printed p. 272. For a
possibly nonunital `k`-algebra `A` acting on a `k`-module `M` through an actual homomorphism
`ρ : A →ₙₐ[k] Module.End k M`, the unitized action of `Unitization k A` is the actual unital
algebra homomorphism `Unitization.lift ρ`, with `x • m = x.fst • m + ρ x.snd m`, and the
corresponding unital `Module` structure. It is a named definition, never a global instance.

Unitized linear maps correspond to `k`-linear maps intertwining the original actions, the
intersection `Hom_A ∩ Hom_k` of I.2.1, and the unitized endomorphism algebra is the actual
centralizer of the range of `ρ` in `Module.End k M`.
-/

namespace Langlands.Algebra

namespace CompatibleUnitization

open Unitization

universe u v w x y

section Action

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [Module k M]

/-- The unitized action homomorphism: the actual lift `Unitization.lift ρ`. -/
def endHom (ρ : A →ₙₐ[k] Module.End k M) : Unitization k A →ₐ[k] Module.End k M :=
  Unitization.lift ρ

/-- The formula of the unitized action homomorphism. -/
theorem endHom_apply (ρ : A →ₙₐ[k] Module.End k M) (x : Unitization k A) (m : M) :
    endHom ρ x m = x.fst • m + ρ x.snd m := rfl

/-- On `A`, the unitized action homomorphism is `ρ`. -/
@[simp] theorem endHom_inr (ρ : A →ₙₐ[k] Module.End k M) (a : A) :
    endHom ρ (a : Unitization k A) = ρ a := by
  ext m
  rw [endHom_apply, fst_inr, snd_inr, zero_smul, zero_add]

/-- On the scalar coordinate, the unitized action homomorphism is the scalar algebra map. -/
@[simp] theorem endHom_inl (ρ : A →ₙₐ[k] Module.End k M) (c : k) :
    endHom ρ (inl c : Unitization k A) = algebraMap k (Module.End k M) c :=
  (endHom ρ).commutes c

/-- Restricting the unitized action homomorphism along `A → Unitization k A` recovers `ρ`. -/
@[simp] theorem lift_symm_endHom (ρ : A →ₙₐ[k] Module.End k M) :
    Unitization.lift.symm (endHom ρ) = ρ :=
  Unitization.lift.symm_apply_apply ρ

/-- Uniqueness of the unitized action homomorphism, from the universal property. -/
theorem endHom_unique (ρ : A →ₙₐ[k] Module.End k M) (φ : Unitization k A →ₐ[k] Module.End k M)
    (h : ∀ a : A, φ a = ρ a) : φ = endHom ρ :=
  Unitization.algHom_ext'' fun a => (h a).trans (endHom_inr ρ a).symm

/-- The unitized action as an actual unital module structure. This is a definition, not an
instance; it is installed locally with `letI`. -/
@[instance_reducible]
def module (ρ : A →ₙₐ[k] Module.End k M) : Module (Unitization k A) M :=
  Module.compHom M (endHom ρ).toRingHom

/-- The unitized action is evaluation of the unitized action homomorphism. -/
theorem smul_def (ρ : A →ₙₐ[k] Module.End k M) (x : Unitization k A) (m : M) :
    (letI := module ρ; x • m) = endHom ρ x m := rfl

/-- The formula `x • m = x.fst • m + ρ x.snd m` of the unitized action. -/
theorem smul_eq (ρ : A →ₙₐ[k] Module.End k M) (x : Unitization k A) (m : M) :
    (letI := module ρ; x • m) = x.fst • m + ρ x.snd m := rfl

/-- Restricted to `A`, the unitized action is the original action. -/
@[simp] theorem inr_smul (ρ : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    (letI := module ρ; (a : Unitization k A) • m) = ρ a m := by
  rw [smul_def, endHom_inr]

/-- The scalar coordinate acts by the original scalar multiplication. -/
@[simp] theorem inl_smul (ρ : A →ₙₐ[k] Module.End k M) (c : k) (m : M) :
    (letI := module ρ; (inl c : Unitization k A) • m) = c • m := by
  rw [smul_def, endHom_inl, Module.algebraMap_end_apply]

/-- The scalar algebra map of the unitization acts by the original scalar multiplication. -/
@[simp] theorem algebraMap_smul (ρ : A →ₙₐ[k] Module.End k M) (c : k) (m : M) :
    (letI := module ρ; algebraMap k (Unitization k A) c • m) = c • m := by
  rw [smul_def, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The unit of the unitization acts as the identity. -/
theorem one_smul (ρ : A →ₙₐ[k] Module.End k M) (m : M) :
    (letI := module ρ; (1 : Unitization k A) • m) = m := by
  rw [smul_def, map_one, Module.End.one_apply]

/-- The published ambient action `NonUnitalModule.ofLinearEndHom ρ` is the restriction of the
unitized action to `A`. -/
theorem ofLinearEndHom_smul_eq_inr_smul (ρ : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    (letI := NonUnitalModule.ofLinearEndHom ρ; a • m) =
      (letI := module ρ; (a : Unitization k A) • m) :=
  (inr_smul ρ a m).symm

/-- Named adapter: the unitized action is a scalar tower over `k`. -/
theorem isScalarTower (ρ : A →ₙₐ[k] Module.End k M) :
    letI := module ρ
    IsScalarTower k (Unitization k A) M :=
  letI := module ρ
  ⟨fun c x m => by
    rw [smul_def, smul_def, map_smul, LinearMap.smul_apply]⟩

/-- Named adapter: the unitized action commutes with the scalar action, `k` on the left. -/
theorem smulCommClass (ρ : A →ₙₐ[k] Module.End k M) :
    letI := module ρ
    SMulCommClass k (Unitization k A) M :=
  letI := module ρ
  ⟨fun c x m => by
    rw [smul_def, smul_def, map_smul]⟩

/-- Named adapter: the unitized action commutes with the scalar action, `k` on the right. This
is the compatibility used by the `k`-module structure on unitized linear maps. -/
theorem smulCommClass' (ρ : A →ₙₐ[k] Module.End k M) :
    letI := module ρ
    SMulCommClass (Unitization k A) k M :=
  letI := module ρ
  ⟨fun x c m => by
    rw [smul_def, smul_def, map_smul]⟩

/-- Uniqueness: a unital action of the unitization with the scalar coordinate acting by the
scalar multiplication and `A` acting by `ρ` is the unitized action. -/
theorem module_unique (ρ : A →ₙₐ[k] Module.End k M) (h : Module (Unitization k A) M)
    (hinl : ∀ (c : k) (m : M), (letI := h; (inl c : Unitization k A) • m) = c • m)
    (hinr : ∀ (a : A) (m : M), (letI := h; (a : Unitization k A) • m) = ρ a m) :
    h = module ρ :=
  Module.ext' _ _ fun x m => by
    rw [smul_eq ρ]
    let _inst := h
    conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
    rw [add_smul, hinl, hinr]

/-- Uniqueness among unital actions of the unitization forming a scalar tower over `k`. -/
theorem module_unique_of_isScalarTower (ρ : A →ₙₐ[k] Module.End k M)
    (h : Module (Unitization k A) M) (hT : letI := h; IsScalarTower k (Unitization k A) M)
    (hinr : ∀ (a : A) (m : M), (letI := h; (a : Unitization k A) • m) = ρ a m) :
    h = module ρ :=
  module_unique ρ h (fun c m => by
    let _inst := h
    rw [← algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one, smul_assoc, _root_.one_smul])
    hinr

end Action

section Hom

variable {k : Type u} {A : Type v} {M : Type w} {N : Type x} {P : Type y}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- The actual `k`-submodule of `k`-linear maps intertwining `ρ` and `σ`. -/
def intertwiners (ρ : A →ₙₐ[k] Module.End k M) (σ : A →ₙₐ[k] Module.End k N) :
    Submodule k (M →ₗ[k] N) where
  carrier := {f | ∀ (a : A) (m : M), f (ρ a m) = σ a (f m)}
  add_mem' {f g} hf hg a m := by
    change f (ρ a m) + g (ρ a m) = σ a (f m + g m)
    rw [hf, hg, map_add]
  zero_mem' a m := by
    change (0 : N) = σ a 0
    rw [map_zero]
  smul_mem' c f hf a m := by
    change c • f (ρ a m) = σ a (c • f m)
    rw [hf, map_smul]

theorem mem_intertwiners (ρ : A →ₙₐ[k] Module.End k M) (σ : A →ₙₐ[k] Module.End k N)
    {f : M →ₗ[k] N} : f ∈ intertwiners ρ σ ↔ ∀ (a : A) (m : M), f (ρ a m) = σ a (f m) :=
  Iff.rfl

variable {ρ : A →ₙₐ[k] Module.End k M} {σ : A →ₙₐ[k] Module.End k N}
  {τ : A →ₙₐ[k] Module.End k P}

/-- The identity `k`-linear map intertwines `ρ` with itself. -/
theorem id_mem_intertwiners : (LinearMap.id : M →ₗ[k] M) ∈ intertwiners ρ ρ :=
  fun _ _ => rfl

/-- Composites of intertwining `k`-linear maps intertwine. -/
theorem comp_mem_intertwiners {g : N →ₗ[k] P} {f : M →ₗ[k] N} (hg : g ∈ intertwiners σ τ)
    (hf : f ∈ intertwiners ρ σ) : g ∘ₗ f ∈ intertwiners ρ τ := fun a m => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]

variable (ρ σ) in
/-- The intertwining `k`-linear maps are exactly the bridge's linear intertwiners. -/
def intertwinersEquiv : intertwiners ρ σ ≃ LinearIntertwiner ρ σ where
  toFun g := ⟨g.1, g.2⟩
  invFun f := ⟨f.toLinearMap, f.map_action'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem intertwinersEquiv_apply (g : intertwiners ρ σ) (m : M) :
    intertwinersEquiv ρ σ g m = g.1 m := rfl

@[simp] theorem intertwinersEquiv_symm_apply_coe (f : LinearIntertwiner ρ σ) :
    ((intertwinersEquiv ρ σ).symm f : M →ₗ[k] N) = f.toLinearMap := rfl

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- The `k`-linear map underlying a unitized linear map, by actual restriction of scalars. -/
def toLinearMap (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    M →ₗ[k] N :=
  letI := module ρ
  letI := module σ
  letI := isScalarTower ρ
  letI := isScalarTower σ
  f.restrictScalars k

@[simp] theorem toLinearMap_apply
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) (m : M) :
    toLinearMap f m = (letI := module ρ; letI := module σ; f m) := rfl

/-- The underlying `k`-linear map of a unitized linear map intertwines `ρ` and `σ`. -/
theorem toLinearMap_mem_intertwiners
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    toLinearMap f ∈ intertwiners ρ σ := fun a m => by
  let _instM := module ρ
  let _instN := module σ
  rw [toLinearMap_apply, toLinearMap_apply, ← inr_smul ρ, ← inr_smul σ]
  exact f.map_smul (a : Unitization k A) m

/-- The unitized linear map of a `k`-linear map intertwining `ρ` and `σ`. -/
def ofLinearMap (g : M →ₗ[k] N) (hg : g ∈ intertwiners ρ σ) :
    letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N :=
  letI := module ρ
  letI := module σ
  { toFun := g
    map_add' := g.map_add
    map_smul' x m := by
      rw [RingHom.id_apply, smul_eq, smul_eq, map_add, map_smul, hg] }

@[simp] theorem ofLinearMap_apply (g : M →ₗ[k] N) (hg : g ∈ intertwiners ρ σ) (m : M) :
    (letI := module ρ; letI := module σ; ofLinearMap g hg m) = g m := rfl

@[simp] theorem toLinearMap_ofLinearMap (g : M →ₗ[k] N) (hg : g ∈ intertwiners ρ σ) :
    toLinearMap (ofLinearMap g hg) = g := rfl

@[simp] theorem ofLinearMap_toLinearMap
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    ofLinearMap (toLinearMap f) (toLinearMap_mem_intertwiners f) = f := rfl

/-- The unitized identity map is the identity `k`-linear map. -/
@[simp] theorem toLinearMap_id :
    toLinearMap (letI := module ρ; (LinearMap.id : M →ₗ[Unitization k A] M)) = LinearMap.id :=
  rfl

/-- Composition of unitized linear maps is composition of `k`-linear maps. -/
@[simp] theorem toLinearMap_comp
    (g : letI := module σ; letI := module τ; N →ₗ[Unitization k A] P)
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    toLinearMap (letI := module ρ; letI := module σ; letI := module τ; g ∘ₗ f) =
      toLinearMap g ∘ₗ toLinearMap f :=
  rfl

@[simp] theorem ofLinearMap_id :
    ofLinearMap LinearMap.id (id_mem_intertwiners (ρ := ρ)) =
      (letI := module ρ; (LinearMap.id : M →ₗ[Unitization k A] M)) :=
  rfl

@[simp] theorem ofLinearMap_comp {g : N →ₗ[k] P} {f : M →ₗ[k] N} (hg : g ∈ intertwiners σ τ)
    (hf : f ∈ intertwiners ρ σ) :
    ofLinearMap (g ∘ₗ f) (comp_mem_intertwiners hg hf) =
      (letI := module ρ; letI := module σ; letI := module τ;
        ofLinearMap g hg ∘ₗ ofLinearMap f hf) :=
  rfl

variable (ρ σ) in
/-- Unitized linear maps form the same `k`-module as the intertwining `k`-linear maps. -/
def linearMapEquiv :
    letI := module ρ
    letI := module σ
    letI := smulCommClass' σ
    (M →ₗ[Unitization k A] N) ≃ₗ[k] intertwiners ρ σ :=
  letI := module ρ
  letI := module σ
  letI := smulCommClass' σ
  { toFun f := ⟨toLinearMap f, toLinearMap_mem_intertwiners f⟩
    invFun g := ofLinearMap g.1 g.2
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv _ := rfl }

@[simp] theorem linearMapEquiv_apply_coe
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    ((letI := module ρ; letI := module σ; letI := smulCommClass' σ;
      linearMapEquiv ρ σ f : intertwiners ρ σ) : M →ₗ[k] N) = toLinearMap f := rfl

@[simp] theorem linearMapEquiv_symm_apply (g : intertwiners ρ σ) :
    (letI := module ρ; letI := module σ; letI := smulCommClass' σ;
      (linearMapEquiv ρ σ).symm g) = ofLinearMap g.1 g.2 := rfl

/-- The bridge's linear intertwiner of a unitized linear map. -/
def toLinearIntertwiner (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    LinearIntertwiner ρ σ :=
  ⟨toLinearMap f, toLinearMap_mem_intertwiners f⟩

/-- The unitized linear map of a linear intertwiner of the bridge. -/
def ofLinearIntertwiner (f : LinearIntertwiner ρ σ) :
    letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N :=
  ofLinearMap f.toLinearMap f.map_action'

@[simp] theorem toLinearIntertwiner_apply
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) (m : M) :
    toLinearIntertwiner f m = (letI := module ρ; letI := module σ; f m) := rfl

@[simp] theorem ofLinearIntertwiner_apply (f : LinearIntertwiner ρ σ) (m : M) :
    (letI := module ρ; letI := module σ; ofLinearIntertwiner f m) = f m := rfl

@[simp] theorem toLinearIntertwiner_ofLinearIntertwiner (f : LinearIntertwiner ρ σ) :
    toLinearIntertwiner (ofLinearIntertwiner f) = f := rfl

@[simp] theorem ofLinearIntertwiner_toLinearIntertwiner
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    ofLinearIntertwiner (toLinearIntertwiner f) = f := rfl

@[simp] theorem toLinearIntertwiner_id :
    toLinearIntertwiner (letI := module ρ; (LinearMap.id : M →ₗ[Unitization k A] M)) =
      LinearIntertwiner.id ρ :=
  rfl

@[simp] theorem toLinearIntertwiner_comp
    (g : letI := module σ; letI := module τ; N →ₗ[Unitization k A] P)
    (f : letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) :
    toLinearIntertwiner (letI := module ρ; letI := module σ; letI := module τ; g ∘ₗ f) =
      (toLinearIntertwiner g).comp (toLinearIntertwiner f) :=
  rfl

@[simp] theorem ofLinearIntertwiner_id :
    ofLinearIntertwiner (LinearIntertwiner.id ρ) =
      (letI := module ρ; (LinearMap.id : M →ₗ[Unitization k A] M)) :=
  rfl

@[simp] theorem ofLinearIntertwiner_comp (g : LinearIntertwiner σ τ)
    (f : LinearIntertwiner ρ σ) :
    ofLinearIntertwiner (g.comp f) =
      (letI := module ρ; letI := module σ; letI := module τ;
        ofLinearIntertwiner g ∘ₗ ofLinearIntertwiner f) :=
  rfl

variable (ρ σ) in
/-- Unitized linear maps correspond exactly to the bridge's linear intertwiners. -/
def linearIntertwinerEquiv :
    (letI := module ρ; letI := module σ; M →ₗ[Unitization k A] N) ≃ LinearIntertwiner ρ σ where
  toFun := toLinearIntertwiner
  invFun := ofLinearIntertwiner
  left_inv := ofLinearIntertwiner_toLinearIntertwiner
  right_inv := toLinearIntertwiner_ofLinearIntertwiner

end Hom

section Centralizer

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]

/-- The endomorphism `k`-algebra of the given action: the actual centralizer of the range of `ρ`
in `Module.End k M`. -/
def centralizer (ρ : A →ₙₐ[k] Module.End k M) : Subalgebra k (Module.End k M) :=
  Subalgebra.centralizer k (Set.range ρ)

theorem mem_centralizer_iff (ρ : A →ₙₐ[k] Module.End k M) {f : Module.End k M} :
    f ∈ centralizer ρ ↔ ∀ (a : A) (m : M), f (ρ a m) = ρ a (f m) := by
  rw [centralizer, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h a m
    exact (LinearMap.congr_fun (h (ρ a) ⟨a, rfl⟩) m).symm
  · rintro h _ ⟨a, rfl⟩
    exact LinearMap.ext fun m => (h a m).symm

/-- As a `k`-submodule, the centralizer is the module of self-intertwiners. -/
theorem toSubmodule_centralizer (ρ : A →ₙₐ[k] Module.End k M) :
    Subalgebra.toSubmodule (centralizer ρ) = intertwiners ρ ρ :=
  Submodule.ext fun _ => mem_centralizer_iff ρ

/-- The scalar algebra map of the centralizer is the scalar algebra map of `Module.End k M`. -/
@[simp] theorem coe_algebraMap_centralizer (ρ : A →ₙₐ[k] Module.End k M) (c : k) :
    ((algebraMap k (centralizer ρ) c : centralizer ρ) : Module.End k M) =
      algebraMap k (Module.End k M) c :=
  rfl

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- The centralizer of the given action is the endomorphism algebra of the unitized action. -/
def endAlgEquiv (ρ : A →ₙₐ[k] Module.End k M) :
    letI := module ρ
    letI := isScalarTower ρ
    letI := smulCommClass' ρ
    centralizer ρ ≃ₐ[k] Module.End (Unitization k A) M :=
  letI := module ρ
  letI := isScalarTower ρ
  letI := smulCommClass' ρ
  { toFun f := ofLinearMap f.1 ((mem_centralizer_iff ρ).1 f.2)
    invFun g := ⟨toLinearMap g, (mem_centralizer_iff ρ).2 (toLinearMap_mem_intertwiners g)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl
    commutes' _ := rfl }

variable (ρ : A →ₙₐ[k] Module.End k M)

@[simp] theorem endAlgEquiv_apply (f : centralizer ρ) (m : M) :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      endAlgEquiv ρ f m) = (f : Module.End k M) m := rfl

@[simp] theorem endAlgEquiv_symm_apply
    (g : letI := module ρ; Module.End (Unitization k A) M) (m : M) :
    ((letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      (endAlgEquiv ρ).symm g : centralizer ρ) : Module.End k M) m =
      (letI := module ρ; g m) := rfl

/-- The equivalence is given by the Hom correspondence `linearMapEquiv`. -/
theorem endAlgEquiv_apply_eq (f : centralizer ρ) :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ; endAlgEquiv ρ f) =
      (letI := module ρ; letI := smulCommClass' ρ;
        (linearMapEquiv ρ ρ).symm ⟨f, (mem_centralizer_iff ρ).1 f.2⟩) := rfl

/-- Multiplication in the centralizer is composition of unitized endomorphisms. -/
theorem endAlgEquiv_mul (f g : centralizer ρ) :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      endAlgEquiv ρ (f * g)) =
      (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
        endAlgEquiv ρ f ∘ₗ endAlgEquiv ρ g) := rfl

/-- The identity of the centralizer is the identity unitized endomorphism. -/
theorem endAlgEquiv_one :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      endAlgEquiv ρ 1) = (letI := module ρ; (LinearMap.id : M →ₗ[Unitization k A] M)) := rfl

/-- The equivalence preserves the scalar algebra maps. -/
theorem endAlgEquiv_algebraMap (c : k) :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      endAlgEquiv ρ (algebraMap k (centralizer ρ) c)) =
      (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
        algebraMap k (Module.End (Unitization k A) M) c) :=
  letI := module ρ
  letI := isScalarTower ρ
  letI := smulCommClass' ρ
  (endAlgEquiv ρ).commutes c

/-- The scalar algebra map of the unitized endomorphism algebra acts by scalar multiplication. -/
theorem algebraMap_end_apply (c : k) (m : M) :
    (letI := module ρ; letI := isScalarTower ρ; letI := smulCommClass' ρ;
      algebraMap k (Module.End (Unitization k A) M) c m) = c • m := rfl

end Centralizer

section ZeroAction

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [Module k M]

/-- For the zero original action, the unitized action homomorphism is the scalar algebra map of
the scalar coordinate. -/
theorem endHom_zero_apply (x : Unitization k A) :
    endHom (0 : A →ₙₐ[k] Module.End k M) x = algebraMap k (Module.End k M) x.fst := by
  ext m
  rw [endHom_apply, Module.algebraMap_end_apply, NonUnitalAlgHom.zero_apply,
    LinearMap.zero_apply, add_zero]

/-- For the zero original action, the unitized action is scalar multiplication by `x.fst`. -/
theorem zero_smul_eq (x : Unitization k A) (m : M) :
    (letI := module (0 : A →ₙₐ[k] Module.End k M); x • m) = x.fst • m := by
  rw [smul_def, endHom_zero_apply, Module.algebraMap_end_apply]

/-- For the zero original action, `A` still acts by zero after unitization. -/
theorem zero_inr_smul (a : A) (m : M) :
    (letI := module (0 : A →ₙₐ[k] Module.End k M); (a : Unitization k A) • m) = 0 := by
  rw [inr_smul, NonUnitalAlgHom.zero_apply, LinearMap.zero_apply]

end ZeroAction

/-! ### The zero action of `ℂ` on the nonzero complex vector space `ℂ` -/

section Complex

/-- The restriction of the unitized zero action of `ℂ` on `ℂ` is still the zero action. -/
theorem complex_zero_lift_symm_endHom :
    Unitization.lift.symm (endHom (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)) = 0 :=
  lift_symm_endHom 0

/-- The unitized zero action of `ℂ` on `ℂ` is multiplication by the scalar coordinate. -/
theorem complex_zero_smul (x : Unitization ℂ ℂ) (z : ℂ) :
    (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ); x • z) = x.fst * z :=
  zero_smul_eq x z

/-- The algebra unit `1 : ℂ` acts by zero, while the unit of the unitization acts by one. -/
theorem complex_zero_inr_one_smul :
    (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ); ((1 : ℂ) : Unitization ℂ ℂ) • (1 : ℂ)) = 0 ∧
      (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ); (1 : Unitization ℂ ℂ) • (1 : ℂ)) = 1 :=
  ⟨zero_inr_smul 1 1, one_smul 0 1⟩

end Complex

/-! ### Field specialization

A field `K`, a possibly noncommutative and nonunital associative `K`-algebra `A` with bilinear
multiplication, and `K`-vector spaces in independent universes. -/

section Field

variable {K : Type u} {A : Type v} {V : Type w} {W : Type x}
  [Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

example (ρ : A →ₙₐ[K] Module.End K V) (x : Unitization K A) (a : A) (c : K) (v : V) :
    letI := module ρ
    x • v = x.fst • v + ρ x.snd v ∧ (a : Unitization K A) • v = ρ a v ∧
      (inl c : Unitization K A) • v = c • v ∧ (1 : Unitization K A) • v = v :=
  ⟨smul_eq ρ x v, inr_smul ρ a v, inl_smul ρ c v, one_smul ρ v⟩

example (ρ : A →ₙₐ[K] Module.End K V) (σ : A →ₙₐ[K] Module.End K W) :
    letI := module ρ
    letI := module σ
    letI := smulCommClass' σ
    (V →ₗ[Unitization K A] W) ≃ₗ[K] intertwiners ρ σ :=
  linearMapEquiv ρ σ

example (ρ : A →ₙₐ[K] Module.End K V) :
    letI := module ρ
    letI := isScalarTower ρ
    letI := smulCommClass' ρ
    centralizer ρ ≃ₐ[K] Module.End (Unitization K A) V :=
  endAlgEquiv ρ

end Field

end CompatibleUnitization

end Langlands.Algebra
