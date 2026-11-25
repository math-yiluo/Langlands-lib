/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Dual invariant functionals and coinvariants

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`sk-l-dl-a1-endpoints.proof.md`, displayed top-cohomology formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedCurve

variable {R : Type u} [Field R] {P : Type v} [Monoid P]
  {V W : Type w} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Functionals that kill all monodromy differences.
Source: latest blueprint, `sk-lem-wrp-hc2.proof.md`, dual invariants
(blueprint: lem-per-invariant-forms-coinvariants). -/
def invariantForms (ρ : Representation R P V) : Submodule R (Module.Dual R V) where
  carrier := { f | ∀ g v, f (ρ g v) = f v }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg p v
    exact congrArg₂ (· + ·) (hf p v) (hg p v)
  smul_mem' := by
    intro r f hf p v
    exact congrArg (r • ·) (hf p v)

/-- Pullback from the quotient identifies its dual with invariant functionals.
Source: latest blueprint, `sk-lem-wrp-hc2.proof.md`, dual invariants
(blueprint: lem-per-invariant-forms-coinvariants).

Proof: pull back along the coinvariant quotient. Conversely an invariant
functional descends by the universal property of that quotient. The two composites
are identities by surjectivity of the quotient map. This needs no semisimplicity. -/
def coinvariantDualEquiv (ρ : Representation R P V) :
    Module.Dual R (Representation.Coinvariants ρ) ≃ₗ[R] invariantForms ρ where
  toFun f := ⟨f.comp (Representation.Coinvariants.mk ρ), by
    intro g v
    simp only [LinearMap.comp_apply, Representation.Coinvariants.mk_self_apply]⟩
  invFun f := Representation.Coinvariants.lift ρ f.val
    (fun g ↦ LinearMap.ext (fun v ↦ f.property g v))
  left_inv f := by ext v; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

/-- The dual of invariant functionals is the coinvariant quotient itself.
Source: latest blueprint, `sk-lem-wrp-hc2.proof.md`, second paragraph
(blueprint: lem-per-invariant-forms-coinvariants).

Proof: dualize the preceding quotient-pullback equivalence and use finite
vector-space biduality for the quotient. This includes rank zero. -/
def dualInvariantFormsEquiv (ρ : Representation R P V) [Module.Finite R V] :
    Module.Dual R (invariantForms ρ) ≃ₗ[R] Representation.Coinvariants ρ :=
  (coinvariantDualEquiv ρ).dualMap.trans
    (Module.evalEquiv R (Representation.Coinvariants ρ)).symm

/-- Evaluation characterizes the preceding equivalence without choosing a basis.
Source: latest blueprint, evaluation in the top-coinvariant formula
(blueprint: lem-per-invariant-forms-coinvariants). -/
theorem dualInvariantFormsEquiv_apply [Module.Finite R V]
    (ρ : Representation R P V) (z : Module.Dual R (invariantForms ρ))
    (f : Module.Dual R (Representation.Coinvariants ρ)) :
    f (dualInvariantFormsEquiv ρ z) = z (coinvariantDualEquiv ρ f) := by
  simp [dualInvariantFormsEquiv]

/-- Equivariant maps act contravariantly on invariant functionals.
Source: latest blueprint, naturality of top coinvariants
(blueprint: lem-per-invariant-forms-coinvariants). -/
def invariantFormsPullback {ρ : Representation R P V} {σ : Representation R P W}
    (q : Representation.IntertwiningMap ρ σ) : invariantForms σ →ₗ[R] invariantForms ρ where
  toFun f := ⟨f.val.comp q.toLinearMap, by
    intro g v
    change f.val (q (ρ g v)) = f.val (q v)
    rw [q.isIntertwining, f.property]⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

/-- The quotient-dual identification commutes with every equivariant linear map.
Source: latest blueprint, canonicality of the top-coinvariant formula
(blueprint: lem-per-invariant-forms-coinvariants).

Proof: evaluate both sides against any functional on the target coinvariants.
The quotient-pullback equivalence turns this into equality of functionals on the
original representation, where it is simply associativity of precomposition.
The dual separates points, so the two coinvariants coincide. -/
theorem dualInvariantFormsEquiv_natural [Module.Finite R V] [Module.Finite R W]
    {ρ : Representation R P V} {σ : Representation R P W}
    (q : Representation.IntertwiningMap ρ σ) (z : Module.Dual R (invariantForms ρ)) :
    dualInvariantFormsEquiv σ ((invariantFormsPullback q).dualMap z) =
      Representation.Coinvariants.map ρ σ q (dualInvariantFormsEquiv ρ z) := by
  apply (Module.evalEquiv R (Representation.Coinvariants σ)).injective
  apply LinearMap.ext
  intro f
  change f (dualInvariantFormsEquiv σ ((invariantFormsPullback q).dualMap z)) = _
  rw [dualInvariantFormsEquiv_apply]
  change z (invariantFormsPullback q (coinvariantDualEquiv σ f)) =
    (f.comp (Representation.Coinvariants.map ρ σ q)) (dualInvariantFormsEquiv ρ z)
  rw [dualInvariantFormsEquiv_apply]
  congr 1

/-- Tensoring the invariant-dual equivalence by any coefficient module gives the
coinvariant identification, without choosing a basis of that module.
Source: latest blueprint, the negative Tate line in the top-coinvariant formula
(blueprint: lem-per-invariant-forms-coinvariants). -/
def dualInvariantFormsTensorIso [Module.Finite R V]
    (ρ : Representation R P V) (T : ModuleCat.{max u w} R) :
    ModuleCat.of R (Module.Dual R (invariantForms ρ) ⊗[R] T) ≅
      ModuleCat.of R (Representation.Coinvariants ρ ⊗[R] T) :=
  ((dualInvariantFormsEquiv ρ).rTensor T).toModuleIso

/-- The tensor identification commutes with every equivariant map.
Source: latest blueprint, naturality of the Tate-twisted coinvariant formula
(blueprint: lem-per-invariant-forms-coinvariants).

Proof: pure tensors generate the tensor product. On a pure tensor the assertion
is the naturality of the double-dual quotient identification in the first factor,
with the identity on the second factor. -/
theorem dualInvariantFormsTensorIso_natural [Module.Finite R V] [Module.Finite R W]
    {ρ : Representation R P V} {σ : Representation R P W}
    (q : Representation.IntertwiningMap ρ σ) (T : ModuleCat.{max u w} R) :
    ModuleCat.ofHom (TensorProduct.map (invariantFormsPullback q).dualMap
        (LinearMap.id : T →ₗ[R] T)) ≫ (dualInvariantFormsTensorIso σ T).hom =
      (dualInvariantFormsTensorIso ρ T).hom ≫
        ModuleCat.ofHom (TensorProduct.map (Representation.Coinvariants.map ρ σ q)
          (LinearMap.id : T →ₗ[R] T)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro t
  change dualInvariantFormsEquiv σ ((invariantFormsPullback q).dualMap z) ⊗ₜ[R] t =
    Representation.Coinvariants.map ρ σ q (dualInvariantFormsEquiv ρ z) ⊗ₜ[R] t
  rw [dualInvariantFormsEquiv_natural]

end AlgebraicGeometry.ProEtale.CondensedCurve
