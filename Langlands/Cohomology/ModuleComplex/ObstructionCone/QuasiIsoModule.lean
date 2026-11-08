import Langlands.Cohomology.ModuleComplex.BoundedFlatQuasiIsoBaseChangeProof
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Bounded flat quasi-isomorphisms remain quasi-isomorphisms after tensoring with a module

The published `boundedFlatQuasiIsoBaseChange` treats base change to algebras. A module `N`
is an `A`-linear retract of the trivial square-zero extension `A ⊕ N`, which gives the
corresponding statement for `- ⊗[A] N` in positive degrees.
-/

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone.QuasiIsoModule

variable {A : Type u} [CommRing A] (N : Type u) [AddCommGroup N] [Module A N]

/-- The right `Aᵐᵒᵖ`-action on `N` equal to the given action, for commutative `A`. -/
abbrev opModule : Module Aᵐᵒᵖ N := Module.compHom N (RingEquiv.toOpposite A).symm.toRingHom

attribute [local instance] opModule

/-- The two actions of `A` on `N` agree. -/
abbrev opCentral : IsCentralScalar A N := ⟨fun _ _ => rfl⟩

attribute [local instance] opCentral

variable (A) in
/-- The trivial square-zero extension `A ⊕ N`. -/
abbrev Ext := TrivSqZeroExt A N

/-- The inclusion `X ⊗ N → (A ⊕ N) ⊗ X`. -/
def incl (X : Type u) [AddCommGroup X] [Module A X] : X ⊗[A] N →ₗ[A] Ext A N ⊗[A] X :=
  (TensorProduct.comm A X (Ext A N)).toLinearMap ∘ₗ (TrivSqZeroExt.inrHom A N).lTensor X

/-- The retraction `(A ⊕ N) ⊗ X → X ⊗ N`. -/
def retr (X : Type u) [AddCommGroup X] [Module A X] : Ext A N ⊗[A] X →ₗ[A] X ⊗[A] N :=
  (TrivSqZeroExt.sndHom A N).lTensor X ∘ₗ (TensorProduct.comm A (Ext A N) X).toLinearMap

variable {N}

lemma retr_incl {X : Type u} [AddCommGroup X] [Module A X] (t : X ⊗[A] N) :
    retr N X (incl N X t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul x n => simp [incl, retr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

lemma baseChange_incl {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (f : X →ₗ[A] Y) (t : X ⊗[A] N) :
    f.baseChange (Ext A N) (incl N X t) = incl N Y (f.rTensor N t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x n => simp [incl]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

lemma retr_baseChange {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (f : X →ₗ[A] Y) (t : Ext A N ⊗[A] X) :
    retr N Y (f.baseChange (Ext A N) t) = f.rTensor N (retr N X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s x => simp [retr]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]


/-- A bounded quasi-isomorphism of complexes of flat modules induces isomorphisms on positive
degree cohomology after tensoring with any module `N` on the right. -/
theorem rTensor_quasiIso
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)] [∀ i, Module.Flat A (K i)]
    (δ : ∀ i, K i →ₗ[A] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)] [∀ i, Module.Flat A (C i)]
    (d : ∀ i, C i →ₗ[A] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hKbdd : ∀ i, n < i → Subsingleton (K i)) (hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[A] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (N : Type u) [AddCommGroup N] [Module A N] :
    (∀ (i : ℕ) (x : K (i + 1) ⊗[A] N), (δ (i + 1)).rTensor N x = 0 →
      (φ (i + 1)).rTensor N x ∈ LinearMap.range ((d i).rTensor N) →
        x ∈ LinearMap.range ((δ i).rTensor N)) ∧
    (∀ (i : ℕ) (y : C (i + 1) ⊗[A] N), (d (i + 1)).rTensor N y = 0 →
      ∃ x : K (i + 1) ⊗[A] N, (δ (i + 1)).rTensor N x = 0 ∧
        (φ (i + 1)).rTensor N x - y ∈ LinearMap.range ((d i).rTensor N)) := by
  obtain ⟨-, -, hinjS, hsurjS⟩ := boundedFlatQuasiIsoBaseChange A K δ hδδ C d hdd n hKbdd hCbdd
    φ hφ h0inj h0surj hinj hsurj (Ext A N)
  constructor
  · intro i x hx hφx
    obtain ⟨y, hy⟩ := hφx
    have h1 : (δ (i + 1)).baseChange (Ext A N) (incl N _ x) = 0 := by
      rw [baseChange_incl, hx, map_zero]
    have h2 : (φ (i + 1)).baseChange (Ext A N) (incl N _ x) ∈
        LinearMap.range ((d i).baseChange (Ext A N)) :=
      ⟨incl N _ y, by rw [baseChange_incl, baseChange_incl, hy]⟩
    obtain ⟨t, ht⟩ := hinjS i _ h1 h2
    refine ⟨retr N _ t, ?_⟩
    rw [← retr_baseChange, ht, retr_incl]
  · intro i y hy
    have h1 : (d (i + 1)).baseChange (Ext A N) (incl N _ y) = 0 := by
      rw [baseChange_incl, hy, map_zero]
    obtain ⟨x', hx', s, hs⟩ := hsurjS i _ h1
    refine ⟨retr N _ x', by rw [← retr_baseChange, hx', map_zero], retr N _ s, ?_⟩
    rw [← retr_baseChange, hs, map_sub, retr_incl, retr_baseChange]

end Langlands.Cohomology.ModuleComplex.ObstructionCone.QuasiIsoModule
