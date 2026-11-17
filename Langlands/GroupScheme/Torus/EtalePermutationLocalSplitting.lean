import Langlands.GroupScheme.Torus.EtalePermutationCoefficientDescent

/-! # Local coefficient splittings of permutation descent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.AlgebraicGeometry.FiniteProductCoefficients

variable {α : Type u} [Finite α] (R : Type u) [CommRing R]
  (A : α → Type u) [∀ a, CommRing (A a)] [∀ a, Algebra R (A a)]
  (E : Type u) [CommRing E] [Algebra R E]

/-- Finite left-product tensor distribution retains the whole product-base
algebra action, with componentwise scalar action on the target. -/
def leftTensorEquiv : ((∀ a, A a) ⊗[R] E) ≃ₐ[∀ a, A a] (∀ a, A a ⊗[R] E) := by
  classical
  letI := Fintype.ofFinite α
  let e := (Algebra.TensorProduct.comm R (∀ a, A a) E).trans
    ((Algebra.TensorProduct.piRight R R E A).trans
      (AlgEquiv.piCongrRight fun a => Algebra.TensorProduct.comm R E (A a)))
  exact { e.toRingEquiv with commutes' := fun _ => rfl }

@[simp] theorem leftTensorEquiv_tmul (x : ∀ a, A a) (e : E) (a : α) :
    leftTensorEquiv R A E (x ⊗ₜ[R] e) a = x a ⊗ₜ[R] e := rfl

omit [Finite α] in
/-- Bijectivity of a componentwise zero-preserving map implies bijectivity of
each component. No nonzero or nonempty-ring assumption is needed. -/
theorem bijective_component {X Y : α → Type u} [∀ a, Zero (X a)] [∀ a, Zero (Y a)]
    (g : ∀ a, X a → Y a) (hg : ∀ a, g a 0 = 0)
    (h : Function.Bijective (fun x : ∀ a, X a => fun a => g a (x a))) (a : α) :
    Function.Bijective (g a) := by
  classical
  constructor
  · intro x y hxy
    have he : (fun b => g b ((Pi.single a x) b)) = (fun b => g b ((Pi.single a y) b)) := by
      funext b
      by_cases hb : b = a
      · subst b
        simpa using hxy
      · simp [hb, hg]
    simpa using congrFun (h.injective he) a
  · intro y
    obtain ⟨x, hx⟩ := h.surjective (Pi.single a y)
    exact ⟨x a, by simpa using congrFun hx a⟩

end Langlands.AlgebraicGeometry.FiniteProductCoefficients

namespace Langlands.GroupScheme.FiniteAffinePermutationCoefficients

open EtalePermutationAtlas
open Langlands.AlgebraicGeometry
open AffineCoverCoefficientTensors

variable {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S}
  {α : Type u} [Finite α] (U : α → Scheme.{u}) [∀ a, IsAffine (U a)]
  (f : ∀ a, U a ⟶ S) (I : α → Type u) [∀ a, Finite (I a)]
  (e : ∀ a, (GroupScheme.baseChange (f a)).obj D ≅ splitTorus (U a) (I a))
  (H : ∀ a b, LocallyPermutes (f a) (f b) (e a) (e b))

/-- The invariant algebra's scalar extension to one affine chart, mapped into
that chart's actual coordinate function algebra. -/
def localDescentHom (a : α) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    Γ(U a, ⊤) ⊗[Γ(S, ⊤)] (coaction U f I e H).invariants →ₐ[Γ(U a, ⊤)]
      (I a → Γ(U a, ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  exact AlgHom.liftEquiv Γ(S, ⊤) Γ(U a, ⊤) (coaction U f I e H).invariants
    (I a → Γ(U a, ⊤))
    ((Pi.evalAlgHom Γ(S, ⊤) (fun a => I a → Γ(U a, ⊤)) a).comp
      (coaction U f I e H).invariants.val)

@[simp] theorem localDescentHom_tmul (a : α) (x : Γ(U a, ⊤))
    (c : (coaction U f I e H).invariants) (i : I a) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    localDescentHom U f I e H a (x ⊗ₜ[Γ(S, ⊤)] c) i = x * c.val a i := rfl

/-- The local coefficient map is the component of the global descent map. -/
theorem localDescentHom_component
    (z : letI (a : α) := (f a).appTop.hom.toAlgebra
      (∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (coaction U f I e H).invariants)
    (a : α) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    localDescentHom U f I e H a
        (FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤))
          (coaction U f I e H).invariants z a) =
      (coaction U f I e H).descentHom z a := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul x c => rfl
  | add x y hx hy =>
    have hl : FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤))
        (coaction U f I e H).invariants (x + y) =
        FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤))
          (coaction U f I e H).invariants x +
        FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤))
          (coaction U f I e H).invariants y :=
      (FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤))
        (coaction U f I e H).invariants).map_add' _ _
    have hd : (coaction U f I e H).descentHom (x + y) =
        (coaction U f I e H).descentHom x + (coaction U f I e H).descentHom y :=
      (coaction U f I e H).descentHom.map_add' _ _
    rw [hl, hd]
    change localDescentHom U f I e H a (_ + _) = _ + _
    exact ((localDescentHom U f I e H a).map_add' _ _).trans (congrArg₂ (· + ·) hx hy)

/-- The component coefficient map is an isomorphism after faithfully flat
jointly surjective chart extension. -/
theorem localDescentHom_bijective [∀ a, Flat (f a)] [Surjective (Sigma.desc f)] (a : α) :
    Function.Bijective (localDescentHom U f I e H a) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  let A := coaction U f I e H
  let L := FiniteProductCoefficients.leftTensorEquiv Γ(S, ⊤) (fun a => Γ(U a, ⊤)) A.invariants
  let g := fun t : ∀ a, Γ(U a, ⊤) ⊗[Γ(S, ⊤)] A.invariants =>
    fun a => localDescentHom U f I e H a (t a)
  have hg : g = fun t => A.descentEquiv (coverRingMap_faithfullyFlat U f) (L.symm t) := by
    funext t a
    have hc := localDescentHom_component U f I e H (L.symm t) a
    change localDescentHom U f I e H a (t a) = A.descentHom (L.symm t) a
    change localDescentHom U f I e H a (L (L.symm t) a) = A.descentHom (L.symm t) a at hc
    simpa only [AlgEquiv.apply_symm_apply] using hc
  have hbij : Function.Bijective g := by
    rw [hg]
    exact (A.descentEquiv (coverRingMap_faithfullyFlat U f)).bijective.comp L.symm.bijective
  exact FiniteProductCoefficients.bijective_component
    (fun a => localDescentHom U f I e H a) (fun a => map_zero _) hbij a

/-- The actual local coefficient splitting supplied by permutation descent. -/
def localDescentEquiv [∀ a, Flat (f a)] [Surjective (Sigma.desc f)] (a : α) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    Γ(U a, ⊤) ⊗[Γ(S, ⊤)] (coaction U f I e H).invariants ≃ₐ[Γ(U a, ⊤)]
      (I a → Γ(U a, ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact AlgEquiv.ofBijective (localDescentHom U f I e H a)
    (localDescentHom_bijective U f I e H a)

@[simp] theorem localDescentEquiv_tmul [∀ a, Flat (f a)] [Surjective (Sigma.desc f)]
    (a : α) (x : Γ(U a, ⊤)) (c : (coaction U f I e H).invariants) (i : I a) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    localDescentEquiv U f I e H a (x ⊗ₜ[Γ(S, ⊤)] c) i = x * c.val a i := rfl

/-- An invariant coefficient family's chart values agree under the actual
transition on every overlap. -/
theorem invariant_overlap (c : (coaction U f I e H).invariants) (a b : α) (j : I b) :
    overlapEquiv U f I e H a b
      (fun i => (pullback.fst (f a) (f b)).appTop.hom (c.val a i)) j =
        (pullback.snd (f a) (f b)).appTop.hom (c.val b j) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  have hc := ((coaction U f I e H).mem_invariants c.val).mp c.property
  change tensorMap U f I e H c.val = (1 : ∀ a, Γ(U a, ⊤)) ⊗ₜ[Γ(S, ⊤)] c.val at hc
  have hi := congrArg (fun z => coefficientTensorEquiv U f I z a b j) hc
  simpa only [tensorMap_formula, coefficientTensorEquiv_tmul, Pi.one_apply, map_one, one_mul] using hi

end Langlands.GroupScheme.FiniteAffinePermutationCoefficients
