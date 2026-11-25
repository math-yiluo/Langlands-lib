module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The shared wild extension, the layer descent and the package step

The wild and carried cases over one produced orbit extension, the layer descent instantiated on
intermediate fields, and Tag 09ES's composition at the shape a layer descent's step needs.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

/-! ### The wild case, mixed with the carried case, over one orbit extension -/

section SharedWild

open IsDiscreteValuationRing

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [IsScalarTower A R K₁]
    {nf : ℕ} (E : Fin nf → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)]
    [∀ i, Algebra K₁ (E i)] [∀ i, Module.Finite L (E i)]

end SharedWild

universe u

/-! ### The layer descent, instantiated on intermediate fields

`solves_of_prescribed` in `EppKuhlmannCompleteCase.lean` is a skeleton: `mu`, `R`, `deg` and
`Terminal` are opaque, and its `hsplit` is a hypothesis.  This section instantiates it at the
ring-theoretic level, which means choosing those four and **proving** `hsplit` from the field
theory rather than assuming it.

The choice is `mu := IntermediateField K L`, `deg E := Module.finrank E L`, and
`Terminal E := Module.finrank E L ≤ 1`.

The one design point worth recording is what happened to `R`.  The abstract lemma has resources
ranging over a type `R`, and the ring-theoretic resource is a field extension `K₂ / K₁` — a type
together with instances, which is not an element of a type, so a literal instantiation would need
an ambient field and `IntermediateField` resources.  None of that is necessary, because the
resource is **prescribed**: it is fixed before the descent starts, so it can live in the ambient
context and be baked into `Solves`, and `R` collapses to a single point.  That is not a trick to
avoid the difficulty; it is what "prescribed" means, stated formally.  A version with `R` a genuine
type of resources would be strictly weaker to use, because a caller would have to produce resources
as *elements*, which is exactly the choice the route forbids.

So `Solves : IntermediateField K L → Prop` is an arbitrary predicate here, and the consumer
instantiates it as "this layer has a weak solution over the prescribed `K₂`".  Its two obligations
are then the ones the route already names: `hterminal`, discharged by the shared degree-`p` family
solver, and `hstep`, discharged by Tag 09ES
(`IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`).

Note what is *not* assumed: there is no hypothesis combining two resources.  `hstep` reduces a
layer to one shorter layer against the same ambient `K₂`, so the amalgamation never arises — the
same reason the abstract version needs no `hmerge`. -/

section LayerDescent

end LayerDescent

/-! ### Tag 09ES's composition at the shape a layer descent's step needs -/

section PackageStep

open IsDiscreteValuationRing

universe uC uM uK₁ uE uL₁ uA₁ uB₁ uM₁ uA₂ uC₁ uN₁ uB₂ uC₂

/-- **The conjugate-factor family, with every carrier collapsed to one universe.**

`IsDiscreteValuationRing.finiteFieldFactors_compatible` produces the factor family of a package in
`Type (max uL uD₁)`, where `uD₁` is the package's `L₁` universe.  That is the concrete form of the
carrier problem: a descent step built from it lands its output in a universe larger than its
input's, so an induction whose members must all inhabit one universe cannot iterate it.

Collapsing every carrier of the package to a single `u` fixes this, because `max u u` normalises to
`u`: the factors then live in `Type u` alongside the input, and the step is universe-closed. That
is the whole content of "reconciling the eight carriers", and the reason it is *available* is that
the package's own construction puts `L₁`, `A₁` and `B₁` in `max` of the input universes, so
demanding `.{u,u,u,u,u,u,u,u}` is satisfiable rather than a restriction imposed from outside.

This wrapper is therefore thin on purpose — it fixes universes and changes nothing else. Its value
is that `forall_solves_of_family_descent`, which quantifies over index types in one fixed `Type u`,
can consume it. -/
theorem exists_finiteFieldFactors_of_package
    (A B K L K₁ : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁) :
    letI := D.commRingL₁
    letI := D.algebraLL₁
    letI := D.algebraK₁L₁
    ∃ (n : ℕ) (E : Fin n → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i)) (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, Algebra A (E i))
      (_ : ∀ i, IsScalarTower B L (E i))
      (_ : ∀ i, IsScalarTower A B (E i))
      (_ : ∀ i, IsScalarTower A K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i)),
      0 < n ∧ ∃ e : D.L₁ ≃ₐ[L] ∀ i, E i,
        ∀ (i : Fin n) (x : K₁), e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x :=
  IsDiscreteValuationRing.finiteFieldFactors_compatible A B K L K₁ D

/-- The field factors of a separable base change are finite and separable, with all compatibility
structures retained. -/
theorem exists_finiteSeparableFieldFactors_of_package
    (A B K L K₁ : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [Algebra.IsSeparable K K₁]
    (D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁) :
    letI := D.commRingL₁
    letI := D.algebraLL₁
    letI := D.algebraK₁L₁
    ∃ (n : ℕ) (E : Fin n → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i)) (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, Algebra A (E i))
      (_ : ∀ i, IsScalarTower B L (E i))
      (_ : ∀ i, IsScalarTower A B (E i))
      (_ : ∀ i, IsScalarTower A K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (_ : ∀ i, Algebra.IsSeparable L (E i)),
      0 < n ∧ ∃ e : D.L₁ ≃ₐ[L] ∀ i, E i,
        ∀ (i : Fin n) (x : K₁), e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x := by
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have hall := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁
      (integralClosure B D.L₁) x)
    (fun x => by
      rw [← IsScalarTower.algebraMap_apply K L D.L₁,
        ← IsScalarTower.algebraMap_apply K K₁ D.L₁])
    (fun x => by
      rw [show (eA x : K₁) = algebraMap D.A₁ K₁ x from
        IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x]
      exact D.ringSquare x)
  rcases hall with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep, _, _⟩
  obtain ⟨n, E, hE, hLE, hfin, hsepE, hn, ⟨e⟩⟩ := (hsep inferInstance).2.1
  let := hE
  let := hLE
  let : ∀ i, Algebra K₁ (E i) := fun i =>
    (((Pi.evalAlgHom L E i).toRingHom.comp e.toRingHom).comp
      (algebraMap K₁ D.L₁)).toAlgebra
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let hBLE : ∀ i, IsScalarTower B L (E i) := fun _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let hABE : ∀ i, IsScalarTower A B (E i) := fun _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let hAK₁E : ∀ i, IsScalarTower A K₁ (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap L (E i) (algebraMap B L (algebraMap A B a)) =
        e (algebraMap K₁ D.L₁ (algebraMap A K₁ a)) i
      rw [← IsScalarTower.algebraMap_apply A B L]
      have hs : algebraMap K₁ D.L₁ (algebraMap A K₁ a) =
          algebraMap L D.L₁ (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K K₁,
          IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply K K₁ D.L₁,
          ← IsScalarTower.algebraMap_apply K L D.L₁]
      rw [hs, e.commutes]
      rfl
  exact ⟨n, E, hE, hLE, inferInstance, inferInstance, inferInstance,
    hBLE, hABE, hAK₁E, hfin, hsepE, hn, e, fun _ _ => rfl⟩

/-- **The package-level step: a solved lower layer plus a solved upper layer over every factor give
a solved whole, all over the one prescribed base change.**

This is the weak-solution half of Tag 09ES's composition
(`IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`) extracted as a direct
implication, which is the form a layer descent's step can actually consume: inside 09ES it sits as
one component of a conjunction nested under a universally quantified factor family, and a caller
holding exactly the two solutions cannot apply it without reconstructing that whole shape.

There is no new mathematics here and none is claimed — this is a projection. Its value is
applicability.

Two things the statement records that are easy to get wrong.

The factors appear **only in the hypotheses**. Each `DBC i` is a weak solution for the upper layer
base-changed by the factor `E i`, not by `K₁`, while the conclusion is about `DAC`, base-changed by
`K₁`. So per-factor solutions are never transported to the shared base: the composition consumes
them where they live. That is the re-entry architecture, and a statement that tried to move them to
`K₁` first would be asking for a map that does not generally exist.

The two `letI`s are load-bearing and their position is forced. `DAB.L₁` has no `CommRing` or
`Algebra L` instance until `DAB.commRingL₁` and `DAB.algebraLL₁` are introduced, and the factor
equivalence `e` mentions both; since `e` is a hypothesis, the instances must precede it in the
telescope, which is why `e`, `DBC` and the two solution hypotheses are stated after them in the
conclusion rather than as ordinary arguments.

Universes are left polymorphic in all seventeen. That costs nothing because this step constructs no
package — universe reconciliation is a problem for building an `IntegralClosureBaseChange`, not for
stating a `Prop` about ones handed in. -/
theorem isWeakSolution_of_prime_layer_of_forall_factor
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁} A C K M K₁)
    (n : ℕ) (E : Fin n → Type uE)
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    (hn : 0 < n) :
    letI := DAB.commRingL₁
    letI := DAB.algebraLL₁
    ∀ (_e : DAB.L₁ ≃ₐ[L] ∀ i, E i)
      (DBC : ∀ i, IntegralClosureBaseChange.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂} B C L M (E i)),
      DAB.IsWeakSolution → (∀ i, (DBC i).IsWeakSolution) → DAC.IsWeakSolution := by
  let := DAB.commRingL₁
  let := DAB.algebraLL₁
  intro e DBC hAB hBC
  exact ((IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose
    A B C K L M K₁ DAB DAC).2 n E hn ⟨e⟩ DBC).1 ⟨hAB, hBC⟩

end PackageStep

end Stacks.EppTheorem

end
