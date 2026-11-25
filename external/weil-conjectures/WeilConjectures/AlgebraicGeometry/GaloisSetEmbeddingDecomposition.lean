/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctor
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.MulAction

/-!
# Decomposition of continuous Galois sets into field embedding sets

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

/-- A continuous discrete Galois set is a disjoint union of finite separable embedding sets.
Source: Stacks Project, Tag 03QR, construction of the inverse functor.
(blueprint: lem-exc-galois-set-embedding-decomposition).

Proof: Take I to be the orbit quotient of the underlying action, in the same universe.
For each orbit choose a representative. Its stabilizer is open because the orbit map
is continuous and the singleton of the representative is open. The Galois group is
compact, so its quotient by this stabilizer is finite; the orbit-stabilizer equivalence
makes the orbit finite. Apply the finite Galois classification to that nonempty
transitive orbit. It yields a finite separable intermediate field E i and an equivariant
bijection from the orbit to the K-embeddings of E i in Ksep. Combine these bijections
with the canonical equivalence of the original set with the sum of its orbits.
If the original set is empty, I is empty and the sum is empty. -/
theorem galoisSet_embedding_decomposition
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (M : DiscreteContAction (Type u) (Gal(Ksep/K))) :
    ∃ (I : Type u) (E : I → IntermediateField K Ksep),
      (∀ i, FiniteDimensional K (E i)) ∧
      (∀ i, Algebra.IsSeparable K (E i)) ∧
      ∃ e : M.obj.obj.V ≃ (Σ i, E i →ₐ[K] Ksep),
        ∀ (g : Gal(Ksep/K)) (x : M.obj.obj.V),
          e (M.obj.obj.ρ g x) = ⟨(e x).1, g.toAlgHom.comp (e x).2⟩  := by
  classical
  let G := Gal(Ksep/K)
  let X := (forget₂ (Action (Type u) G) TopCat).obj M.obj.obj
  let _ : MulAction G X :=
    inferInstanceAs (MulAction G ((forget₂ (Action (Type u) G) TopCat).obj M.obj.obj))
  have : ContinuousSMul G X := M.obj.property
  have : DiscreteTopology X := inferInstanceAs (DiscreteTopology ((forget₂ _ TopCat).obj M))
  let I := MulAction.orbitRel.Quotient G X
  have hfinite (i : I) : Finite i.orbit := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out i Quotient.out_eq']
    have : Finite (G ⧸ MulAction.stabilizer G i.out) :=
      Subgroup.quotient_finite_of_isOpen _ (stabilizer_isOpen G i.out)
    exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G i.out).symm
  let := hfinite
  have hclass :=
    (FieldTheory.finite_separable_extension_galois_classification K Ksep K K).2.1
  have hreal (i : I) :
      ∃ E : IntermediateField K Ksep,
        FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
          ∃ e : i.orbit ≃ (E →ₐ[K] Ksep),
            ∀ (g : G) (y : i.orbit), e (g • y) = g.toAlgHom.comp (e y) := by
    apply hclass i.orbit (MulAction.orbitRel.Quotient.nonempty_orbit i).to_subtype inferInstance
    intro y
    have hy := stabilizer_isOpen G y.val
    convert hy using 1
    ext g
    change (g • y = y) ↔ (g • y.val = y.val)
    exact Subtype.ext_iff
  choose E hdim hsep e he using hreal
  let q := MulAction.selfEquivSigmaOrbits' G X
  have hq (i : I) (y : i.orbit) : q y.val = ⟨i, y⟩ := q.apply_symm_apply ⟨i, y⟩
  let t := q.trans (Equiv.sigmaCongrRight e)
  refine ⟨I, E, hdim, hsep, t, ?_⟩
  change ∀ (g : G) (x : X), t (g • x) = ⟨(t x).1, g.toAlgHom.comp (t x).2⟩
  intro g x
  have hqx : (q x).2.val = x := rfl
  have hqgx : q (g • x) = ⟨(q x).1, g • (q x).2⟩ := by
    rw [← hqx]
    exact hq (q x).1 (g • (q x).2)
  change (Equiv.sigmaCongrRight e) (q (g • x)) = _
  rw [hqgx]
  change (⟨(q x).1, e (q x).1 (g • (q x).2)⟩ : Σ i, E i →ₐ[K] Ksep) =
    ⟨(q x).1, g.toAlgHom.comp (e (q x).1 (q x).2)⟩
  rw [he]

end AlgebraicGeometry
