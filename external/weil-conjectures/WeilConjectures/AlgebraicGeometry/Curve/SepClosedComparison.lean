/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Curve.SepClosedComparisonCore
import WeilConjectures.AlgebraicGeometry.Curve.SepClosedComparisonCurve

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- A geometric comparison square over algebraically closed fields.
Source: Stacks Project, Tag 0A5E, proof (compatible algebraic closures).
(blueprint: lemma-weil-pbc-curve-separably-closed-passage-comparison)

Proof: Choose an algebraic closure K' of k'. The algebraic closure of the image of k
inside K' is an algebraically closed field K, and the two embeddings into K' commute.
Since k and k' are separably closed, K/k and K'/k' are purely inseparable algebraic
extensions. Their spectrum maps are universal homeomorphisms. Set D = C times Spec K
over Spec k and D' = C' times Spec K' over Spec k'. The projections p and p' are universal
homeomorphisms by stability under base change. Associativity of pullbacks gives the
cartesian square D' -> D over Spec K' -> Spec K and the equality p' >> iota' = a >> p.
Properness, finite type, and separatedness of b follow by base change from f. Since p is
a homeomorphism, D has the same topological Krull dimension as C, at most one; thus b
is a proper curve. This construction also applies to the empty scheme and to dimension
zero, and uses no sheaf or cohomology assertion. -/
theorem sepClosed_geometric_comparison
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (K' : Type u) (_ : Field K') (_ : IsAlgClosed K')
      (D D' : Scheme.{u}) (b : D ⟶ Spec (.of K)) (b' : D' ⟶ Spec (.of K'))
      (j : Spec (.of K') ⟶ Spec (.of K)) (a : D' ⟶ D) (p : D ⟶ C) (p' : D' ⟶ C'),
      IsCurve b ∧ IsProper b ∧ IsPullback a b' b j ∧
        IsUniversalHomeomorphism p ∧ IsUniversalHomeomorphism p' ∧ p' ≫ ι' = a ≫ p := by
  obtain ⟨K, hK, hKa, K', hK', hK'a, D, D', b, b', j, a, p, p', t, ht, hs, hp, hp', hcomm⟩ :=
    exists_sepClosed_comparison_core f h
  have : IsUniversalHomeomorphism p := hp
  obtain ⟨hb, hbp⟩ := isCurve_isProper_of_sepClosed_comparison_core f b p t ht
  exact ⟨K, hK, hKa, K', hK', hK'a, D, D', b, b', j, a, p, p', hb, hbp, hs, hp, hp', hcomm⟩

end AlgebraicGeometry.IsCurve
