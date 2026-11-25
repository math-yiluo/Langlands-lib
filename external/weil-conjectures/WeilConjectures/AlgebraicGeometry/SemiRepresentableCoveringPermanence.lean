/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject

/-!
# Permanence of coverings of semi-representable étale objects

Source: Stacks Project, Tag 01G4, Lemma 25.3.2
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private abbrev componentSieve {X : Scheme.{u}}
    {K L : FormalCoproduct.{w} X.Etale} (a : K ⟶ L) (j : L.I) : Sieve (L.obj j) :=
  Sieve.ofArrows (fun i : {i : K.I // a.f i = j} ↦ K.obj i.val)
    (fun i ↦ a.φ i.val ≫ eqToHom (congrArg L.obj i.property))

private theorem componentSieve_mem_iff {X : Scheme.{u}}
    {K L : FormalCoproduct.{w} X.Etale} (a : K ⟶ L) (j : L.I)
    {T : X.Etale} (h : T ⟶ L.obj j) :
    componentSieve a j h ↔
      ∃ t : (FormalCoproduct.incl X.Etale).obj T ⟶ K,
        t ≫ a = FormalCoproduct.Hom.fromIncl j h := by
  constructor
  · intro hh
    obtain ⟨i, t, ht⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hh
    refine ⟨FormalCoproduct.Hom.fromIncl i.val t, ?_⟩
    apply FormalCoproduct.hom_ext (funext fun _ ↦ i.property)
    intro _
    change (t ≫ a.φ i.val) ≫ eqToHom (congrArg L.obj i.property) = h
    simpa only [Category.assoc] using ht.symm
  · rintro ⟨t, ht⟩
    have hi : a.f (t.f PUnit.unit) = j :=
      congrFun (congrArg FormalCoproduct.Hom.f ht) PUnit.unit
    apply (Sieve.mem_ofArrows_iff _ _ _).mpr
    refine ⟨⟨t.f PUnit.unit, hi⟩, t.φ PUnit.unit, ?_⟩
    simpa [Category.assoc] using
      (((FormalCoproduct.hom_ext_iff _ _).mp ht).2 PUnit.unit).symm

/-- Coverings of semi-representable objects are stable under composition and base change.
Source: Stacks Project, Tag 01G4, Lemma 25.3.2
(auxiliary; not a blueprint node).

Proof: by def-weil-pbc-semi-representable-object, a covering is a covering family over each
index of its target. For (1), fix an index of M. Compose the family of b-components over
that index with the a-component families using lem-weil-pbc-etale-covering-composition.
The bijection sending i to (a.f i, i) identifies the resulting family with the components
of a ≫ b, so the composite is a covering. For (2),
lem-weil-pbc-semi-representable-finite-limits constructs the pullback using matching pairs
of indices and the componentwise scheme pullbacks in the étale site. Fix an index of L'.
The projections over it are the base changes of the a-components over its image in L.
By lem-weil-pbc-etale-covering-base-change, these are jointly surjective étale maps,
hence a covering family. This proves the projection is a semi-representable covering.
-/
theorem semiRepresentableCovering_comp_baseChange {X : Scheme.{u}}
    {K L : FormalCoproduct.{w} X.Etale} (a : K ⟶ L)
    (ha : IsSemiRepresentableCovering a) :
    (∀ {M : FormalCoproduct.{w} X.Etale} (b : L ⟶ M),
      IsSemiRepresentableCovering b → IsSemiRepresentableCovering (a ≫ b)) ∧
    (∀ {L' : FormalCoproduct.{w} X.Etale} (c : L' ⟶ L),
      IsSemiRepresentableCovering (pullback.fst c a : pullback c a ⟶ L')) := by
  -- Use the topology axioms on the component sieves, with lifts from one-component objects.
  constructor
  · intro M b hb n
    change componentSieve (a ≫ b) n ∈ X.smallEtaleTopology _
    refine X.smallEtaleTopology.transitive (hb n) _ ?_
    intro T h hh
    obtain ⟨t, ht⟩ := (componentSieve_mem_iff b n h).mp hh
    refine X.smallEtaleTopology.superset_covering ?_
      (X.smallEtaleTopology.pullback_stable (t.φ PUnit.unit) (ha (t.f PUnit.unit)))
    intro Z k hk
    change componentSieve a (t.f PUnit.unit) (k ≫ t.φ PUnit.unit) at hk
    obtain ⟨s, hs⟩ := (componentSieve_mem_iff a _ _).mp hk
    change componentSieve (a ≫ b) n (k ≫ h)
    apply (componentSieve_mem_iff (a ≫ b) n _).mpr
    refine ⟨s, ?_⟩
    have he : FormalCoproduct.Hom.fromIncl (t.f PUnit.unit)
        (k ≫ t.φ PUnit.unit) = (FormalCoproduct.incl X.Etale).map k ≫ t := by
      ext p <;> cases p <;> simp [FormalCoproduct.incl]
    calc
      s ≫ (a ≫ b) = (s ≫ a) ≫ b := (Category.assoc _ _ _).symm
      _ = ((FormalCoproduct.incl X.Etale).map k ≫ t) ≫ b := by rw [hs, he]
      _ = (FormalCoproduct.incl X.Etale).map k ≫
          FormalCoproduct.Hom.fromIncl n h := by rw [Category.assoc, ht]
      _ = FormalCoproduct.Hom.fromIncl n (k ≫ h) := rfl
  · intro L' c j
    change componentSieve (pullback.fst c a) j ∈ X.smallEtaleTopology _
    refine X.smallEtaleTopology.superset_covering ?_
      (X.smallEtaleTopology.pullback_stable (c.φ j) (ha (c.f j)))
    intro T h hh
    change componentSieve a (c.f j) (h ≫ c.φ j) at hh
    obtain ⟨t, ht⟩ := (componentSieve_mem_iff a _ _).mp hh
    apply (componentSieve_mem_iff (pullback.fst c a) j h).mpr
    have hc : FormalCoproduct.Hom.fromIncl j h ≫ c = t ≫ a := by
      rw [ht]
      rfl
    exact ⟨pullback.lift (FormalCoproduct.Hom.fromIncl j h) t hc,
      pullback.lift_fst _ _ _⟩

end AlgebraicGeometry.Scheme
