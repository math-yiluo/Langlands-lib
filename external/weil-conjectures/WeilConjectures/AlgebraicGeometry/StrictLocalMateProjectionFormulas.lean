/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionData
import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceSections
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # Projection restriction formulas for the strict-local mate

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Derived neighbourhood sections identify with stage hypercohomology, compatibly
with transition pullbacks and with projection restriction for the derived mate.
This does not assert that the canonical source cocone is colimiting.
Source: Stacks, Tag 03Q9, final injective-complex paragraph; Tag 03Q8
(blueprint: lem-weil-pbc-strict-local-mate-projection-formulas).

Proof: choose a bounded below injective representative J of K. Under derived adjunction,
Hom(Z[V][0], (Rf_*K)[n]) is Hom(f^*Z[V][0], K[n]); the free sheaf f^*Z[V] corepresents
sections on V ×_S X. Restriction along its etale projection to X preserves injectives,
so this derived Hom is the n-th hypercohomology of the restricted complex J.
These identifications provide e. Precomposition by a neighbourhood morphism is the
restriction of sections; express this restriction using the derived unit, Leray,
and the exact inverse-image composition isomorphism to obtain transition.
For the limit projection, evaluate the adjunction mate on J: its sections map is
inverse-image restriction along the pullback square. The canonical cohomology germ
map is taking the homology class of that same section. The first leg equation for Q
identifies the representative germ restriction with the limit projection. Exact
inverse image commutes with homology, and exact strict-local sections followed by
Leray give strictLocalBaseChangeTargetIso. Thus the two composites agree on every
derived section, proving restriction. Naturality of all the comparisons transports
the formulas from J to K. No continuity or invertibility of the mate is used. -/
theorem nonempty_strictLocalMateProjectionData {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s) :
    Nonempty (StrictLocalMateProjectionData f s K n Q) := by
  classical
  obtain ⟨b, hb⟩ := K.property
  let : K.IsGE b := (K.isGE_ι_obj_iff b).1 hb
  obtain ⟨J, _, ⟨qJ⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K b
  let q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
    DerivedCategory.Plus.ι.mapIso qJ.symm
  obtain ⟨e, ht, hr⟩ := exists_strictLocalInjectiveSourceSections f s K n Q J q
  obtain ⟨he, htransition, hrestriction⟩ :=
    injectiveSections_strictLocal_comparison f s K n Q J q
  let := he
  let E := fun i ↦ e i ≪≫ asIso (representativeSectionsComparison
    ((strictLocalNeighbourhoodProjection f s).app i) q n)
  refine ⟨{ e := E, transition := ?_, restriction := ?_ }⟩
  · intro i j a
    have h := htransition a
    refine (ht a).trans ?_
    dsimp only [E]
    simp only [Iso.trans_hom, Iso.trans_inv, asIso_hom, asIso_inv] at h ⊢
    simp only [Category.assoc] at h ⊢
    rw [reassoc_of% h]
    simp only [IsIso.hom_inv_id_assoc]
  · intro i
    have h := hrestriction i
    refine (hr i).trans ?_
    dsimp only [E]
    simp only [Iso.trans_hom, Iso.trans_inv, asIso_hom] at h ⊢
    simp only [Category.assoc] at h ⊢
    rw [reassoc_of% h]

end AlgebraicGeometry.Etale
