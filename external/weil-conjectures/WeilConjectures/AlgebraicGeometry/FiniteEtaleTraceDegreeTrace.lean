/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTrace
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDegreeSplitAt
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitComponent

/-!
# Trace after restriction for a finite étale morphism of fixed degree

Source: Stacks Project, Section 03SH (section-trace-method), the paragraph following
Definition 03SE; local splitting is Lemma 04HN (lemma-finite-etale-etale-local).
(blueprint: lem-weil-pbc-finite-etale-trace-degree-trace).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Restriction followed by trace is multiplication by the prescribed finite locally free
 degree. Source: Stacks Project, Section 03SH (section-trace-method), paragraph following
Definition 03SE (blueprint: lem-weil-pbc-finite-etale-trace-degree-trace).

Proof:
1. A geometric fibre over an algebraically closed field Ω has dimension d: choose the unique
point z of Spec Ω, use `fiberDegree_eq_finrankΓ` and `fiberDegree_of_isPullback`, then the
assumed `IsFiniteLocallyFreeOfDegree.fiberDegree_eq`. The existing geometric fibre theorem
`exists_overIso_sigma_of_isSepClosed` splits it into n copies of Spec Ω with n equal to that
dimension. Each Spec Ω has one point, so the fibre has d points.
2. At each x of X, Lemma 04HN supplies an étale neighbourhood g : U → X with a point u
mapping to x and a finite clopen splitting of Y ×_X U into pieces isomorphic to U. Choose
an algebraic closure Ω of κ(u). Base change the splitting to Spec Ω. Cartesian pasting
identifies its coproduct with the geometric fibre of f at Spec Ω → U → X. Thus its number
of pieces is d by step 1, and reindexing yields d pieces.
3. The inverse-image restriction isomorphism identifies the adjunction unit at a site
object W with restriction along W ×_X Y → W. Pasting identifies this projection after
localizing at g with W ×_U (Y ×_X U) → W. Property (1) of the chosen trace family in
`existsUnique_finiteEtaleTrace` identifies the localized trace with the trace of this
base change, through the same restriction isomorphisms.
4. For the split base change, the sheaf condition identifies sections over the disjoint
union with the product of the d groups of sections. Restriction is the diagonal since
each section of the projection composes with that projection to the identity. Property
(2) of `existsUnique_finiteEtaleTrace` says trace is the sum of restrictions along these
sections. Hence the composite sends s to the sum of d copies of s, namely d • s.
The argument includes d = 0: the empty covering forces sections of the empty scheme to
be the zero group, and the empty sum is zero.
5. The neighbourhoods g are jointly surjective because u maps to x. Pulling this covering
back to every W gives an étale covering W ×_X U → W. Naturality and step 3 identify the
restrictions of the difference between the composite and d times the identity with the
zero maps computed in step 4. Sheaf separatedness makes the difference zero on W. Equality
on every W proves equality of sheaf morphisms. If X is empty, the empty covering already
forces every group of sections to be zero, so no nonemptiness assumption is necessary. -/
theorem finiteEtaleTrace_comp_restriction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d] :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F := by
  classical
  intro F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  obtain ⟨W⟩ := W
  let C := finiteEtaleRestriction f F ≫ finiteEtaleTrace f F
  have hlocal (w : W.left) := exists_finiteEtale_degree_split_at f d W w
  choose V a v hv D i hc hi hp using hlocal
  have hcover : Sieve.ofArrows V a ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
    apply Set.eq_univ_of_forall
    intro w
    exact Set.mem_iUnion.mpr ⟨w, v w, hv w⟩
  apply F.property.hom_ext_ofArrows a hcover
  intro w
  have hs := finiteEtaleTrace_comp_restriction_app_of_split f F (V w)
    (ULift.{u} (Fin d)) (D w) (i w) (hc w) (hi w) (hp w)
  change C.hom.app (Opposite.op W) ≫ F.obj.map (a w).op =
    (d • 𝟙 F).hom.app (Opposite.op W) ≫ F.obj.map (a w).op
  rw [← C.hom.naturality]
  simp only [Fintype.card_ulift, Fintype.card_fin] at hs
  rw [show C.hom.app (Opposite.op (V w)) = d • 𝟙 (F.obj.obj (Opposite.op (V w))) from hs]
  change F.obj.map (a w).op ≫ (d • 𝟙 (F.obj.obj (Opposite.op (V w)))) =
    (d • (𝟙 F.obj)).app (Opposite.op W) ≫ F.obj.map (a w).op
  simp

end AlgebraicGeometry.Etale
