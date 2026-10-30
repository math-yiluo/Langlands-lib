import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Continuous descent under actual finite full-domain refinements -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K} {V : Domain K A}
variable {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z]

/-- Compatible continuous maps on the actual component loci of a finite cover. -/
abbrev CompatibleFamily (c : FiniteCover V) (Y : Type v) [TopologicalSpace Y] :=
  {g : ∀ i : Fin c.size, C((c.obj i).locus, Y) // c.Compatible g}

namespace Refinement

variable {a b c d : FiniteCover V}

/-- Restrict a family through the selected actual full-domain arrows. -/
def pullbackFamily (r : Refinement d c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    ∀ j : Fin d.size, C((d.obj j).locus, Y) :=
  fun j => (g (r.index j)).comp (r.map j).locusMap

theorem compatible_pullbackFamily (r : Refinement d c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    d.Compatible (r.pullbackFamily g) := by
  intro i j x y h
  exact hg (r.index i) (r.index j) _ _ h

/-- Actual restriction therefore maps compatible families to compatible families. -/
def pullback (r : Refinement d c) (g : CompatibleFamily c Y) :
    CompatibleFamily d Y :=
  ⟨r.pullbackFamily g.val, r.compatible_pullbackFamily g.val g.property⟩

@[simp] theorem pullback_apply (r : Refinement d c) (g : CompatibleFamily c Y)
    (j : Fin d.size) (x : (d.obj j).locus) :
    (r.pullback g).val j x = g.val (r.index j) ((r.map j).locusMap x) := rfl

/-- Successive actual restrictions agree with restriction through their composite. -/
@[simp] theorem pullback_comp (r : Refinement a b) (s : Refinement b c)
    (g : CompatibleFamily c Y) :
    (r.comp s).pullback g = r.pullback (s.pullback g) := by
  apply Subtype.ext
  funext j
  apply ContinuousMap.ext
  intro x
  rfl

@[simp] theorem pullback_id (g : CompatibleFamily c Y) :
    (Refinement.id c).pullback g = g := by
  apply Subtype.ext
  funext j
  apply ContinuousMap.ext
  intro x
  rfl

/-- Restricting a global map through any refinement gives its finer restrictions. -/
@[simp] theorem pullbackFamily_restrict (r : Refinement d c) (f : C(V.locus, Y)) :
    r.pullbackFamily (c.restrict f) = d.restrict f := by
  funext j
  apply ContinuousMap.ext
  intro x
  rfl

/-- The concrete gluing equivalences commute with refinement restriction. -/
theorem pullback_gluingEquiv (r : Refinement d c) (f : C(V.locus, Y)) :
    r.pullback (c.gluingEquiv f) = d.gluingEquiv f := by
  apply Subtype.ext
  exact r.pullbackFamily_restrict f

/-- Refining a compatible family preserves the descended continuous map. -/
theorem glue_pullbackFamily (r : Refinement d c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    d.glue (r.pullbackFamily g) (r.compatible_pullbackFamily g hg) = c.glue g hg := by
  apply (d.glue_unique _ _ _ ?_).symm
  intro j
  change (c.restrict (c.glue g hg) (r.index j)).comp (r.map j).locusMap =
    (g (r.index j)).comp (r.map j).locusMap
  rw [c.restrict_glue]

/-- The inverse descends a finer compatible family and restricts it to the
coarser cover. Thus every chosen actual refinement gives an equivalence. -/
def pullbackEquiv (r : Refinement d c) :
    CompatibleFamily c Y ≃ CompatibleFamily d Y where
  toFun := r.pullback
  invFun g := ⟨c.restrict (d.glue g.val g.property),
    c.compatible_restrict (d.glue g.val g.property)⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    change c.restrict
      (d.glue (r.pullbackFamily g.val) (r.compatible_pullbackFamily g.val g.property)) i =
      g.val i
    rw [r.glue_pullbackFamily g.val g.property, c.restrict_glue g.val g.property]
  right_inv g := by
    apply Subtype.ext
    change r.pullbackFamily (c.restrict (d.glue g.val g.property)) = g.val
    rw [r.pullbackFamily_restrict]
    funext j
    exact d.restrict_glue g.val g.property j

@[simp] theorem pullbackEquiv_apply (r : Refinement d c) (g : CompatibleFamily c Y) :
    r.pullbackEquiv g = r.pullback g := rfl

/-- Different choices of coarser component induce the same map on compatible
families, although the underlying refinement arrows need not be equal. -/
theorem pullback_eq (r s : Refinement d c) (g : CompatibleFamily c Y) :
    r.pullback g = s.pullback g := by
  apply (d.gluingEquiv (Y := Y)).symm.injective
  change d.glue (r.pullbackFamily g.val) (r.compatible_pullbackFamily g.val g.property) =
    d.glue (s.pullbackFamily g.val) (s.compatible_pullbackFamily g.val g.property)
  rw [r.glue_pullbackFamily g.val g.property, s.glue_pullbackFamily g.val g.property]

/-- Refinement restriction commutes with continuous maps of the target space. -/
theorem pullbackFamily_postcomp (r : Refinement d c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (p : C(Y, Z)) :
    r.pullbackFamily (fun i => p.comp (g i)) =
      fun j => p.comp (r.pullbackFamily g j) := by
  funext j
  apply ContinuousMap.ext
  intro x
  rfl

end Refinement

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
