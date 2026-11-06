import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteCoverIdealLocality
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Closed ideals under refinement of finite full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A}

/-- Intersect a finite cover with an actual full subdomain of its target.
The restriction maps are the original first intersection projections. -/
def interCover (c : FiniteCover U) (V : Domain K A) (f : V ⟶ U) : FiniteCover V where
  size := c.size
  obj j := V.inter (c.obj j)
  map j := V.interLeft (c.obj j)
  covers x hx := by
    obtain ⟨j, hj⟩ := c.covers x (f.subset hx)
    exact ⟨j, hx, hj⟩

/-- Pairwise compatibility implies equality after every actual full-domain
test into two components. -/
theorem IdealCompatible.on_test {c : FiniteCover U}
    {I : ∀ i : Fin c.size, Ideal (c.obj i).algebra} (hI : c.IdealCompatible I)
    (i j : Fin c.size) (W : Domain K A) (f : W ⟶ c.obj i) (g : W ⟶ c.obj j) :
    f.restriction.closedIdealMap (I i) = g.restriction.closedIdealMap (I j) := by
  let p := Domain.interLift f g
  have hf : f.restriction = p.restriction.comp
      ((c.obj i).interLeft (c.obj j)).restriction :=
    congrArg Inclusion.restriction (Domain.interLift_left f g).symm
  have hg : g.restriction = p.restriction.comp
      ((c.obj i).interRight (c.obj j)).restriction :=
    congrArg Inclusion.restriction (Domain.interLift_right f g).symm
  rw [hf, hg, ← BoundedAlgHom.closedIdealMap_comp, ← BoundedAlgHom.closedIdealMap_comp,
    hI i j]

namespace Refinement

variable {c d : FiniteCover U} (r : Refinement d c)

/-- Closedly extend each coarse ideal along its chosen actual refinement map. -/
def idealFamily (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) :
    ∀ j : Fin d.size, Ideal (d.obj j).algebra :=
  fun j => (r.map j).restriction.closedIdealMap (I (r.index j))

/-- The refined ideals are compatible on all actual intersections. -/
theorem idealFamily_compatible
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) (hI : c.IdealCompatible I) :
    d.IdealCompatible (r.idealFamily I) := by
  intro j k
  rw [idealFamily, idealFamily, BoundedAlgHom.closedIdealMap_comp,
    BoundedAlgHom.closedIdealMap_comp]
  exact hI.on_test (r.index j) (r.index k) ((d.obj j).inter (d.obj k))
    ((d.obj j).interLeft (d.obj k) ≫ r.map j)
    ((d.obj j).interRight (d.obj k) ≫ r.map k)

/-- On the intersection of any original component and any refined component,
their two prescribed ideals have equal closed extension. -/
theorem idealFamily_on_inter
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) (hI : c.IdealCompatible I)
    (i : Fin c.size) (j : Fin d.size) :
    ((c.obj i).interLeft (d.obj j)).restriction.closedIdealMap (I i) =
      ((c.obj i).interRight (d.obj j)).restriction.closedIdealMap (r.idealFamily I j) := by
  rw [idealFamily, BoundedAlgHom.closedIdealMap_comp]
  exact hI.on_test i (r.index j) ((c.obj i).inter (d.obj j))
    ((c.obj i).interLeft (d.obj j)) ((c.obj i).interRight (d.obj j) ≫ r.map j)

/-- Refinement does not change the explicit global contraction of a compatible
ideal family. -/
theorem idealContraction_idealFamily
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) (hI : c.IdealCompatible I) :
    d.idealContraction (r.idealFamily I) = c.idealContraction I := by
  ext a
  rw [mem_idealContraction, mem_idealContraction]
  constructor
  · intro ha i
    apply ((d.interCover (c.obj i) (c.map i)).mem_iff_restrict_mem_closedIdealMap
      (I i) ((c.map i).restriction a)).mpr
    intro j
    change Fin d.size at j
    change ((c.obj i).interLeft (d.obj j)).restriction ((c.map i).restriction a) ∈
      ((c.obj i).interLeft (d.obj j)).restriction.closedIdealMap (I i)
    rw [r.idealFamily_on_inter I hI i j]
    have heq : (c.obj i).interLeft (d.obj j) ≫ c.map i =
        (c.obj i).interRight (d.obj j) ≫ d.map j :=
      @Subsingleton.elim (Inclusion ((c.obj i).inter (d.obj j)) U) inferInstance _ _
    have hmap := congrArg (fun f : Inclusion ((c.obj i).inter (d.obj j)) U =>
      f.restriction a) heq
    exact hmap.symm ▸ ((c.obj i).interRight (d.obj j)).restriction.mem_closedIdealMap (ha j)
  · intro ha j
    have hmap := congrArg (fun f : Inclusion (d.obj j) U => f.restriction a)
      (r.over_target j)
    exact hmap ▸ (r.map j).restriction.mem_closedIdealMap (ha (r.index j))

/-- Effectiveness for the refined ideal family implies effectiveness for the
original compatible family. No reverse containment is assumed for the latter. -/
theorem ideal_effective_of_idealFamily_effective
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) (hI : c.IdealCompatible I)
    (heff : ∀ j, (d.map j).restriction.closedIdealMap
      (d.idealContraction (r.idealFamily I)) = r.idealFamily I j) :
    ∀ i, (c.map i).restriction.closedIdealMap (c.idealContraction I) = I i := by
  intro i
  apply ((d.interCover (c.obj i) (c.map i)).idealExtensionOrderEmbedding).injective
  funext j
  change Fin d.size at j
  change ((c.obj i).interLeft (d.obj j)).restriction.closedIdealMap
      ((c.map i).restriction.closedIdealMap (c.idealContraction I)) =
    ((c.obj i).interLeft (d.obj j)).restriction.closedIdealMap (I i)
  rw [r.idealFamily_on_inter I hI i j,
    ← heff j, r.idealContraction_idealFamily I hI,
    BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp]
  have heq : (c.obj i).interLeft (d.obj j) ≫ c.map i =
      (c.obj i).interRight (d.obj j) ≫ d.map j :=
    @Subsingleton.elim (Inclusion ((c.obj i).inter (d.obj j)) U) inferInstance _ _
  have hres : ((c.obj i).interLeft (d.obj j)).restriction.comp (c.map i).restriction =
      ((c.obj i).interRight (d.obj j)).restriction.comp (d.map j).restriction :=
    congrArg Inclusion.restriction heq
  rw [hres]

end Refinement

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
