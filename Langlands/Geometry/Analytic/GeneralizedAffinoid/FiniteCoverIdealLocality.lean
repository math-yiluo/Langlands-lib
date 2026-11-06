import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotientBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Detecting global ideal membership on finite full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A} (c : FiniteCover U)

/-- The same finite cover over the actual algebra of its target. All component
algebras and all actual restrictions are retained. -/
def relativeCover : FiniteCover (Domain.whole K U.algebra) where
  size := c.size
  obj i := U.relative (c.obj i) (c.map i)
  map i := ⟨(c.map i).restriction, rfl⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := c.covers (U.spectrumMap x) (U.represents.hasImageIn x)
    refine ⟨i, ?_⟩
    rw [U.relative_locus_eq_preimage]
    exact hi

variable (J : Ideal U.algebra)

local instance : IsClosed (J : Set U.algebra) :=
  PresentedAffinoidAlgebra.isClosed_ideal U.algebra J

/-- The inverse-image cover on the actual closed quotient of the target.
The cover may be empty, and the quotient may be the zero algebra. -/
def quotientCover :
    FiniteCover (Domain.whole K (ClosedQuotient.algebra U.algebra J)) where
  size := c.size
  obj i := Domain.pullback (ClosedQuotient.map U.algebra J) (c.relativeCover.obj i)
  map i := ⟨(Domain.pullback (ClosedQuotient.map U.algebra J)
    (c.relativeCover.obj i)).baseMap, rfl⟩
  covers x _ := c.relativeCover.covers
    (BanachSpectrum.comap (ClosedQuotient.map U.algebra J).toBoundedRingHom x)
    (Set.mem_univ _)

/-- Membership in a global ideal is detected by the closed extensions on any
finite full-domain cover, using scalar separation on the quotient cover. -/
theorem mem_iff_restrict_mem_closedIdealMap (a : U.algebra) :
    a ∈ J ↔ ∀ i, (c.map i).restriction a ∈ (c.map i).restriction.closedIdealMap J := by
  constructor
  · intro ha i
    exact (c.map i).restriction.mem_closedIdealMap ha
  · intro ha
    apply (ClosedQuotient.map_eq_zero_iff U.algebra J a).mp
    apply (c.quotientCover J).algebra_ext_of_restrict_eq
    intro i
    change Fin c.size at i
    change AffinoidPushout.leftMap (ClosedQuotient.map U.algebra J)
        (c.map i).restriction (ClosedQuotient.map U.algebra J a) =
      AffinoidPushout.leftMap (ClosedQuotient.map U.algebra J)
        (c.map i).restriction 0
    rw [map_zero]
    have h := congrArg
      (fun f : BoundedAlgHom K U.algebra
        (AffinoidPushout.algebra (ClosedQuotient.map U.algebra J)
          (c.map i).restriction) => f a)
      (AffinoidPushout.condition (ClosedQuotient.map U.algebra J)
        (c.map i).restriction)
    exact h.trans
      (ClosedQuotient.rightMap_annihilates_closedIdealMap (c.map i).restriction J
        ((c.map i).restriction a) (ha i))

/-- Contracting all closed extensions of a global ideal recovers it exactly. -/
theorem idealContraction_closedIdealMap :
    c.idealContraction (fun i => (c.map i).restriction.closedIdealMap J) = J := by
  ext a
  exact (c.mem_idealContraction _ a).trans
    (c.mem_iff_restrict_mem_closedIdealMap J a).symm

/-- Closed extensions on a finite full-domain cover detect the inclusion
relation between arbitrary global ideals. -/
theorem le_iff_closedIdealMap_le (H : Ideal U.algebra) :
    J ≤ H ↔ ∀ i, (c.map i).restriction.closedIdealMap J ≤
      (c.map i).restriction.closedIdealMap H := by
  constructor
  · intro h i
    exact (c.map i).restriction.closedIdealMap_mono h
  · intro h a ha
    apply (c.mem_iff_restrict_mem_closedIdealMap H a).mpr
    intro i
    exact h i ((c.map i).restriction.mem_closedIdealMap ha)

/-- The actual restriction maps give an order embedding from the target's
ideal lattice to the product of the component ideal lattices. -/
def idealExtensionOrderEmbedding :
    Ideal U.algebra ↪o (∀ i : Fin c.size, Ideal (c.obj i).algebra) where
  toFun J i := (c.map i).restriction.closedIdealMap J
  inj' := by
    intro J H h
    have hJ := c.idealContraction_closedIdealMap J
    have hH := c.idealContraction_closedIdealMap H
    exact hJ.symm.trans ((congrArg c.idealContraction h).trans hH)
  map_rel_iff' := (c.le_iff_closedIdealMap_le _ _).symm

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
