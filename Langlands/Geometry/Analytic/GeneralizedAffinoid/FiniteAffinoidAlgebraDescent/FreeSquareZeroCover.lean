import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FreeSquareZeroBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # The inverse-image cover in free square-zero coordinates -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

variable (n : ℕ)

/-- The inverse image of a full domain under the scalar map, presented in
free square-zero coordinates over that domain's original algebra. -/
def domain (U : Domain K A) : Domain K (algebra K A n) where
  algebra := FreeSquareZero.algebra K U.algebra n
  baseMap := map U.baseMap n
  locus := (BanachSpectrum.comap (baseMap K A n).toBoundedRingHom) ⁻¹' U.locus
  represents := by
    have h := (Domain.represents_pullback (baseMap K A n) U).postcomp_equiv
      (pushoutEquiv (n := n) U.baseMap)
    exact (pushoutEquiv_left (n := n) U.baseMap) ▸ h

/-- A restriction of original full domains restricts all the square-zero
coefficients by the original bounded map. -/
def inclusion {U V : Domain K A} (f : U ⟶ V) : domain n U ⟶ domain n V where
  restriction := map f.restriction n
  comp_baseMap := (map_comp f.restriction V.baseMap).trans
    (congrArg (fun g : BoundedAlgHom K A U.algebra => map g n) f.comp_baseMap)

/-- Use the same indices and original domains to cover the free square-zero
spectrum by these inverse-image domains. -/
def cover (c : Domain.FiniteCover (Domain.whole K A)) :
    Domain.FiniteCover (Domain.whole K (algebra K A n)) where
  size := c.size
  obj i := domain n (c.obj i)
  map i := ⟨(domain n (c.obj i)).baseMap, rfl⟩
  covers x _ := c.covers (BanachSpectrum.comap (baseMap K A n).toBoundedRingHom x)
    (Set.mem_univ _)

/-- The literal intersection in the new cover has the bounded algebra of the
square-zero domain over the original literal intersection. -/
def intersectionEquiv (U V : Domain K A) :
    BoundedAlgEquiv K ((domain n U).inter (domain n V)).algebra (domain n (U.inter V)).algebra :=
  Domain.boundedEquivOfLocusEq _ _ rfl

@[simp] theorem intersectionEquiv_comp_interLeft (U V : Domain K A) :
    (intersectionEquiv n U V).toBoundedAlgHom.comp ((domain n U).interLeft (domain n V)).restriction =
      (inclusion n (U.interLeft V)).restriction := by
  apply Domain.boundedHom_eq_of_over_base (domain n U) (domain n (U.inter V))
  · rw [BoundedAlgHom.comp_assoc, ((domain n U).interLeft (domain n V)).comp_baseMap]
    exact Domain.boundedEquivOfLocusEq_comp_baseMap _ _ _
  · exact (inclusion n (U.interLeft V)).comp_baseMap

@[simp] theorem intersectionEquiv_comp_interRight (U V : Domain K A) :
    (intersectionEquiv n U V).toBoundedAlgHom.comp ((domain n U).interRight (domain n V)).restriction =
      (inclusion n (U.interRight V)).restriction := by
  apply Domain.boundedHom_eq_of_over_base (domain n V) (domain n (U.inter V))
  · rw [BoundedAlgHom.comp_assoc, ((domain n U).interRight (domain n V)).comp_baseMap]
    exact Domain.boundedEquivOfLocusEq_comp_baseMap _ _ _
  · exact (inclusion n (U.interRight V)).comp_baseMap

end Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero
