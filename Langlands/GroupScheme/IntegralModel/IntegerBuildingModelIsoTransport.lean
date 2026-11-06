import Langlands.GroupScheme.IntegralModel.InducedGenericIso
import Langlands.Geometry.Building.IntegerValuationBuildingIsoTransport

/-! # Original model images through integer-building isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

variable {R k : Type u} [CommRing R] [IsDomain R] [Field k]
  [Algebra R k] [IsFractionRing R k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {M : IntegralModel R k G} {N : IntegralModel R k H}
  {f : G ≅ H}

namespace Iso

/-- A compatible integral-model isomorphism carries an exact source-model
comparison to the original target-model image on the transported quotient. -/
theorem integralPoints_eq_oneStabilizer_mapIso (e : M.Iso N f)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) :
    N.integralPoints =
      (B.mapIso f).oneStabilizer (B.mapIsoReducedBuildingEquiv f x) := by
  rw [← e.map_integralPoints, hM]
  exact B.map_oneStabilizer_mapIso f x

/-- The original target integral-section map, with codomain restricted to the
one-group stabilizer of the same transported building point. -/
def integralSectionsToOneStabilizer (e : M.Iso N f)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) :
    N.integralSections →*
      (B.mapIso f).oneStabilizer (B.mapIsoReducedBuildingEquiv f x) where
  toFun s := ⟨N.integralPointMap s,
    (e.integralPoints_eq_oneStabilizer_mapIso B x hM).le ⟨s, rfl⟩⟩
  map_one' := Subtype.ext (map_one N.integralPointMap)
  map_mul' s t := Subtype.ext (map_mul N.integralPointMap s t)

/-- Forgetting stabilizer membership recovers the actual original section map. -/
@[simp] theorem integralSectionsToOneStabilizer_coe (e : M.Iso N f)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) (s : N.integralSections) :
    (e.integralSectionsToOneStabilizer B x hM s : rationalPoints H) =
      N.integralPointMap s := rfl

/-- Every element of the target one-group stabilizer comes from an original
target-model integral section. -/
theorem integralSectionsToOneStabilizer_surjective (e : M.Iso N f)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) :
    Function.Surjective (e.integralSectionsToOneStabilizer B x hM) := by
  intro y
  have hy : y.val ∈ N.integralPoints :=
    (e.integralPoints_eq_oneStabilizer_mapIso B x hM).ge y.property
  obtain ⟨s, hs⟩ := hy
  exact ⟨s, Subtype.ext hs⟩

/-- Global uniqueness for the original image transports through the actual
quotient equivalence and compatible model point map. -/
theorem unique_fixed_mapIso (e : M.Iso N f)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hx : ∀ y : B.ReducedBuilding,
      (∀ g : rationalPoints G, g ∈ M.integralPoints → g • y = y) → y = x)
    (y : (B.mapIso f).ReducedBuilding)
    (hy : ∀ g : rationalPoints H, g ∈ N.integralPoints → g • y = y) :
    y = B.mapIsoReducedBuildingEquiv f x := by
  let Q := B.mapIsoReducedBuildingEquiv f
  have hfixed : ∀ g : rationalPoints G, g ∈ M.integralPoints →
      g • Q.symm y = Q.symm y := by
    intro g hg
    apply Q.injective
    rw [B.mapIsoReducedBuildingEquiv_smul, Q.apply_symm_apply]
    exact hy _ (e.toHom.map_mem_integralPoints hg)
  have hpoint := hx (Q.symm y) hfixed
  simpa only [Q.apply_symm_apply] using congrArg Q hpoint

end Iso

/-- An abstract integral isomorphism uses its actual induced generic map to
carry the exact original model image to the transported one-group stabilizer. -/
theorem integralPoints_eq_oneStabilizer_ofGroupIso
    (e : M.group ≅ N.group)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) :
    N.integralPoints =
      (B.mapIso (M.inducedGenericIso N e)).oneStabilizer
        (B.mapIsoReducedBuildingEquiv (M.inducedGenericIso N e) x) :=
  (Iso.ofGroupIso M N e).integralPoints_eq_oneStabilizer_mapIso B x hM

/-- The original target section map for an abstract integral isomorphism,
using both supplied generic identifications to compute its generic map. -/
def integralSectionsToOneStabilizerOfGroupIso
    (e : M.group ≅ N.group)
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding)
    (hM : M.integralPoints = B.oneStabilizer x) :
    N.integralSections →*
      (B.mapIso (M.inducedGenericIso N e)).oneStabilizer
        (B.mapIsoReducedBuildingEquiv (M.inducedGenericIso N e) x) :=
  (Iso.ofGroupIso M N e).integralSectionsToOneStabilizer B x hM

end Langlands.GroupScheme.IntegralModel
