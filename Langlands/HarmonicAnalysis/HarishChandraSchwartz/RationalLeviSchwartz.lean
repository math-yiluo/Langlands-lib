import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GroupTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme

/-! # Schwartz spaces on the standard Levi scheme and its actual subgroup

The canonical rational-point equivalence identifies the Schwartz space defined on the
Levi scheme with the space on the actual standard Levi subgroup, preserving the topology
and every defining seminorm.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance leviSchwartzIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance leviSchwartzLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

/-- The Schwartz space on the actual standard Levi subgroup is continuously linearly
equivalent to the Schwartz space on the Levi scheme, for `j⁻¹(K)` and `ρ ∘ j`. -/
def rationalLeviSchwartzEquiv :
    Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) ≃L[ℂ]
      RationalSchwartzSpace (isCompact_leviSchemeCompact hKc)
        (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)
        (ρ.restrict (Standard.leviHom i ν J)) :=
  Space.comapEquiv (leviSchemePointsEquiv i ν J)
    (rationalXi_leviScheme hG hi hν hJ hKo hKc hM)
    (rationalHeight_restrict_leviHom ρ)

/-- The equivalence pulls functions back along the canonical Levi point equivalence. -/
@[simp] theorem rationalLeviSchwartzEquiv_apply
    (f : Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m))
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f x =
      f (leviSchemePointsEquiv i ν J x) := rfl

/-- The inverse reads a function on the Levi scheme as a function on the actual subgroup. -/
@[simp] theorem rationalLeviSchwartzEquiv_symm_apply
    (f : RationalSchwartzSpace (isCompact_leviSchemeCompact hKc)
      (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)
      (ρ.restrict (Standard.leviHom i ν J)))
    (m : standardLeviPoints i ν J) :
    (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM).symm f m =
      f ((leviSchemePointsEquiv i ν J).symm m) := rfl

/-- Every defining seminorm agrees in the scheme and subgroup realizations. -/
theorem nu_rationalLeviSchwartzEquiv (r : ℝ)
    (f : Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m)) :
    nu (rationalXi (isCompact_leviSchemeCompact hKc)
        (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM))
      (rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J))) r
      (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f) =
        nu (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) r f :=
  Space.nu_comapEquiv (leviSchemePointsEquiv i ν J)
    (rationalXi_leviScheme hG hi hν hJ hKo hKc hM)
    (rationalHeight_restrict_leviHom ρ) r f

end Langlands.HarishChandraSchwartz
