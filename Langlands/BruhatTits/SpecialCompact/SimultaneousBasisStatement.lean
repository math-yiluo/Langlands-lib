import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Geometry.Building.KPBuilding

/-! # General existence of a simultaneous basis at a geometric compact stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- General existence target for the simultaneous actual-standard-group basis
at the compact stabilizer of a geometric special vertex. The apartment data and
the point are conclusions, with the same maximal split torus and positive system
used in every standard subgroup. This makes no assertion for arbitrary weak
`KPApartmentData`, and supplies no proof or joint compact-package witness. -/
def SimultaneousStandardBasisExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (ν : cocharacterLattice S), IsGenericCocharacter i ν →
      ∃ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment),
        AffineRootSystem.IsSpecialPoint D.affineRoots x ∧
          AffineRootSystem.IsVertex D.affineRoots x ∧
            SimultaneousStandardBasisAt i ν
              (D.compactStabilizer (D.apartmentMap x))

end Langlands.BruhatTits.SpecialCompact
