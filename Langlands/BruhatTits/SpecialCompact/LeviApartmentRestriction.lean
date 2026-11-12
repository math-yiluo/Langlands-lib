import Langlands.BruhatTits.SpecialCompact.LeviValuationRestriction
import Langlands.BruhatTits.SpecialCompact.Properties

/-! # The prescribed Levi apartment as a restricted valuation class -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ω : Fˣ → ℝ} (D : KPApartmentData i ω)

/-- The original ambient valuation class restricted to the prescribed Levi,
with normalizer stability and compatibility with the same field valuation. -/
def leviRestrictedApartmentData : KPApartmentData iM ω where
  carrier := leviRestrictedRootFunctionFamily iM j '' D.carrier
  exists_eq_orbit := by
    obtain ⟨φ, hφ, hω, hc⟩ := D.exists_eq_orbit
    refine ⟨leviRestrictedRootFunctionFamily iM j φ,
      leviRestricted_isRootDatumValuation iM j hS i hcomp ζ hj hjc hG hi hφ,
      leviRestricted_isSplitTorusCompatible iM j hS i hcomp ζ hj hjc hω, ?_⟩
    rw [hc]
    ext ψ
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, (leviRestrictedRootFunctionFamily_vadd iM j hS i hcomp ζ hj hjc φ v).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v +ᵥ φ, ⟨v, rfl⟩,
        leviRestrictedRootFunctionFamily_vadd iM j hS i hcomp ζ hj hjc φ v⟩
  smul_mem := by
    rintro n _ ⟨φ, hφ, rfl⟩
    let n' := normalizerPointsMap iM j i hcomp n
    exact ⟨n' • φ, D.smul_mem n' φ hφ,
      leviRestrictedRootFunctionFamily_smul iM j hS i hcomp ζ hj hjc φ n⟩

/-- The actual map from the ambient apartment to the restricted Levi apartment. -/
def leviApartmentProjection (x : D.Apartment) :
    (leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D).Apartment :=
  ⟨leviRestrictedRootFunctionFamily iM j x.val, ⟨x.val, x.mem, rfl⟩⟩

/-- The projected point restricts exactly the original root valuation on every
Levi root and every rational point, in the published predicate. -/
theorem isLeviRestriction_leviApartmentProjection (x : D.Apartment) :
    IsLeviRestriction j x
      (leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x) := by
  intro a ha m
  exact leviRestrictedRootFunctionFamily_apply iM j x.val a ha m

/-- Every point of the restricted class is the projection of an ambient point. -/
theorem leviApartmentProjection_surjective :
    Function.Surjective (leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D) := by
  rintro ⟨ψ, φ, hφ, heq⟩
  exact ⟨⟨φ, hφ⟩, KPApartmentData.Apartment.ext heq⟩

end Langlands.BruhatTits.SpecialCompact
