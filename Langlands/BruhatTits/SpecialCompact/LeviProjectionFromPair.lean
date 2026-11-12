import Langlands.BruhatTits.SpecialCompact.LeviApartmentProjection

/-! # The canonical Levi affine projection from a supplied restriction pair -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
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
    (hjc : IsClosedSubgroup j) {ω : Fˣ → ℝ}
    (D : KPApartmentData i ω) (PM : KPApartmentData iM ω)

/-- The affine map with the existing quotient projection as linear part and
sending the specified ambient point to the specified Levi point. -/
def leviProjectionFromPair (x : D.Apartment) (xM : PM.Apartment) :
    D.Apartment →ᵃ[ℝ] PM.Apartment where
  toFun y := leviTranslationProjection i iM j hcomp ζ hj (y -ᵥ x) +ᵥ xM
  linear := leviTranslationProjection i iM j hcomp ζ hj
  map_vadd' := by
    intro y v
    rw [vadd_vsub_assoc, map_add, add_vadd]

@[simp] theorem leviProjectionFromPair_apply_self (x : D.Apartment) (xM : PM.Apartment) :
    leviProjectionFromPair i iM j hcomp ζ hj D PM x xM x = xM := by
  change leviTranslationProjection i iM j hcomp ζ hj (x -ᵥ x) +ᵥ xM = xM
  rw [vsub_self, map_zero, zero_vadd]

/-- The same full cocharacter vector translates a restriction pair together. -/
theorem leviProjectionFromPair_mk_vadd (x : D.Apartment) (xM : PM.Apartment) (v : V S) :
    leviProjectionFromPair i iM j hcomp ζ hj D PM x xM
        ((Submodule.Quotient.mk v : TranslationSpace i) +ᵥ x) =
      (Submodule.Quotient.mk v : TranslationSpace iM) +ᵥ xM := by
  rw [AffineMap.map_vadd, leviProjectionFromPair_apply_self]
  rfl

/-- One literal restriction pair determines restriction at every point of the
canonical affine projection. -/
theorem isLeviRestriction_leviProjectionFromPair
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM)
    (y : D.Apartment) :
    IsLeviRestriction j y (leviProjectionFromPair i iM j hcomp ζ hj D PM x xM y) := by
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (rootAnnihilator i) (y -ᵥ x)
  have hy : y = (Submodule.Quotient.mk v : TranslationSpace i) +ᵥ x := by
    rw [hv, vsub_vadd]
  rw [hy, leviProjectionFromPair_mk_vadd]
  intro a ha m
  simp only [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply]
  rw [hres a ha m]

/-- A literal restriction pair is equality with the normalized restricted
root-function family on all characters, including those off the Levi support. -/
theorem val_eq_restricted_of_isLeviRestriction
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM) :
    xM.val = leviRestrictedRootFunctionFamily iM j x.val := by
  ext a m
  by_cases ha : a ∈ relativeRoots iM
  · rw [leviRestrictedRootFunctionFamily_apply iM j x.val a ha]
    exact hres a ha m
  · rw [xM.isValuation.eq_top_of_not_mem_roots a ha,
      leviRestrictedRootFunctionFamily_apply_not_mem iM j x.val a ha]

include hS hcomp hj hjc in
/-- Normalizer equivariance follows from literal restriction at all points;
no independent equivariance hypothesis or new apartment is required. -/
theorem leviProjectionFromPair_normalizer
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM)
    (n : normalizerPoints iM) (y : D.Apartment) :
    leviProjectionFromPair i iM j hcomp ζ hj D PM x xM
        (normalizerPointsMap iM j i hcomp n • y) =
      n • leviProjectionFromPair i iM j hcomp ζ hj D PM x xM y := by
  let f := leviProjectionFromPair i iM j hcomp ζ hj D PM x xM
  have hval (z : D.Apartment) : (f z).val = leviRestrictedRootFunctionFamily iM j z.val :=
    val_eq_restricted_of_isLeviRestriction i iM j D PM z (f z)
      (isLeviRestriction_leviProjectionFromPair i iM j hcomp ζ hj D PM x xM hres z)
  apply KPApartmentData.Apartment.ext
  change (f (normalizerPointsMap iM j i hcomp n • y)).val = n • (f y).val
  rw [hval, KPApartmentData.val_smul,
    leviRestrictedRootFunctionFamily_smul iM j hS i hcomp ζ hj hjc y.val n, hval]

/-- The canonical affine projection onto the supplied Levi apartment is surjective. -/
theorem leviProjectionFromPair_surjective (x : D.Apartment) (xM : PM.Apartment) :
    Function.Surjective (leviProjectionFromPair i iM j hcomp ζ hj D PM x xM) := by
  intro yM
  obtain ⟨v, hv⟩ := leviTranslationProjection_surjective i iM j hcomp ζ hj (yM -ᵥ xM)
  refine ⟨v +ᵥ x, ?_⟩
  rw [AffineMap.map_vadd, leviProjectionFromPair_apply_self]
  change leviTranslationProjection i iM j hcomp ζ hj v +ᵥ xM = yM
  rw [hv, vsub_vadd]

include hS hcomp hj hjc in
/-- A finite filtration at any literal restriction pair maps into the ambient
filtration at the same real depth. -/
theorem map_filtration_le_of_isLeviRestriction
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM)
    (a : relativeRoots iM) (r : ℝ) :
    PM.filtration xM a r ≤ (D.filtration x a r).comap (rationalPoints.map j) := by
  intro m hm
  apply KPApartmentData.mem_filtration.mpr
  refine ⟨?_, ?_⟩
  · rw [← map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a a.property]
    exact Subgroup.mem_map.mpr ⟨m, hm.1, rfl⟩
  · change (r : WithTop ℝ) ≤ x.val a (rationalPoints.map j m)
    rw [← hres a a.property m]
    exact hm.2

include hS hcomp hj hjc in
/-- Every Levi sharp fixer at a literal restriction pair maps into the
ambient sharp fixer, in the original group and quotient carriers. -/
theorem sharpFixer_le_of_isLeviRestriction
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM) :
    PM.sharpFixer {xM} ≤ (D.sharpFixer {x}).comap (rationalPoints.map j) := by
  change (⨆ a : relativeRoots iM, PM.rootFixer a {xM}) ≤ _
  refine iSup_le fun a => ?_
  rw [PM.rootFixer_singleton]
  intro m hm
  apply D.rootFixer_le_sharpFixer
    ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩ {x}
  rw [D.rootFixer_singleton]
  exact map_filtration_le_of_isLeviRestriction hS i iM j hcomp ζ hj hjc D PM x xM hres a 0 hm

end Langlands.BruhatTits.SpecialCompact
