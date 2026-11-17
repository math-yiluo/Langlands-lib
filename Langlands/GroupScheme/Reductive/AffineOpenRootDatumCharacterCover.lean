import Langlands.GroupScheme.Reductive.LocalRootDatumCharacterBaseChange
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Affine open covers carrying root-datum character maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace splitTorus

/-- The common torus square survives arbitrary scheme base change in
standard split-torus coordinates. -/
theorem coordinateBaseChangeHom_square_scheme
    {S B : Scheme.{u}} (b : B ⟶ S)
    {I I' : Type u} [Fintype I] [Fintype I'] {G H : GroupScheme S}
    (i : splitTorus S I ⟶ G) (j : splitTorus S I' ⟶ H)
    (tau : commGroupScheme S I ⟶ commGroupScheme S I')
    (f : G ⟶ H) (h : i ≫ f = CommGroupScheme.groupHom tau ≫ j) :
    ((baseChangeIso b I).inv ≫ (baseChange b).map i) ≫ (baseChange b).map f =
      CommGroupScheme.groupHom (coordinateBaseChangeHom b tau) ≫
        ((baseChangeIso b I').inv ≫ (baseChange b).map j) := by
  change (baseChangeIso b I).inv ≫
      (baseChange b).map i ≫ (baseChange b).map f =
    ((baseChangeIso b I).inv ≫
      (baseChange b).map (CommGroupScheme.groupHom tau) ≫
      (baseChangeIso b I').hom) ≫ (baseChangeIso b I').inv ≫ (baseChange b).map j
  rw [← Functor.map_comp, h, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end splitTorus

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]

/-- Actual character maps of root-datum isogenies exist on an affine open cover. -/
def HasAffineOpenRootDatumTorusCharacterMap
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced] : Prop :=
  ∃ U : Scheme.AffineOpenCover.{u} (Spec (CommRingCat.of R)),
    ∀ a : U.I₀, HasRootDatumTorusCharacterMap
      (splitTorus.coordinateBaseChangeHom (U.f a) tau) P Q

/-- Neighbourhood formulas refine to actual character maps on affine charts. -/
theorem HasZariskiLocalRootDatumTorusCharacterMap.affineOpenCover
    {tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I'}
    (h : HasZariskiLocalRootDatumTorusCharacterMap tau P Q) :
    HasAffineOpenRootDatumTorusCharacterMap tau P Q := by
  classical
  choose V hs p r hw using h
  let U := (Spec (CommRingCat.of R)).openCoverOfIsOpenCover V (by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_le_iff.mp
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hs s⟩)
  refine ⟨U.affineRefinement, ?_⟩
  rintro ⟨s, a⟩
  refine ⟨p s, r s, ?_⟩
  apply hw s
  change ((U.X s).affineOpenCover.f a ≫ (V s).ι) ⁻¹ᵁ (V s) = ⊤
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

variable {G H : GroupScheme (Spec (CommRingCat.of R))}
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I'}
  (phi Phi : G ⟶ H)
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)

include hphi hPhi

/-- The affine character cover and the two original torus squares give
the actual common root-datum map on each pulled-back pair of groups. -/
theorem HasAffineOpenRootDatumTorusCharacterMap.common_torusSquares
    (h : HasAffineOpenRootDatumTorusCharacterMap tau P Q) :
    ∃ U : Scheme.AffineOpenCover.{u} (Spec (CommRingCat.of R)),
      ∀ a : U.I₀, HasCommonRootDatumTorusMap
        ((splitTorus.baseChangeIso (U.f a) I).inv ≫ (baseChange (U.f a)).map i)
        ((splitTorus.baseChangeIso (U.f a) I').inv ≫ (baseChange (U.f a)).map j)
        P Q ((baseChange (U.f a)).map phi) ((baseChange (U.f a)).map Phi) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun a => ?_⟩
  obtain ⟨p, r, hw⟩ := hU a
  exact ⟨p, r, splitTorus.coordinateBaseChangeHom (U.f a) tau, hw,
    splitTorus.coordinateBaseChangeHom_square_scheme (U.f a) i j tau phi hphi,
    splitTorus.coordinateBaseChangeHom_square_scheme (U.f a) i j tau Phi hPhi⟩

/-- Neighbourhood character formulas assemble the common torus maps for
both ambient homomorphisms on one affine open cover. -/
theorem HasZariskiLocalRootDatumTorusCharacterMap.common_torusSquares
    (h : HasZariskiLocalRootDatumTorusCharacterMap tau P Q) :
    ∃ U : Scheme.AffineOpenCover.{u} (Spec (CommRingCat.of R)),
      ∀ a : U.I₀, HasCommonRootDatumTorusMap
        ((splitTorus.baseChangeIso (U.f a) I).inv ≫ (baseChange (U.f a)).map i)
        ((splitTorus.baseChangeIso (U.f a) I').inv ≫ (baseChange (U.f a)).map j)
        P Q ((baseChange (U.f a)).map phi) ((baseChange (U.f a)).map Phi) :=
  h.affineOpenCover.common_torusSquares i j phi Phi hphi hPhi

end Langlands.GroupScheme
