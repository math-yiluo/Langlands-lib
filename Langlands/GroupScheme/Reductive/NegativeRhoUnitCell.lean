import Langlands.GroupScheme.Reductive.BruhatUnitCell
import Langlands.GroupScheme.Reductive.BicovariantNormalizerCentralizer
import Langlands.GroupScheme.Reductive.NegativeRhoCharacter

/-! # The unit cell for the same extended negative-rho character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section ConjugateFactor

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    {i : H ⟶ G} {j : T.toGrp ⟶ G}

/-- The torus factor in a conjugate subgroup, using the inverse normalizing automorphism. -/
def conjugateTorusFactor (jH : T.toGrp ⟶ H) (n : normalizerPoints j) : T.toGrp ⟶ H :=
  CommGroupScheme.groupHom (normalizingAut j n).inv ≫ jH

/-- This factor embeds the identical torus into the conjugate subgroup. -/
theorem conjugateTorusFactor_comp (jH : T.toGrp ⟶ H) (hH : jH ≫ i = j)
    (n : normalizerPoints j) :
    conjugateTorusFactor jH n ≫ (i ≫ (G.innerIso n.val).hom) = j := by
  let sigma := normalizingAut j n
  have hn : j ≫ (G.innerIso n.val).hom = CommGroupScheme.groupHom sigma.hom ≫ j :=
    isNormalizingPoint_normalizingAut j n
  calc
    conjugateTorusFactor jH n ≫ (i ≫ (G.innerIso n.val).hom) =
        CommGroupScheme.groupHom sigma.inv ≫ ((jH ≫ i) ≫ (G.innerIso n.val).hom) := by
          simp only [conjugateTorusFactor, sigma, Category.assoc]
    _ = CommGroupScheme.groupHom sigma.inv ≫ (j ≫ (G.innerIso n.val).hom) := by rw [hH]
    _ = CommGroupScheme.groupHom sigma.inv ≫ (CommGroupScheme.groupHom sigma.hom ≫ j) := by
      rw [hn]
    _ = j := by
      rw [← Category.assoc]
      change CommGroupScheme.groupHom (sigma.inv ≫ sigma.hom) ≫ j = j
      rw [Iso.inv_hom_id]
      exact Category.id_comp j

end ConjugateFactor

namespace Dynamic

open AffineCoordinates

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

variable (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : H ⟶ G) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {J : Type u} [Fintype J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hroot : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (nu : cocharacterLattice T)
    (hP : (parabolic (CommGroupScheme.groupHom nu ≫ j)).IsRepresentedBy i)
    (hZ : (centralizer (CommGroupScheme.groupHom nu ≫ j)).IsRepresentedBy j)
    (n : normalizerPoints j)
    (hanti : characterAut (normalizingAut j n) (-IntegralWeylVector.rho P b hspan) =
      IntegralWeylVector.rho P b hspan)

include hanti

omit [IsAffineHom H.X.hom] [Fintype J] in
/-- Negation of the original negative-rho weight gives opposite restrictions
for the same character on the subgroup and its supplied conjugate. -/
theorem restrict_negativeRhoCharacter_conjugate :
    characterRestrict (conjugateTorusFactor (centralizerToParabolic hP hZ) n)
        (negativeRhoCharacter hP hZ P b hspan) =
      -characterRestrict (centralizerToParabolic hP hZ)
        (negativeRhoCharacter hP hZ P b hspan) := by
  apply (rationalCharacters.equivCharacterLattice T).injective
  change characterAut (normalizingAut j n)
      (rationalCharacters.equivCharacterLattice T
        (characterRestrict (centralizerToParabolic hP hZ)
          (negativeRhoCharacter hP hZ P b hspan))) =
    -rationalCharacters.equivCharacterLattice T
      (characterRestrict (centralizerToParabolic hP hZ)
        (negativeRhoCharacter hP hZ P b hspan))
  rw [restrict_negativeRhoCharacter]
  simpa only [neg_neg] using hanti

variable (d : algebra G)
    (hd : d ∈ leftCovariantSubspace i
      (negativeRhoCoordinate hP hZ P b hspan))
    (hr : ∀ (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X),
      pointAlgebraHom G V (g * (h ≫ (i ≫ (G.innerIso n.val).hom).hom.hom)⁻¹) d =
        pointAlgebraHom H V h (negativeRhoCoordinate hP hZ P b hspan) *
          pointAlgebraHom G V g d)

include hG hT hj hroot hanti hd hr

/-- A unit-valued normalizing point centralizes the same torus, with
regularity supplied by the actual negative-rho character. -/
theorem mem_centralizerPoints_of_unit_negativeRho
    (m : normalizerPoints j)
    (hm : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) m.val d)) :
    m.val ∈ centralizerPoints j := by
  apply mem_centralizerPoints_of_unit_bicovariant hG hT i
    (i ≫ (G.innerIso n.val).hom) j hj P hroot
    (centralizerToParabolic hP hZ)
    (conjugateTorusFactor (centralizerToParabolic hP hZ) n)
    (negativeRhoCharacter hP hZ P b hspan)
    (negativeRhoCharacter hP hZ P b hspan) d hd hr
    (centralizerToParabolic_comp hP hZ)
    (conjugateTorusFactor_comp _ (centralizerToParabolic_comp hP hZ) n)
    (restrict_negativeRhoCharacter_conjugate i j P b hspan nu hP hZ n hanti)
    ?_ m hm
  intro a
  change P.toLinearMap _ (P.coroot a) ≠ 0
  rw [restrict_negativeRhoCharacter]
  exact IntegralWeylVector.pairing_neg_rho_coroot_ne_zero P b hspan a

section Global

variable [IsAlgClosed k]
    (hcover : BorelTorusBruhatCovering i j)
    (hQ : (parabolic (oppositeCocharacter (CommGroupScheme.groupHom nu ≫ j))).IsRepresentedBy
      (i ≫ (G.innerIso n.val).hom))

include hcover hQ

/-- The actual global unit-cell lift for the supplied negative-rho data.
The unipotent representative is constructed from the affine dynamic functor. -/
def negativeRhoUnitCellLift
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    V ⟶ (Affine.unipotentScheme (CommGroupScheme.groupHom nu ≫ j)).X ⊗ H.X := by
  letI : Smooth G.X.hom := hG.smooth
  exact bruhatUnitCellLift i j n nu hcover hP hQ
    (Affine.unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (negativeRhoCoordinate hP hZ P b hspan)
    (negativeRhoCoordinate hP hZ P b hspan) d hd hr
    (mem_centralizerPoints_of_unit_negativeRho hG hT i j hj P hroot b hspan nu
      hP hZ n hanti d hd hr) g hg

/-- Multiplication of the constructed lift gives the original arbitrary test point. -/
theorem negativeRhoUnitCellLift_comp
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    negativeRhoUnitCellLift hG hT i j hj P hroot b hspan nu hP hZ n hanti d hd hr hcover hQ
        g hg ≫
      SubgroupFunctor.cellMultiplication
        (Affine.unipotentHom (CommGroupScheme.groupHom nu ≫ j))
        (i ≫ (G.innerIso n.val).hom) = g := by
  let : Smooth G.X.hom := hG.smooth
  exact bruhatUnitCellLift_comp i j n nu hcover hP hQ
    (Affine.unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (negativeRhoCoordinate hP hZ P b hspan)
    (negativeRhoCoordinate hP hZ P b hspan) d hd hr
    (mem_centralizerPoints_of_unit_negativeRho hG hT i j hj P hroot b hspan nu
      hP hZ n hanti d hd hr) g hg

/-- The inverse-factor form on every relative test scheme. -/
theorem exists_opposite_parabolic_factors_of_unit_negativeRho
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    ∃ (c c' : V ⟶ H.X),
      g = (c ≫ i.hom.hom) * (c' ≫ (i ≫ (G.innerIso n.val).hom).hom.hom)⁻¹ := by
  let : Smooth G.X.hom := hG.smooth
  exact exists_opposite_parabolic_factors_of_bruhat_unit i j n nu hcover hP hQ
    (Affine.unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom nu ≫ j))
    (negativeRhoCoordinate hP hZ P b hspan)
    (negativeRhoCoordinate hP hZ P b hspan) d hd hr
    (mem_centralizerPoints_of_unit_negativeRho hG hT i j hj P hroot b hspan nu
      hP hZ n hanti d hd hr) g hg

end Global

end Dynamic

end Langlands.GroupScheme
