import Langlands.GroupScheme.Absolute.BruhatCoveringStatement
import Langlands.GroupScheme.Reductive.BicovariantTorusWeight
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Reductive.SteinbergRationalCellCriterion
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # From a supplied Bruhat cover to the unit locus of an opposite cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section MixedCover

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Right translation of a Bruhat cover by a supplied normalizing point gives
a cover with its conjugate subgroup on the right. -/
theorem BorelTorusBruhatCovering.exists_mixed_factors
    {i : H ⟶ G} {j : T.toGrp ⟶ G} (hcover : BorelTorusBruhatCovering i j)
    (n₀ : normalizerPoints j)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ (b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (n : normalizerPoints j),
      g = (b₁ ≫ i.hom.hom) * n.val *
        (b₂ ≫ (i ≫ (G.innerIso n₀.val).hom).hom.hom) := by
  obtain ⟨b₁, b₂, n, he⟩ := hcover (g * n₀.val)
  refine ⟨b₁, b₂, n * n₀⁻¹, ?_⟩
  have hc : G.constantPoint n₀.val (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      n₀.val := by
    unfold constantPoint
    change (Over.homMk (𝟙 (Spec (CommRingCat.of k))) _ :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ n₀.val = n₀.val
    have h : (Over.homMk (𝟙 (Spec (CommRingCat.of k))) (by simp) :
        Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rfl
    rw [h, Category.id_comp]
  change g = (b₁ ≫ i.hom.hom) * (n.val * n₀.val⁻¹) *
    (b₂ ≫ i.hom.hom ≫ (G.innerIso n₀.val).hom.hom.hom)
  rw [← Category.assoc b₂, comp_innerIso_hom, hc]
  have he' := congrArg (fun x => x * n₀.val⁻¹) he
  calc
    g = (b₁ ≫ i.hom.hom) * n.val * (b₂ ≫ i.hom.hom) * n₀.val⁻¹ := by
      simpa only [mul_inv_cancel_right] using he'
    _ = (b₁ ≫ i.hom.hom) * (n.val * n₀.val⁻¹) *
        (n₀.val * (b₂ ≫ i.hom.hom) * n₀.val⁻¹) := by group

end MixedCover

namespace AffineCoordinates

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom

/-- A unit value of a bi-covariant coordinate on a subgroup-normalizer-subgroup
product forces a unit value at its middle point. -/
theorem isUnit_middle_of_bicovariant_product
    (i : H ⟶ G) (q : Q ⟶ G) {χ : algebra H} {ψ : algebra Q} {d : algebra G}
    (hd : d ∈ leftCovariantSubspace i χ)
    (hr : ∀ (U : Over (Spec (CommRingCat.of k))) (h : U ⟶ Q.X) (g : U ⟶ G.X),
      pointAlgebraHom G U (g * (h ≫ q.hom.hom)⁻¹) d =
        pointAlgebraHom Q U h ψ * pointAlgebraHom G U g d)
    {U : Over (Spec (CommRingCat.of k))}
    (b : U ⟶ H.X) (b' : U ⟶ Q.X) (m : U ⟶ G.X)
    (hu : IsUnit (pointAlgebraHom G U
      ((b ≫ i.hom.hom) * m * (b' ≫ q.hom.hom)) d)) :
    IsUnit (pointAlgebraHom G U m d) := by
  have he : pointAlgebraHom G U
      ((b ≫ i.hom.hom) * m * (b' ≫ q.hom.hom)) d =
      pointAlgebraHom H U b χ *
        (pointAlgebraHom Q U b'⁻¹ ψ * pointAlgebraHom G U m d) := by
    rw [mul_assoc, pointAlgebraHom_leftCovariant i χ hd U b]
    congr 1
    simpa only [GrpObj.inv_comp, inv_inv] using hr U b'⁻¹ m
  rw [he] at hu
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)

end AffineCoordinates

namespace Dynamic

open AffineCoordinates

variable {k : Type u} [Field k]
    {G H U : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Once the unit-valued normalizing factors centralize the supplied torus,
a supplied Bruhat cover gives actual rational opposite-cell factors. -/
theorem exists_opposite_cell_factors_of_bruhat_unit
    (i : H ⟶ G) (j : T.toGrp ⟶ G) (n₀ : normalizerPoints j)
    (ν : cocharacterLattice T)
    (hcover : BorelTorusBruhatCovering i j)
    (hP : (parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (hQ : (parabolic (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j))).IsRepresentedBy
      (i ≫ (G.innerIso n₀.val).hom))
    (iU : U ⟶ G)
    (hU : (unipotent (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy iU)
    (χ ψ : algebra H) (d : algebra G)
    (hd : d ∈ leftCovariantSubspace i χ)
    (hr : ∀ (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X),
      pointAlgebraHom G V (g * (h ≫ (i ≫ (G.innerIso n₀.val).hom).hom.hom)⁻¹) d =
        pointAlgebraHom H V h ψ * pointAlgebraHom G V g d)
    (hcentral : ∀ n : normalizerPoints j,
      IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d) →
        n.val ∈ centralizerPoints j)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G _ g d)) :
    ∃ (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X),
      g = (a ≫ iU.hom.hom) *
        (b ≫ (i ≫ (G.innerIso n₀.val).hom).hom.hom) := by
  let coch := CommGroupScheme.groupHom ν ≫ j
  let q := i ≫ (G.innerIso n₀.val).hom
  obtain ⟨b₁, b₂, n, he⟩ := hcover.exists_mixed_factors n₀ g
  have hnunit : IsUnit (pointAlgebraHom G _ n.val d) := by
    apply isUnit_middle_of_bicovariant_product i q hd hr b₁ b₂ n.val
    rwa [← he]
  have hnZ : n.val ∈ (torusCentralizer j).carrier _ := by
    rw [torusCentralizer_carrier_base]
    exact hcentral n hnunit
  have hnD : n.val ∈ (centralizer coch).carrier _ :=
    torusCentralizer_le_dynamicCentralizer j (CommGroupScheme.groupHom ν) _ hnZ
  have hnQ : n.val ∈ (parabolic (oppositeCocharacter coch)).carrier _ := by
    apply centralizer_le_parabolic (oppositeCocharacter coch) _
    rwa [centralizer_oppositeCocharacter]
  have hb₁ : b₁ ≫ i.hom.hom ∈ (parabolic coch).carrier _ := (hP.pointsEquiv _ b₁).2
  let z := limit coch ⟨b₁ ≫ i.hom.hom, hb₁⟩
  have hz : z ∈ (centralizer coch).carrier _ :=
    limit_mem_centralizer coch ⟨b₁ ≫ i.hom.hom, hb₁⟩
  have hzQ : z ∈ (parabolic (oppositeCocharacter coch)).carrier _ := by
    apply centralizer_le_parabolic (oppositeCocharacter coch) _
    rwa [centralizer_oppositeCocharacter]
  have ha : (b₁ ≫ i.hom.hom) * z⁻¹ ∈ (unipotent coch).carrier _ :=
    mul_inv_limit_mem_unipotent coch ⟨b₁ ≫ i.hom.hom, hb₁⟩
  rw [← hU.2] at ha
  obtain ⟨a, hea⟩ := SubgroupFunctor.mem_range.mp ha
  have hb₂ : b₂ ≫ q.hom.hom ∈ (parabolic (oppositeCocharacter coch)).carrier _ :=
    (hQ.pointsEquiv _ b₂).2
  have hb : z * n.val * (b₂ ≫ q.hom.hom) ∈
      (parabolic (oppositeCocharacter coch)).carrier _ :=
    mul_mem (mul_mem hzQ hnQ) hb₂
  rw [← hQ.2] at hb
  obtain ⟨b, heb⟩ := SubgroupFunctor.mem_range.mp hb
  refine ⟨a, b, ?_⟩
  change g = (a ≫ iU.hom.hom) * (b ≫ q.hom.hom)
  rw [hea, heb]
  calc
    g = (b₁ ≫ i.hom.hom) * n.val * (b₂ ≫ q.hom.hom) := he
    _ = ((b₁ ≫ i.hom.hom) * z⁻¹) * (z * n.val * (b₂ ≫ q.hom.hom)) := by group

section GlobalLift

variable [IsAlgClosed k] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (j : T.toGrp ⟶ G) (n₀ : normalizerPoints j)
    (ν : cocharacterLattice T)
    (hcover : BorelTorusBruhatCovering i j)
    (hP : (parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (hQ : (parabolic (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j))).IsRepresentedBy
      (i ≫ (G.innerIso n₀.val).hom))
    (iU : U ⟶ G)
    (hU : (unipotent (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy iU)
    (χ ψ : algebra H) (d : algebra G)
    (hd : d ∈ leftCovariantSubspace i χ)
    (hr : ∀ (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X),
      pointAlgebraHom G V (g * (h ≫ (i ≫ (G.innerIso n₀.val).hom).hom.hom)⁻¹) d =
        pointAlgebraHom H V h ψ * pointAlgebraHom G V g d)
    (hcentral : ∀ n : normalizerPoints j,
      IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d) →
        n.val ∈ centralizerPoints j)

/-- A global lift into the supplied opposite open multiplication cell,
constructed for every unit-valued point on every relative test scheme. -/
def bruhatUnitCellLift
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    V ⟶ U.X ⊗ H.X := by
  let : IsOpenImmersion
      (SubgroupFunctor.cellMultiplication iU (i ≫ (G.innerIso n₀.val).hom)).left :=
    oppositeCellStatement k G (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j))
      U H iU (i ≫ (G.innerIso n₀.val).hom)
      (by
        change (unipotent (oppositeCocharacter
          (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j)))).IsRepresentedBy iU
        simpa only [oppositeCocharacter_oppositeCocharacter] using hU) hQ
  exact unitPointCellLift G iU (i ≫ (G.innerIso n₀.val).hom) d
    (exists_opposite_cell_factors_of_bruhat_unit i j n₀ ν hcover hP hQ iU hU
      χ ψ d hd hr hcentral) g hg

/-- Multiplication of the constructed global lift recovers the supplied point. -/
theorem bruhatUnitCellLift_comp
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    bruhatUnitCellLift i j n₀ ν hcover hP hQ iU hU χ ψ d hd hr hcentral g hg ≫
      SubgroupFunctor.cellMultiplication iU (i ≫ (G.innerIso n₀.val).hom) = g := by
  let : IsOpenImmersion
      (SubgroupFunctor.cellMultiplication iU (i ≫ (G.innerIso n₀.val).hom)).left :=
    oppositeCellStatement k G (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j))
      U H iU (i ≫ (G.innerIso n₀.val).hom)
      (by
        change (unipotent (oppositeCocharacter
          (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j)))).IsRepresentedBy iU
        simpa only [oppositeCocharacter_oppositeCocharacter] using hU) hQ
  exact unitPointCellLift_comp G iU (i ≫ (G.innerIso n₀.val).hom) d
    (exists_opposite_cell_factors_of_bruhat_unit i j n₀ ν hcover hP hQ iU hU
      χ ψ d hd hr hcentral) g hg

include hcover hP hQ hU hd hr hcentral

/-- The supplied Bruhat and centralizer data imply the opposite-parabolic
factorization on all relative tests required in Steinberg big-cell data. -/
theorem exists_opposite_parabolic_factors_of_bruhat_unit
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g d)) :
    ∃ (b b' : V ⟶ H.X),
      g = (b ≫ i.hom.hom) *
        (b' ≫ (i ≫ (G.innerIso n₀.val).hom).hom.hom)⁻¹ := by
  let a := bruhatUnitCellLift i j n₀ ν hcover hP hQ iU hU χ ψ d hd hr hcentral g hg
  have ha : a ≫ SubgroupFunctor.cellMultiplication iU
      (i ≫ (G.innerIso n₀.val).hom) = g :=
    bruhatUnitCellLift_comp i j n₀ ν hcover hP hQ iU hU χ ψ d hd hr hcentral g hg
  have hau : a ≫ fst U.X H.X ≫ iU.hom.hom ∈
      (parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier V :=
    unipotent_le_parabolic _ V (hU.pointsEquiv V (a ≫ fst U.X H.X)).2
  rw [← hP.2] at hau
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hau
  refine ⟨b, (a ≫ snd U.X H.X)⁻¹, ?_⟩
  rw [GrpObj.inv_comp, inv_inv, hb, ← ha]
  simp only [SubgroupFunctor.cellMultiplication, MonObj.comp_mul, Category.assoc]

end GlobalLift

end Dynamic

end Langlands.GroupScheme
