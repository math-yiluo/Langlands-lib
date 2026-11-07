import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.CoordinateNonZeroDivisor
import Langlands.GroupScheme.Reductive.CovariantSocleIrreducible
import Langlands.GroupScheme.Reductive.SteinbergRationalCellCriterion
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Mathlib.RingTheory.Localization.BaseChange

/-! # The negative Borel cell of a supplied split pinning -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-! ### A cocharacter positive on the supplied base -/

/-- The simple roots of the supplied base stay independent after rationalization. -/
theorem linearIndependent_toRat_simpleRoot :
    LinearIndependent ℚ (fun a : p.base.support => toRat (p.rootDatum.root a)) := by
  have hZ : LinearIndependent ℤ (fun a : p.base.support => p.rootDatum.root a) :=
    p.base.linearIndepOn_root
  exact hZ.of_isLocalizedModule ℚ (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (characterLattice p.torus) 1)

/-- Some cocharacter pairs with every root as a fixed positive multiple of its
height relative to the supplied base. -/
theorem exists_cocharacter_pairing_eq_height :
    ∃ d : ℤ, 0 < d ∧ ∃ ν : cocharacterLattice p.torus,
      ∀ i : p.rootIndex,
        latticePairing p.torus (p.rootDatum.root i) ν = d * p.base.height i := by
  classical
  obtain ⟨d, hd, ν, hν⟩ := p.isSplitTorus.exists_scaled_pairings
    (fun a : p.base.support => p.rootDatum.root a) p.linearIndependent_toRat_simpleRoot
    (fun _ => 1)
  refine ⟨d, hd, ν, fun i => ?_⟩
  obtain ⟨f, -, -, hf⟩ := p.base.exists_root_eq_sum_int i
  rw [RootPairing.Base.height_eq_sum hf, hf, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  have h := hν ⟨j, hj⟩
  simp only [mul_one] at h
  rw [h, mul_comm]

/-- A chosen cocharacter of the supplied torus whose root pairings are a positive
multiple of the heights relative to the supplied base. -/
def positiveCocharacter : cocharacterLattice p.torus :=
  (p.exists_cocharacter_pairing_eq_height.choose_spec.2).choose

/-- The positive scale of `positiveCocharacter`. -/
def positiveScale : ℤ :=
  p.exists_cocharacter_pairing_eq_height.choose

theorem positiveScale_pos : 0 < p.positiveScale :=
  p.exists_cocharacter_pairing_eq_height.choose_spec.1

theorem latticePairing_root_positiveCocharacter (i : p.rootIndex) :
    latticePairing p.torus (p.rootDatum.root i) p.positiveCocharacter =
      p.positiveScale * p.base.height i :=
  (p.exists_cocharacter_pairing_eq_height.choose_spec.2).choose_spec i

/-- The chosen cocharacter pairs positively exactly with the positive roots. -/
theorem latticePairing_root_positiveCocharacter_pos_iff (i : p.rootIndex) :
    0 < latticePairing p.torus (p.rootDatum.root i) p.positiveCocharacter ↔
      p.base.IsPos i := by
  rw [p.latticePairing_root_positiveCocharacter, RootPairing.Base.isPos_iff]
  exact ⟨fun h => pos_of_mul_pos_right h p.positiveScale_pos.le,
    fun h => mul_pos p.positiveScale_pos h⟩

/-- The chosen cocharacter pairs nontrivially with every root. -/
theorem latticePairing_root_positiveCocharacter_ne_zero (i : p.rootIndex) :
    latticePairing p.torus (p.rootDatum.root i) p.positiveCocharacter ≠ 0 := by
  rw [p.latticePairing_root_positiveCocharacter]
  exact mul_ne_zero p.positiveScale_pos.ne' (p.base.height_ne_zero i)

/-- The chosen cocharacter is generic for the supplied maximal torus. -/
theorem isGenericCocharacter_positiveCocharacter :
    IsGenericCocharacter p.inclusion p.positiveCocharacter := by
  intro α hα
  obtain ⟨i, rfl⟩ : ∃ i, p.rootDatum.root i = α := by
    rw [← Set.mem_range, p.isRootDatum.2.1]
    exact hα
  exact p.latticePairing_root_positiveCocharacter_ne_zero i

/-! ### The negative Borel subgroup and the positive unipotent subgroup -/

/-- The chosen positive cocharacter as a homomorphism `𝔾_m ⟶ G`. -/
def positiveGm : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  CommGroupScheme.groupHom p.positiveCocharacter ≫ p.inclusion

/-- The positive cocharacter centralizes exactly the supplied maximal torus. -/
theorem centralizer_positiveGm :
    Dynamic.centralizer p.positiveGm = SubgroupFunctor.range p.inclusion := by
  rw [positiveGm, genericCentralizer k G p.isConnectedReductive p.torus p.inclusion
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus) _
    p.isGenericCocharacter_positiveCocharacter]
  exact maximalTorusCentralizer k G p.isConnectedReductive p.torus p.inclusion p.isMaximalTorus

/-- The supplied torus embedding represents the centralizer of the reversed
positive cocharacter. -/
theorem isRepresentedBy_centralizer_opposite :
    (Dynamic.centralizer (Dynamic.oppositeCocharacter p.positiveGm)).IsRepresentedBy
      p.inclusion := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  rw [Dynamic.centralizer_oppositeCocharacter, p.centralizer_positiveGm]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The negative Borel subgroup `P_G(ν⁻¹)` of the reversed positive cocharacter. -/
abbrev negativeBorel : GroupScheme (Spec (CommRingCat.of k)) :=
  Dynamic.Affine.parabolicScheme (Dynamic.oppositeCocharacter p.positiveGm)

/-- The inclusion of the negative Borel subgroup. -/
def negativeBorelHom : p.negativeBorel ⟶ G :=
  Dynamic.Affine.parabolicHom (Dynamic.oppositeCocharacter p.positiveGm)

theorem isRepresentedBy_negativeBorelHom :
    (Dynamic.parabolic (Dynamic.oppositeCocharacter p.positiveGm)).IsRepresentedBy
      p.negativeBorelHom :=
  Dynamic.Affine.isRepresentedBy_parabolicHom _

/-- The positive unipotent subgroup `U_G(ν)` contracted by the positive cocharacter. -/
abbrev positiveUnipotent : GroupScheme (Spec (CommRingCat.of k)) :=
  Dynamic.Affine.unipotentScheme p.positiveGm

/-- The inclusion of the positive unipotent subgroup. -/
def positiveUnipotentHom : p.positiveUnipotent ⟶ G :=
  Dynamic.Affine.unipotentHom p.positiveGm

theorem isRepresentedBy_positiveUnipotentHom :
    (Dynamic.unipotent p.positiveGm).IsRepresentedBy p.positiveUnipotentHom :=
  Dynamic.Affine.isRepresentedBy_unipotentHom _

instance isAffineHom_negativeBorel : IsAffineHom p.negativeBorel.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom _).isAffineHom

instance isAffineHom_positiveUnipotent : IsAffineHom p.positiveUnipotent.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom _).isAffineHom

/-- The positive unipotent subgroup is unipotent. -/
theorem isUnipotent_positiveUnipotent : IsUnipotent p.positiveUnipotent := by
  have := p.isConnectedReductive.smooth
  exact Dynamic.isUnipotent_of_isRepresentedBy_unipotent p.positiveGm
    p.isRepresentedBy_positiveUnipotentHom (Dynamic.Affine.isClosedSubgroup_unipotentHom _)

/-- The limit homomorphism from the negative Borel subgroup onto the supplied torus. -/
def negativeBorelToTorus : p.negativeBorel ⟶ p.torus.toGrp :=
  Dynamic.limitGroupHom p.isRepresentedBy_negativeBorelHom
    p.isRepresentedBy_centralizer_opposite

/-- The inclusion of the supplied torus into the negative Borel subgroup. -/
def torusToNegativeBorel : p.torus.toGrp ⟶ p.negativeBorel :=
  Dynamic.centralizerToParabolic p.isRepresentedBy_negativeBorelHom
    p.isRepresentedBy_centralizer_opposite

theorem torusToNegativeBorel_comp :
    p.torusToNegativeBorel ≫ p.negativeBorelHom = p.inclusion :=
  Dynamic.centralizerToParabolic_comp _ _

theorem torusToNegativeBorel_comp_negativeBorelToTorus :
    p.torusToNegativeBorel ≫ p.negativeBorelToTorus = 𝟙 _ :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

/-! ### Characters of the negative Borel subgroup -/

/-- The extension of a torus character to the negative Borel subgroup through
the limit homomorphism. -/
def borelCharacter (lam : characterLattice p.torus) : rationalCharacters p.negativeBorel :=
  characterRestrict p.negativeBorelToTorus
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)

theorem borelCharacter_add (lam mu : characterLattice p.torus) :
    p.borelCharacter (lam + mu) = p.borelCharacter lam + p.borelCharacter mu := by
  rw [borelCharacter, borelCharacter, borelCharacter, map_add, map_add]

/-- The coordinate function of the extended character. -/
def borelCharacterCoordinate (lam : characterLattice p.torus) :
    AffineCoordinates.algebra p.negativeBorel :=
  AffineCoordinates.characterCoordinate p.negativeBorel (p.borelCharacter lam)

theorem pointAlgebraHom_borelCharacterCoordinate (lam : characterLattice p.torus)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ p.negativeBorel.X) :
    AffineCoordinates.pointAlgebraHom p.negativeBorel T h (p.borelCharacterCoordinate lam) =
      (characterEval (p.borelCharacter lam) T h).1 :=
  AffineCoordinates.pointAlgebraHom_characterCoordinate _ _ T h

theorem pointAlgebraHom_borelCharacterCoordinate_add (lam mu : characterLattice p.torus)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ p.negativeBorel.X) :
    AffineCoordinates.pointAlgebraHom p.negativeBorel T h
        (p.borelCharacterCoordinate (lam + mu)) =
      AffineCoordinates.pointAlgebraHom p.negativeBorel T h (p.borelCharacterCoordinate lam) *
        AffineCoordinates.pointAlgebraHom p.negativeBorel T h (p.borelCharacterCoordinate mu) := by
  rw [pointAlgebraHom_borelCharacterCoordinate, pointAlgebraHom_borelCharacterCoordinate,
    pointAlgebraHom_borelCharacterCoordinate, borelCharacter_add, characterEval_add]
  rfl

theorem pointAlgebraHom_borelCharacterCoordinate_zero
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ p.negativeBorel.X) :
    AffineCoordinates.pointAlgebraHom p.negativeBorel T h (p.borelCharacterCoordinate 0) = 1 := by
  rw [pointAlgebraHom_borelCharacterCoordinate, borelCharacter, map_zero, map_zero,
    characterEval_zero]
  rfl

/-- The extended character restricts to the original character on the torus. -/
theorem characterRestrict_torusToNegativeBorel_borelCharacter (lam : characterLattice p.torus) :
    characterRestrict p.torusToNegativeBorel (p.borelCharacter lam) =
      (rationalCharacters.equivCharacterLattice p.torus).symm lam := by
  rw [borelCharacter, ← AddMonoidHom.comp_apply, ← characterRestrict_comp,
    p.torusToNegativeBorel_comp_negativeBorelToTorus, characterRestrict_id,
    AddMonoidHom.id_apply]

/-- Every rational character of the negative Borel subgroup is the extension of
its restriction to the torus. -/
theorem eq_borelCharacter (χ : rationalCharacters p.negativeBorel) :
    χ = p.borelCharacter ((rationalCharacters.equivCharacterLattice p.torus)
      (characterRestrict p.torusToNegativeBorel χ)) := by
  rw [borelCharacter, AddEquiv.symm_apply_apply]
  exact ((Dynamic.parabolicCharacterEquiv p.isRepresentedBy_negativeBorelHom
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
    p.isRepresentedBy_centralizer_opposite).left_inv χ).symm

/-! ### The big cell -/

/-- Multiplication `U(ν) × P(ν⁻¹) ⟶ G` is an open immersion. -/
theorem isOpenImmersion_cellMultiplication :
    IsOpenImmersion
      (SubgroupFunctor.cellMultiplication p.positiveUnipotentHom p.negativeBorelHom).left := by
  have := p.isConnectedReductive.smooth
  exact oppositeCellStatement k G (Dynamic.oppositeCocharacter p.positiveGm) _ _
    p.positiveUnipotentHom p.negativeBorelHom
    (by
      change (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.oppositeCocharacter p.positiveGm))).IsRepresentedBy _
      simpa only [Dynamic.oppositeCocharacter_oppositeCocharacter] using
        p.isRepresentedBy_positiveUnipotentHom)
    p.isRepresentedBy_negativeBorelHom

/-- Some non-zero-divisor coordinate has its whole unit locus inside the big cell
`P(ν⁻¹) · U(ν)`: every point where it is a unit factors through the negative
Borel subgroup followed by the positive unipotent subgroup, on every scheme test. -/
theorem exists_cellCoordinate :
    ∃ q : AffineCoordinates.algebra G, q ∈ nonZeroDivisors (AffineCoordinates.algebra G) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        IsUnit (AffineCoordinates.pointAlgebraHom G T g q) →
          ∃ (a : T ⟶ p.negativeBorel.X) (u : T ⟶ p.positiveUnipotent.X),
            g = (a ≫ p.negativeBorelHom.hom.hom) * (u ≫ p.positiveUnipotentHom.hom.hom) := by
  classical
  let := p.isOpenImmersion_cellMultiplication
  let m := SubgroupFunctor.cellMultiplication p.positiveUnipotentHom p.negativeBorelHom
  let e : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let x : G.X.left := (1 : e ⟶ G.X).left (IsLocalRing.closedPoint k)
  have hm1 : CartesianMonoidalCategory.lift 1 1 ≫ m = (1 : e ⟶ G.X) := by
    rw [SubgroupFunctor.lift_cellMultiplication, MonObj.one_comp, MonObj.one_comp, mul_one]
  have hx : x ∈ m.left.opensRange := by
    refine ⟨(CartesianMonoidalCategory.lift (1 : e ⟶ _) (1 : e ⟶ _)).left
      (IsLocalRing.closedPoint k), ?_⟩
    change ((CartesianMonoidalCategory.lift (1 : e ⟶ _) (1 : e ⟶ _)).left ≫ m.left)
      (IsLocalRing.closedPoint k) = x
    rw [← Over.comp_left, hm1]
  obtain ⟨f, hfle, hxf⟩ := (isAffineOpen_top G.X.left).exists_basicOpen_le ⟨x, hx⟩ trivial
  let q₀ : AffineCoordinates.algebra G := (AffineCoordinates.globalAlgEquiv G).symm f
  have hq₀ : AffineCoordinates.globalAlgHom G q₀ = f :=
    (AffineCoordinates.globalAlgEquiv G).apply_symm_apply f
  refine ⟨AffineCoordinates.antipodeCoord G q₀, ?_, ?_⟩
  · have := AffineCoordinates.isDomain_of_isConnectedReductive G p.isConnectedReductive
    have := AffineCoordinates.nontrivial_algΓ_identityTest (k := k)
    have hunit : IsUnit (AffineCoordinates.pointAlgebraHom G e 1
        (AffineCoordinates.antipodeCoord G q₀)) := by
      rw [AffineCoordinates.pointAlgebraHom_antipode, inv_one,
        AffineCoordinates.isUnit_pointAlgebraHom_iff_range_subset_basicOpen, hq₀]
      have : Subsingleton e.left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    rw [h0, map_zero] at hunit
    exact not_isUnit_zero hunit
  · intro T g hg
    rw [AffineCoordinates.pointAlgebraHom_antipode] at hg
    have hsub := AffineCoordinates.range_point_subset_basicOpen_of_isUnit G g⁻¹ q₀ hg
    rw [hq₀] at hsub
    obtain ⟨a, b, he⟩ := SubgroupFunctor.exists_cell_factors_of_range_subset
      p.positiveUnipotentHom p.negativeBorelHom g⁻¹ (hsub.trans hfle)
    refine ⟨b⁻¹, a⁻¹, ?_⟩
    rw [GrpObj.inv_comp, GrpObj.inv_comp, ← mul_inv_rev, ← he, inv_inv]

/-- A chosen big-cell coordinate. -/
def cellCoordinate : AffineCoordinates.algebra G :=
  p.exists_cellCoordinate.choose

theorem cellCoordinate_mem_nonZeroDivisors :
    p.cellCoordinate ∈ nonZeroDivisors (AffineCoordinates.algebra G) :=
  p.exists_cellCoordinate.choose_spec.1

theorem exists_factors_of_isUnit_cellCoordinate
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (hg : IsUnit (AffineCoordinates.pointAlgebraHom G T g p.cellCoordinate)) :
    ∃ (a : T ⟶ p.negativeBorel.X) (u : T ⟶ p.positiveUnipotent.X),
      g = (a ≫ p.negativeBorelHom.hom.hom) * (u ≫ p.positiveUnipotentHom.hom.hom) :=
  p.exists_cellCoordinate.choose_spec.2 T g hg

/-! ### Realized weights -/

/-- A coordinate realizes `lam` when it is left covariant for the negative Borel
subgroup with the extended character of `lam`, invariant under right
multiplication by the positive unipotent subgroup, and has counit one. -/
def IsRealizedBy (lam : characterLattice p.torus) (f : AffineCoordinates.algebra G) : Prop :=
  f ∈ AffineCoordinates.leftCovariantSubspace p.negativeBorelHom
      (p.borelCharacterCoordinate lam) ∧
    f ∈ AffineCoordinates.rightInvariantSubspace p.positiveUnipotentHom ∧
      AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G) f = 1

/-- A torus character is realized when some coordinate realizes it. -/
def IsRealizedWeight (lam : characterLattice p.torus) : Prop :=
  ∃ f : AffineCoordinates.algebra G, p.IsRealizedBy lam f

/-- The constant coordinate realizes the zero character. -/
theorem isRealizedBy_zero : p.IsRealizedBy 0 1 := by
  refine ⟨?_, ?_, map_one _⟩
  · rw [AffineCoordinates.mem_leftCovariantSubspace_iff_points]
    intro T h g
    rw [map_one, map_one, pointAlgebraHom_borelCharacterCoordinate_zero, mul_one]
  · intro T u g
    rw [map_one, map_one]

theorem isRealizedWeight_zero : p.IsRealizedWeight 0 :=
  ⟨1, p.isRealizedBy_zero⟩

section RealizedLemmas

variable {p}

/-- Products of realizing coordinates realize the sum of the characters. -/
theorem IsRealizedBy.mul {lam mu : characterLattice p.torus}
    {f f' : AffineCoordinates.algebra G}
    (hf : p.IsRealizedBy lam f) (hf' : p.IsRealizedBy mu f') :
    p.IsRealizedBy (lam + mu) (f * f') := by
  refine ⟨?_, ?_, ?_⟩
  · have h₁ := (AffineCoordinates.mem_leftCovariantSubspace_iff_points _ _ _).mp hf.1
    have h₂ := (AffineCoordinates.mem_leftCovariantSubspace_iff_points _ _ _).mp hf'.1
    rw [AffineCoordinates.mem_leftCovariantSubspace_iff_points]
    intro T h g
    rw [map_mul, map_mul, h₁ T h g, h₂ T h g,
      pointAlgebraHom_borelCharacterCoordinate_add]
    ring
  · intro T u g
    rw [map_mul, map_mul, hf.2.1 T u g, hf'.2.1 T u g]
  · rw [map_mul, hf.2.2, hf'.2.2, mul_one]

theorem IsRealizedWeight.add {lam mu : characterLattice p.torus}
    (h : p.IsRealizedWeight lam) (h' : p.IsRealizedWeight mu) :
    p.IsRealizedWeight (lam + mu) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  exact ⟨f * f', hf.mul hf'⟩

theorem IsRealizedBy.pow {lam : characterLattice p.torus} {f : AffineCoordinates.algebra G}
    (hf : p.IsRealizedBy lam f) (n : ℕ) : p.IsRealizedBy (n • lam) (f ^ n) := by
  induction n with
  | zero => simpa using isRealizedBy_zero p
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hf

/-- The covariant socle of a realizing coordinate is an irreducible representation. -/
theorem IsRealizedBy.isIrreducible {lam : characterLattice p.torus}
    {f : AffineCoordinates.algebra G} (hf : p.IsRealizedBy lam f) :
    (Chevalley.affineCovariantSocleRepresentation G f).IsIrreducible :=
  Chevalley.affineCovariantSocleRepresentation_isIrreducible G p.negativeBorelHom
    p.positiveUnipotentHom p.isUnipotent_positiveUnipotent _
    p.cellCoordinate_mem_nonZeroDivisors p.exists_factors_of_isUnit_cellCoordinate
    hf.1 hf.2.1 hf.2.2

end RealizedLemmas

end SplitPinning
end Langlands.GroupScheme
