import Langlands.GroupScheme.Reductive.SuppliedRootWordCoordinates
import Langlands.GroupScheme.Rational.HighestWeightWordCoordinates

/-! # Full word coordinates from supplied linked simple-root data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme
namespace SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- A supplied family of full linked root coordinates, restricted to simple roots.
This type does not choose or assert the existence of any root map. -/
abbrev SimpleRootCoordinateFamily :=
  (i : p.base.support) → LinkedRootParametrization p.inclusion
    (p.rootDatum.root i) (p.rootDatum.coroot i)

variable (c : p.SimpleRootCoordinateFamily)

/-- The negative simple map in the supplied family. -/
def suppliedSimpleLoweringMap (i : p.base.support) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  (c i).negative

variable [Fintype p.rootIndex]
    (s : p.SimpleReflectionRepresentatives)
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)

/-- A positive word listing all positive roots gives full opposite-unipotent
coordinates for the supplied full lowering maps, on every relative test scheme. -/
theorem suppliedWord_orderedProduct_points
    (l : List p.base.support)
    (hn : (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup)
    (hall : ∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
      p.base.IsPos j)
    (Z : Over (Spec (CommRingCat.of k))) :
    let x := p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l
    Function.Injective (LocalSplitCell.orderedProduct id x.get Z) ∧
      ∀ g : Z ⟶ G.X,
        g ∈ (Dynamic.unipotent
          (CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion)).carrier Z ↔
            ∃ w, LocalSplitCell.orderedProduct id x.get Z w = g := by
  let x := p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l
  let rs := Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l
  have hlen : x.length = rs.length := by
    simp only [x, rs, length_reflectionWordLoweringMaps,
      Langlands.PositiveRootWord.length_wordRoots]
  let r : Fin x.length → p.rootIndex := fun j =>
    rs.get ⟨j, by simpa only [← hlen] using j.isLt⟩
  let a : Fin x.length → characterLattice p.torus := fun j => -p.rootDatum.root (r j)
  have hrinj : Function.Injective r := by
    intro i j hij
    have hh := (List.Nodup.get_inj_iff hn).mp hij
    exact Fin.ext (congrArg (fun z : Fin rs.length => z.val) hh)
  have hainj : Function.Injective a :=
    neg_injective.comp (p.rootDatum.root.injective.comp hrinj)
  have harange : Set.range a =
      {β | β ∈ relativeRoots p.inclusion ∧ 0 < latticePairing p.torus β (-ν₀)} := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨p.isRootDatum.neg_mem_roots (p.root_mem_relativeRoots (r j)), ?_⟩
      change 0 < latticePairing p.torus (-p.rootDatum.root (r j)) (-ν₀)
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
        p.base hspan (r j)).mpr ((hall (r j)).mp (List.get_mem _ _))
    · rintro ⟨hβ, hpos⟩
      have hneg : -β ∈ roots p.inclusion := p.isRootDatum.neg_mem_roots hβ
      rw [← p.isRootDatum.2.1] at hneg
      obtain ⟨j, hj⟩ := hneg
      have hjpos : p.base.IsPos j := by
        apply (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
          p.base hspan j).mp
        rw [hj]
        simpa only [map_neg, LinearMap.neg_apply] using hpos
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hall j).mpr hjpos)
      refine ⟨⟨i, by simpa only [hlen] using i.isLt⟩, ?_⟩
      change -p.rootDatum.root (rs.get i) = β
      rw [hi, hj, neg_neg]
  have hrep := p.reflectionWordLoweringMaps_represents_of_fullSimpleMaps s
    (p.suppliedSimpleLoweringMap c) (fun i => (c i).negative_represents) l
  apply SplitBigCell.orderedProduct_points G p.isConnectedReductive p.torus p.inclusion
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus) (-ν₀) p.reducedRays
    id x.get a hainj harange ?_ Z
  intro j
  exact hrep.get j.isLt (by change j.val < rs.length; rw [← hlen]; exact j.isLt)

variable [Infinite k] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (m : ℕ)

/-- The supplied linked maps retain the nonzero constant-degree endpoint of every
word in any supplied highest-weight representation of weight `m rho`. -/
theorem suppliedWordCoefficient_ne_zero
    (hρ : p.IsHighestWeight ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (l : List p.base.support) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hv0 : v ≠ 0) :
    p.reflectionWordCoefficient s (p.suppliedSimpleLoweringMap c) ρ m l v ≠ 0 := by
  have hα (i : p.base.support) : 0 < p.rootDatum.toLinearMap (p.rootDatum.root i)
      (p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho
        p.rootDatum p.base hspan)) :=
    (Langlands.IntegralWeylVector.pairing_root_polarization_rho_pos_iff
      p.rootDatum p.base hspan i).mpr (p.base.isPos_of_mem_support i.property)
  have hm (i : p.base.support) :
      latticePairing p.torus (m • Langlands.IntegralWeylVector.rho
        p.rootDatum p.base hspan) (p.rootDatum.coroot i) = (m : ℤ) := by
    rw [← p.isRootDatum.1, map_nsmul, LinearMap.smul_apply,
      Langlands.IntegralWeylVector.pairing_rho_simple]
    simp
  obtain ⟨b, hb⟩ := p.highestWeight_reflectionWordCoefficient_eq_unit_smul
    s (p.suppliedSimpleLoweringMap c) ρ _ hspan hρ
    (fun i => (c i).positive)
    (fun i => (c i).positive_equivariant)
    (fun i => (c i).negative_equivariant)
    hα m hm (fun i => (c i).relation) hv hv0 l
  rw [hb]
  intro hz
  have hz' : (ρ.rationalMatrix (p.reflectionWordPoint s l) : Matrix n n k) *ᵥ v = 0 :=
    (smul_eq_zero.mp hz).resolve_left b.ne_zero
  apply hv0
  apply Matrix.mulVec_injective_of_isUnit
    (Units.isUnit (ρ.rationalMatrix (p.reflectionWordPoint s l)))
  simpa only [Matrix.mulVec_zero] using hz'

/-- A supplied linked simple-root family gives a positive word whose factors are
full opposite-unipotent coordinates on every test scheme and whose actual
constant-degree action coefficient is nonzero on each nonzero highest vector. -/
theorem exists_supplied_highestWeight_wordCoordinates
    (hρ : p.IsHighestWeight ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)) :
    ∃ (s : p.SimpleReflectionRepresentatives) (l : List p.base.support),
      Langlands.PositiveRootWord.IsPositive p.rootDatum p.base l ∧
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup ∧
      (∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
        p.base.IsPos j) ∧
      (∀ Z : Over (Spec (CommRingCat.of k)),
        let x := p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l
        Function.Injective (LocalSplitCell.orderedProduct id x.get Z) ∧
          ∀ g : Z ⟶ G.X,
            g ∈ (Dynamic.unipotent
              (CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion)).carrier Z ↔
                ∃ w, LocalSplitCell.orderedProduct id x.get Z w = g) ∧
      ∀ (a : Fin (p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l).length →₀ ℕ),
        (∀ j, a j = m) → ∀ v : n → k,
        v ∈ p.representationWeightSpace ρ
          (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan) → v ≠ 0 →
        OrderedAdditiveProducts.orderedCoefficients ρ
          (p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l).get a v ≠ 0 := by
  let := p.isReduced
  let s : p.SimpleReflectionRepresentatives := p.simpleReflectionRepresentative
  obtain ⟨l, hl, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  refine ⟨s, l, hl, hn, hall,
    p.suppliedWord_orderedProduct_points c s hspan l hn hall, ?_⟩
  intro a ha v hv hv0
  rw [p.orderedCoefficients_reflectionWord s (p.suppliedSimpleLoweringMap c) ρ m l a ha]
  exact p.suppliedWordCoefficient_ne_zero c s hspan ρ m hρ l hv hv0

end SplitPinning
end Langlands.GroupScheme
