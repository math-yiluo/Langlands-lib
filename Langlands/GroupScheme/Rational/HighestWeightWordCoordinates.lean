import Langlands.GroupScheme.Rational.HighestWeightWordEndpoint
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.SplitBigCellField

/-! # Full opposite-root coordinates with a nonzero highest-weight coefficient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace VectorGroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational conjugation preserves monicity of an actual additive map. -/
theorem mono_conjugateMap
    (x : groupScheme (CommRingCat.of k) 1 ⟶ G) [Mono x.hom.hom]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    Mono (conjugateMap x g).hom.hom := by
  change Mono (x.hom.hom ≫ (G.innerIso g).hom.hom.hom)
  infer_instance

end VectorGroup

namespace SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The fixed simple lowering maps supplied by the linked full-root construction. -/
def linkedSimpleLoweringMap (i : p.base.support) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  (p.linkedRootParametrization i).negative

/-- Every conjugated lowering map is monic when the original simple maps are. -/
theorem mono_reflectionWordLoweringMaps
    (s : p.SimpleReflectionRepresentatives)
    (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
    (hmono : ∀ i, Mono (xm i).hom.hom)
    (l : List p.base.support) :
    ∀ x ∈ p.reflectionWordLoweringMaps s xm l, Mono x.hom.hom := by
  induction l with
  | nil => simp [reflectionWordLoweringMaps]
  | cons i l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · let := hmono i
      exact VectorGroup.mono_conjugateMap _ _
    · exact ih x hx

/-- With full simple maps, each word factor represents its entire successive
negative root subgroup, on all relative test schemes. -/
theorem reflectionWordLoweringMaps_represents
    (s : p.SimpleReflectionRepresentatives)
    (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
    (hmono : ∀ i, Mono (xm i).hom.hom)
    (hequiv : ∀ i, VectorGroup.IsTorusEquivariant p.inclusion (xm i)
      (-p.rootDatum.root i))
    (l : List p.base.support) :
    List.Forall₂
      (fun x j => (RelativeRoot.subgroup p.inclusion
        (-p.rootDatum.root j)).IsRepresentedBy x)
      (p.reflectionWordLoweringMaps s xm l)
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l) := by
  have he := p.reflectionWordLoweringMaps_equivariant s xm hequiv l
  rw [List.forall₂_iff_get] at he ⊢
  refine ⟨he.1, ?_⟩
  intro j hx hj
  let x := (p.reflectionWordLoweringMaps s xm l).get ⟨j, hx⟩
  let r := (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).get ⟨j, hj⟩
  have : Mono x.hom.hom :=
    p.mono_reflectionWordLoweringMaps s xm hmono l x (List.get_mem _ _)
  have hroot := p.root_mem_relativeRoots r
  obtain ⟨r', hr'⟩ := p.rootDatum.neg_root_mem r
  have hhigh : RelativeRoot.HasNoHigherRoots p.inclusion (-p.rootDatum.root r) := by
    rw [← hr']
    exact p.hasNoHigherRoots r'
  exact (he.2 j hx hj).represents_root p.isConnectedReductive p.isSplitTorus
    p.isMaximalTorus (p.isRootDatum.neg_mem_roots hroot) hhigh

/-- Every pair of positive root rays of a supplied pinning has unique root and
positive integral multiplicity. -/
theorem reducedRays : SplitBigCell.ReducedRays p.inclusion := by
  let : p.rootDatum.IsReduced := p.isReduced
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice p.torus) :=
    IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice p.torus) :=
    p.isSplitTorus.character_toRat_injective.isAddTorsionFree toRat
  intro a ha b hb r t hr ht he
  rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hlin : ¬ LinearIndependent ℤ ![p.rootDatum.root i, p.rootDatum.root j] := by
    simp only [LinearIndependent.pair_iff, not_forall]
    refine ⟨(r : ℤ), -(t : ℤ), ?_, ?_⟩
    · simpa only [neg_smul, natCast_zsmul, add_neg_eq_zero] using he
    · simp only [Int.natCast_eq_zero, neg_eq_zero]
      omega
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := p.rootDatum) i j hlin with hij | hij
  · refine ⟨hij, ?_⟩
    rw [hij] at he
    apply Int.ofNat_inj.mp
    exact (smul_left_injective ℤ (p.rootDatum.ne_zero j))
      (by simpa only [natCast_zsmul] using he)
  · exfalso
    rw [hij, smul_neg] at he
    have he' : (-(r : ℤ)) • p.rootDatum.root j = (t : ℤ) • p.rootDatum.root j := by
      simpa only [neg_smul, natCast_zsmul] using he
    have := (smul_left_injective ℤ (p.rootDatum.ne_zero j)) he'
    omega

variable [Fintype p.rootIndex]
    (s : p.SimpleReflectionRepresentatives)
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)

/-- A positive word listing all positive roots gives full opposite-unipotent
coordinates for the fixed linked lowering maps, on every relative test scheme. -/
theorem linkedWord_orderedProduct_points
    (l : List p.base.support)
    (hn : (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup)
    (hall : ∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
      p.base.IsPos j)
    (Z : Over (Spec (CommRingCat.of k))) :
    let x := p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l
    Function.Injective (LocalSplitCell.orderedProduct id x.get Z) ∧
      ∀ g : Z ⟶ G.X,
        g ∈ (Dynamic.unipotent
          (CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion)).carrier Z ↔
            ∃ w, LocalSplitCell.orderedProduct id x.get Z w = g := by
  let x := p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l
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
  have hrep := p.reflectionWordLoweringMaps_represents s p.linkedSimpleLoweringMap
    (fun i => (p.linkedRootParametrization i).negative_represents.1)
    (fun i => (p.linkedRootParametrization i).negative_equivariant) l
  apply SplitBigCell.orderedProduct_points G p.isConnectedReductive p.torus p.inclusion
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus) (-ν₀) p.reducedRays
    id x.get a hainj harange ?_ Z
  intro j
  exact hrep.get j.isLt (by change j.val < rs.length; rw [← hlen]; exact j.isLt)

variable [Infinite k] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (m : ℕ)

/-- The fixed linked maps retain the nonzero constant-degree endpoint of every
word in any supplied highest-weight representation of weight `m rho`. -/
theorem linkedWordCoefficient_ne_zero
    (hρ : p.IsHighestWeight ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (l : List p.base.support) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hv0 : v ≠ 0) :
    p.reflectionWordCoefficient s p.linkedSimpleLoweringMap ρ m l v ≠ 0 := by
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
  obtain ⟨c, hc⟩ := p.highestWeight_reflectionWordCoefficient_eq_unit_smul
    s p.linkedSimpleLoweringMap ρ _ hspan hρ
    (fun i => (p.linkedRootParametrization i).positive)
    (fun i => (p.linkedRootParametrization i).positive_equivariant)
    (fun i => (p.linkedRootParametrization i).negative_equivariant)
    hα m hm (fun i => (p.linkedRootParametrization i).relation) hv hv0 l
  rw [hc]
  intro hz
  have hz' : (ρ.rationalMatrix (p.reflectionWordPoint s l) : Matrix n n k) *ᵥ v = 0 :=
    (smul_eq_zero.mp hz).resolve_left c.ne_zero
  apply hv0
  apply Matrix.mulVec_injective_of_isUnit
    (Units.isUnit (ρ.rationalMatrix (p.reflectionWordPoint s l)))
  simpa only [Matrix.mulVec_zero] using hz'

/-- The pinning supplies a single positive word whose fixed linked factors are
full opposite-unipotent coordinates on every test scheme and whose actual
constant-degree action coefficient is nonzero on each nonzero highest vector. -/
theorem exists_highestWeight_wordCoordinates
    (hρ : p.IsHighestWeight ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)) :
    ∃ (s : p.SimpleReflectionRepresentatives) (l : List p.base.support),
      Langlands.PositiveRootWord.IsPositive p.rootDatum p.base l ∧
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup ∧
      (∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
        p.base.IsPos j) ∧
      (∀ Z : Over (Spec (CommRingCat.of k)),
        let x := p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l
        Function.Injective (LocalSplitCell.orderedProduct id x.get Z) ∧
          ∀ g : Z ⟶ G.X,
            g ∈ (Dynamic.unipotent
              (CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion)).carrier Z ↔
                ∃ w, LocalSplitCell.orderedProduct id x.get Z w = g) ∧
      ∀ (a : Fin (p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l).length →₀ ℕ),
        (∀ j, a j = m) → ∀ v : n → k,
        v ∈ p.representationWeightSpace ρ
          (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan) → v ≠ 0 →
        OrderedAdditiveProducts.orderedCoefficients ρ
          (p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l).get a v ≠ 0 := by
  let := p.isReduced
  let s : p.SimpleReflectionRepresentatives := p.simpleReflectionRepresentative
  obtain ⟨l, hl, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  refine ⟨s, l, hl, hn, hall,
    p.linkedWord_orderedProduct_points s hspan l hn hall, ?_⟩
  intro a ha v hv hv0
  rw [p.orderedCoefficients_reflectionWord s p.linkedSimpleLoweringMap ρ m l a ha]
  exact p.linkedWordCoefficient_ne_zero s hspan ρ m hρ l hv hv0

end SplitPinning
end Langlands.GroupScheme
