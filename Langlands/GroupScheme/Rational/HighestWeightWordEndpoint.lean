import Langlands.GroupScheme.Rational.HighestWeightRootEndpoint
import Langlands.GroupScheme.Rational.NormalizedRootExistenceProof
import Langlands.LinearAlgebra.PositiveRootWord
import Langlands.GroupScheme.MatrixRepresentation.AdditiveConjugation
import Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveProducts

/-! # Actual lowering endpoints along simple-reflection words -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (s : p.SimpleReflectionRepresentatives)

/-- The actual rational normalizer product, with a new head multiplied on
the right of the product of the tail. -/
def reflectionWordPoint : List p.base.support →
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
  | [] => 1
  | i :: l => reflectionWordPoint l * (s i).point

/-- The actual torus automorphism of the rational word product. -/
def reflectionWordTorusAut : List p.base.support → (p.torus ≅ p.torus)
  | [] => Iso.refl p.torus
  | i :: l => (s i).torusAut ≪≫ reflectionWordTorusAut l

/-- The accumulated point normalizes the original torus. -/
theorem reflectionWordPoint_normalizes (l : List p.base.support) :
    IsNormalizingPoint p.inclusion (p.reflectionWordPoint s l)
      (p.reflectionWordTorusAut s l) := by
  induction l with
  | nil => exact IsNormalizingPoint.one
  | cons i l ih => exact ih.mul (s i).normalizes

/-- The character action of the actual rational word product is exactly
the product in the root-datum automorphism group. -/
theorem characterAut_reflectionWordTorusAut (l : List p.base.support) :
    characterAut (p.reflectionWordTorusAut s l) =
      (Langlands.PositiveRootWord.wordAut p.rootDatum p.base l).weightEquiv := by
  induction l with
  | nil =>
    ext χ
    exact Category.id_comp χ
  | cons i l ih =>
    ext χ
    change characterAut (p.reflectionWordTorusAut s l)
      (characterAut (s i).torusAut χ) = _
    rw [(s i).characterAut_eq, ih]
    rfl

variable
    (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))

/-- At a new head, conjugate its original simple lowering map by the
actual rational product belonging to the tail. -/
def reflectionWordLoweringMaps :
    List p.base.support → List (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
  | [] => []
  | i :: l => VectorGroup.conjugateMap (xm i) (p.reflectionWordPoint s l) ::
      reflectionWordLoweringMaps l

@[simp] theorem length_reflectionWordLoweringMaps (l : List p.base.support) :
    (p.reflectionWordLoweringMaps s xm l).length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [reflectionWordLoweringMaps, ih]

/-- Every conjugated lowering map has the negative of its successive
root as its character, on every relative test scheme. -/
theorem reflectionWordLoweringMaps_equivariant
    (hxm : ∀ i, VectorGroup.IsTorusEquivariant p.inclusion (xm i)
      (-p.rootDatum.root i)) (l : List p.base.support) :
    List.Forall₂
      (fun x j => VectorGroup.IsTorusEquivariant p.inclusion x (-p.rootDatum.root j))
      (p.reflectionWordLoweringMaps s xm l)
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons i l ih =>
    refine List.Forall₂.cons ?_ ih
    have h := (hxm i).conjugateMap (p.reflectionWordPoint_normalizes s l)
    rw [p.characterAut_reflectionWordTorusAut s l, map_neg] at h
    convert h using 1
    exact congrArg Neg.neg (RootPairing.Equiv.root_indexEquiv_eq_smul
      p.rootDatum (i : p.rootIndex)
      (Langlands.PositiveRootWord.wordAut p.rootDatum p.base l))

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The ordered product of original degree-`m` operators of the actual
conjugated lowering maps. -/
def reflectionWordCoefficient (m : ℕ) (l : List p.base.support) :
    Module.End k (n → k) :=
  ((p.reflectionWordLoweringMaps s xm l).map
    (fun x => dividedPower (ρ.restrict x) m)).prod

/-- Single-root endpoint equations telescope along the actual conjugated
maps. No positivity of the word is needed for this identity. -/
theorem reflectionWordCoefficient_eq_unit_smul (m : ℕ) {v : n → k}
    (he : ∀ i : p.base.support, ∃ c : kˣ, dividedPower (ρ.restrict (xm i)) m v =
      (c : k) • ((ρ.rationalMatrix (s i).point : Matrix n n k) *ᵥ v))
    (l : List p.base.support) :
    ∃ c : kˣ, p.reflectionWordCoefficient s xm ρ m l v =
      (c : k) • ((ρ.rationalMatrix (p.reflectionWordPoint s l) : Matrix n n k) *ᵥ v) := by
  induction l with
  | nil =>
    refine ⟨1, ?_⟩
    simp [reflectionWordCoefficient, reflectionWordLoweringMaps, reflectionWordPoint]
  | cons i l ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := he i
    refine ⟨c * d, ?_⟩
    change dividedPower (ρ.restrict
      (VectorGroup.conjugateMap (xm i) (p.reflectionWordPoint s l))) m
        (p.reflectionWordCoefficient s xm ρ m l v) = _
    rw [hc, map_smul, dividedPower_conjugateMap_apply, hd, Matrix.mulVec_smul,
      smul_smul, reflectionWordPoint, map_mul, Units.val_mul,
      Matrix.mulVec_mulVec, Units.val_mul]

/-- The same product is the coefficient of the genuine ordered polynomial
action at any tuple with every coordinate equal to `m`. -/
theorem orderedCoefficients_reflectionWord (m : ℕ) (l : List p.base.support)
    (a : Fin (p.reflectionWordLoweringMaps s xm l).length →₀ ℕ)
    (ha : ∀ j, a j = m) :
    MatrixRepresentation.OrderedAdditiveProducts.orderedCoefficients ρ
      (p.reflectionWordLoweringMaps s xm l).get a =
        p.reflectionWordCoefficient s xm ρ m l := by
  rw [MatrixRepresentation.OrderedAdditiveProducts.orderedCoefficients_eq_prod]
  simp only [ha, reflectionWordCoefficient]
  congr 1
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map (fun x => dividedPower (ρ.restrict x) m))
      (List.ofFn_get (p.reflectionWordLoweringMaps s xm l))

variable [Fintype p.rootIndex] [Infinite k]
    (lam : characterLattice p.torus)
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hρ : p.IsHighestWeight ρ lam)
    (xp : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
    (hxp : ∀ i, VectorGroup.IsTorusEquivariant p.inclusion (xp i)
      (p.rootDatum.root i))
    (hxm : ∀ i, VectorGroup.IsTorusEquivariant p.inclusion (xm i)
      (-p.rootDatum.root i))
    (hα : ∀ i : p.base.support, 0 < p.rootDatum.toLinearMap (p.rootDatum.root i)
      (p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho
        p.rootDatum p.base hspan)))
    (m : ℕ)
    (hm : ∀ i : p.base.support, latticePairing p.torus lam
      (p.rootDatum.coroot i) = (m : ℤ))
    (hcell : ∀ (i : p.base.support) (Z : Over (Spec (CommRingCat.of k))),
      RootCell.RelationOver p.inclusion (p.rootDatum.coroot i) (xp i) (xm i) Z)

include hρ hxp hxm hα hm hcell

/-- The original highest-weight endpoint theorem supplies every single-root
equation needed for the word product. -/
theorem highestWeight_reflectionWordCoefficient_eq_unit_smul
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0)
    (l : List p.base.support) :
    ∃ c : kˣ, p.reflectionWordCoefficient s xm ρ m l v =
      (c : k) • ((ρ.rationalMatrix (p.reflectionWordPoint s l) : Matrix n n k) *ᵥ v) := by
  apply p.reflectionWordCoefficient_eq_unit_smul s xm ρ m ?_ l
  intro i
  exact p.highestWeight_rootEndpoint_eq_unit_smul ρ lam hspan hρ i
    (hxp i) (hxm i) (hα i) m (hm i) (hcell i)
    (s i).normalizes (s i).characterAut_eq hv hv0

omit hρ hxp hxm hα hm hcell in
/-- For highest weight `m rho`, linked simple maps and a positive word exist
whose actual ordered degree-`m` coefficient is nonzero on every nonzero
highest vector. All positive roots occur exactly once. -/
theorem exists_highestWeight_positiveWord
    (hρ : p.IsHighestWeight ρ (m • Langlands.IntegralWeylVector.rho
      p.rootDatum p.base hspan)) :
    ∃ (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
      (l : List p.base.support),
      Langlands.PositiveRootWord.IsPositive p.rootDatum p.base l ∧
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup ∧
      (∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
        p.base.IsPos j) ∧
      List.Forall₂
        (fun x j => VectorGroup.IsTorusEquivariant p.inclusion x (-p.rootDatum.root j))
        (p.reflectionWordLoweringMaps s xm l)
        (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l) ∧
      ∀ v : n → k,
        v ∈ p.representationWeightSpace ρ (m • Langlands.IntegralWeylVector.rho
          p.rootDatum p.base hspan) → v ≠ 0 →
        p.reflectionWordCoefficient s xm ρ m l v ≠ 0 := by
  let := p.isReduced
  choose xp xm hxp hxm hcell using
    (fun i : p.base.support => p.hasRootRankOneRelations i)
  obtain ⟨l, hl, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  refine ⟨xm, l, hl, hn, hall, p.reflectionWordLoweringMaps_equivariant s xm hxm l, ?_⟩
  intro v hv hv0
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
    s xm ρ _ hspan hρ xp hxp hxm hα m hm hcell hv hv0 l
  rw [hc]
  intro hz
  have hz' : (ρ.rationalMatrix (p.reflectionWordPoint s l) : Matrix n n k) *ᵥ v = 0 :=
    (smul_eq_zero.mp hz).resolve_left c.ne_zero
  apply hv0
  apply Matrix.mulVec_injective_of_isUnit
    (Units.isUnit (ρ.rationalMatrix (p.reflectionWordPoint s l)))
  simpa only [Matrix.mulVec_zero] using hz'

omit hρ hxp hxm hα hm hcell in
/-- The pinning also supplies the rational simple-reflection representatives.
Thus the nonzero coefficient is an actual coefficient of a supplied
representation, with no separate representative or root-cell premise. -/
theorem exists_highestWeight_nonzero_orderedCoefficient
    (hρ : p.IsHighestWeight ρ (m • Langlands.IntegralWeylVector.rho
      p.rootDatum p.base hspan)) :
    ∃ (s : p.SimpleReflectionRepresentatives)
      (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
      (l : List p.base.support),
      Langlands.PositiveRootWord.IsPositive p.rootDatum p.base l ∧
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l).Nodup ∧
      (∀ j, j ∈ Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l ↔
        p.base.IsPos j) ∧
      List.Forall₂
        (fun x j => VectorGroup.IsTorusEquivariant p.inclusion x (-p.rootDatum.root j))
        (p.reflectionWordLoweringMaps s xm l)
        (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l) ∧
      ∀ (a : Fin (p.reflectionWordLoweringMaps s xm l).length →₀ ℕ),
        (∀ j, a j = m) → ∀ v : n → k,
        v ∈ p.representationWeightSpace ρ (m • Langlands.IntegralWeylVector.rho
          p.rootDatum p.base hspan) → v ≠ 0 →
        MatrixRepresentation.OrderedAdditiveProducts.orderedCoefficients ρ
          (p.reflectionWordLoweringMaps s xm l).get a v ≠ 0 := by
  let s : p.SimpleReflectionRepresentatives := p.simpleReflectionRepresentative
  obtain ⟨xm, l, hl, hn, hall, he, hv⟩ :=
    p.exists_highestWeight_positiveWord s ρ hspan m hρ
  refine ⟨s, xm, l, hl, hn, hall, he, ?_⟩
  intro a ha v hvw hv0
  rw [p.orderedCoefficients_reflectionWord s xm ρ m l a ha]
  exact hv v hvw hv0

end Langlands.GroupScheme.SplitPinning
