import Langlands.GroupScheme.Rational.HighestWeightWordCoordinates
import Langlands.GroupScheme.MatrixRepresentation.OrderedFrobeniusCyclicity
import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # Actual Frobenius orbits of supplied highest-weight vectors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation OrderedAdditiveProducts OrderedAdditiveCoordinates
open OrderedAdditiveTruncation FrobeniusPolynomialBox OrderedFrobeniusCyclicity

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (s : p.SimpleReflectionRepresentatives)
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (l : List p.base.support)

local instance frobeniusOrbitIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "U" => Dynamic.Affine.unipotentScheme λ₋
local notation "iU" => Dynamic.Affine.unipotentHom λ₋
local notation "maps" => p.reflectionWordLoweringMaps s p.linkedSimpleLoweringMap l
local notation "roots" => Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l

local instance frobeniusOrbitUnipotentIsAffineHom : IsAffineHom (U).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

/-- The successive original root index of a fixed linked word factor. -/
def linkedWordRoot (j : Fin (maps).length) : p.rootIndex :=
  (roots).get ⟨j.val, by
    simpa only [Langlands.PositiveRootWord.length_wordRoots,
      length_reflectionWordLoweringMaps] using j.isLt⟩

/-- The actual character of a fixed linked word factor. -/
def linkedWordWeight (j : Fin (maps).length) : characterLattice p.torus :=
  -p.rootDatum.root (p.linkedWordRoot s l j)

omit [Fintype p.rootIndex] in
theorem linkedWord_equivariant (j : Fin (maps).length) :
    VectorGroup.IsTorusEquivariant p.inclusion ((maps).get j)
      (p.linkedWordWeight s l j) := by
  have h := p.reflectionWordLoweringMaps_equivariant s p.linkedSimpleLoweringMap
    (fun i => (p.linkedRootParametrization i).negative_equivariant) l
  exact h.get j.isLt (by
    simpa only [Langlands.PositiveRootWord.length_wordRoots,
      length_reflectionWordLoweringMaps] using j.isLt)

/-- Every word factor has positive height for the opposite-rho contraction. -/
theorem linkedWordWeight_pairing_pos (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j)
    (j : Fin (maps).length) :
    0 < latticePairing p.torus (p.linkedWordWeight s l j) (-ν₀) := by
  change 0 < latticePairing p.torus (-p.rootDatum.root (p.linkedWordRoot s l j)) (-ν₀)
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
    p.base hspan (p.linkedWordRoot s l j)).mpr ((hall _).mp (List.get_mem roots _))

/-- The entire image of each fixed word factor lies in the actual opposite
dynamic unipotent functor. -/
theorem linkedWord_range_le_unipotent
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (j : Fin (maps).length) :
    SubgroupFunctor.range ((maps).get j) ≤ Dynamic.unipotent λ₋ := by
  have hrep := p.reflectionWordLoweringMaps_represents s p.linkedSimpleLoweringMap
    (fun i => (p.linkedRootParametrization i).negative_represents.1)
    (fun i => (p.linkedRootParametrization i).negative_equivariant) l
  have hr := hrep.get j.isLt (by
    simpa only [Langlands.PositiveRootWord.length_wordRoots,
      length_reflectionWordLoweringMaps] using j.isLt)
  exact hr.2.le.trans (RelativeRoot.subgroup_le_dynamicUnipotent
    p.inclusion (-ν₀) (p.linkedWordWeight_pairing_pos s hspan l hall j))

/-- The original linked word factors lifted into the actual opposite
dynamic unipotent representative. -/
def linkedWordUnipotentMap
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (j : Fin (maps).length) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ U :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋) ((maps).get j)
    (p.linkedWord_range_le_unipotent s hspan l hall j)

theorem linkedWordUnipotentMap_comp
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (j : Fin (maps).length) :
    p.linkedWordUnipotentMap s hspan l hall j ≫ iU = (maps).get j :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋) ((maps).get j)
    (p.linkedWord_range_le_unipotent s hspan l hall j)

/-- Conjugation by the original torus on the actual opposite unipotent group. -/
def oppositeRhoUnipotentAction : AutomorphicAction p.torus.toGrp U :=
  (AutomorphicAction.conjugation p.inclusion).onRepresentedSubgroup iU
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
    (Dynamic.unipotent_isStable_conjugation p.inclusion
      (CommGroupScheme.groupHom (-ν₀)))

theorem oppositeRhoUnipotentAction_comp
    {Z : Over (Spec (CommRingCat.of k))}
    (t : Z ⟶ p.torus.X) (g : Z ⟶ (U).X) :
    (p.oppositeRhoUnipotentAction hspan).act t g ≫ (iU).hom.hom =
      (t ≫ p.inclusion.hom.hom) * (g ≫ (iU).hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ := by
  unfold oppositeRhoUnipotentAction
  rw [AutomorphicAction.onRepresentedSubgroup_act_comp, AutomorphicAction.conjugation_act]

theorem linkedWordUnipotentMap_scaling
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j)
    (A : CommAlgCat.{u} k) (t : GroupScheme.affinePoints p.torus.toGrp A)
    (c : A) (j : Fin (maps).length) :
    (p.oppositeRhoUnipotentAction hspan).act t
      (VectorGroup.affinePoint (R := CommRingCat.of k) A (fun _ : Fin 1 => c) ≫
        (p.linkedWordUnipotentMap s hspan l hall j).hom.hom) =
      VectorGroup.affinePoint (R := CommRingCat.of k) A
        (fun _ : Fin 1 => (Lie.characterValue (p.linkedWordWeight s l j) t : A) * c) ≫
          (p.linkedWordUnipotentMap s hspan l hall j).hom.hom := by
  let : Mono (iU).hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋).1
  apply (cancel_mono (iU).hom.hom).mp
  rw [oppositeRhoUnipotentAction_comp]
  have hcomp := congrArg (fun f => f.hom.hom)
    (p.linkedWordUnipotentMap_comp s hspan l hall j)
  change (p.linkedWordUnipotentMap s hspan l hall j).hom.hom ≫ (iU).hom.hom =
    ((maps).get j).hom.hom at hcomp
  simp only [Category.assoc, hcomp]
  exact (p.linkedWord_equivariant s l j).affinePoint_conjugation A t c

/-- The lifted ordered chart recovers the original full root product, with the
actual spectrum/global-section comparison on parameters. -/
theorem linkedWordUnipotentPoint_comp
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j)
    (A : CommAlgCat.{u} k) (t : Fin (maps).length → A) :
    orderedPoint (p.linkedWordUnipotentMap s hspan l hall) A t ≫ (iU).hom.hom =
      LocalSplitCell.orderedProduct id (maps).get ((algSpec (CommRingCat.of k)).obj (op A))
        (fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (t j)) := by
  have h := RelativeRoot.orderedPoints_map
    (p.linkedWordUnipotentMap s hspan l hall) (maps).get iU (fun _ => 𝟙 _)
    (fun j => (p.linkedWordUnipotentMap_comp s hspan l hall j).trans
      (Category.id_comp _).symm)
    (fun j => VectorGroup.affinePoint (R := CommRingCat.of k) A
      (fun _ : Fin 1 => t j))
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  apply h.trans
  unfold RelativeRoot.orderedPoints LocalSplitCell.orderedProduct LocalSplitCell.rootPoint
  simp only [id_eq, VectorGroup.affinePoint_eq_scalarPoint]

/-- Full opposite-root factorization gives a bijective chart on the actual
unipotent representative over every commutative coefficient algebra. -/
theorem linkedWordUnipotentPoint_bijective
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup)
    (A : CommAlgCat.{u} k) :
    Function.Bijective (orderedPoint (p.linkedWordUnipotentMap s hspan l hall) A) := by
  let : Mono (iU).hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋).1
  have hchart := p.linkedWord_orderedProduct_points s hspan l hn hall
    ((algSpec (CommRingCat.of k)).obj (op A))
  constructor
  · intro t t' htt
    have h := congrArg (fun g => g ≫ (iU).hom.hom) htt
    rw [linkedWordUnipotentPoint_comp, linkedWordUnipotentPoint_comp] at h
    have he := hchart.1 h
    funext j
    have hj := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (a j)) he
    simpa using hj
  · intro g
    have hg : g ≫ (iU).hom.hom ∈ (Dynamic.unipotent λ₋).carrier
        ((algSpec (CommRingCat.of k)).obj (op A)) := by
      rw [← (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋).2]
      exact SubgroupFunctor.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := (hchart.2 _).mp hg
    refine ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (c j), ?_⟩
    apply (cancel_mono (iU).hom.hom).mp
    rw [linkedWordUnipotentPoint_comp]
    simpa using hc

/-- The full root chart has a bijective actual coordinate-algebra pullback. -/
theorem linkedWordUnipotentCoordinateMap_bijective
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup) :
    Function.Bijective (coordinateMap (p.linkedWordUnipotentMap s hspan l hall)) :=
  coordinateMap_bijective_of_orderedPoint _
    (p.linkedWordUnipotentPoint_bijective s hspan l hall hn)

variable {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- Restriction to the actual unipotent group preserves every original ordered
coefficient in the fixed factor order. -/
theorem linkedWordUnipotent_coefficientOperator
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (a : Fin (maps).length →₀ ℕ) :
    coefficientOperator (ρ.restrict iU) (p.linkedWordUnipotentMap s hspan l hall) a =
      orderedCoefficients ρ (maps).get a := by
  rw [coefficientOperator, orderedCoefficients_eq_prod]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [restrict_comp, linkedWordUnipotentMap_comp]

variable [Infinite k]

/-- The actual lifted word has the nonzero original highest-weight endpoint. -/
theorem linkedWordUnipotent_coefficientOperator_ne_zero
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (m : ℕ)
    (hρ : p.IsHighestWeight ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (a : Fin (maps).length →₀ ℕ) (ha : ∀ j, a j = m) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ
      (m • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hv0 : v ≠ 0) :
    coefficientOperator (ρ.restrict iU) (p.linkedWordUnipotentMap s hspan l hall) a v ≠ 0 := by
  rw [linkedWordUnipotent_coefficientOperator,
    p.orderedCoefficients_reflectionWord s p.linkedSimpleLoweringMap ρ m l a ha]
  exact p.linkedWordCoefficient_ne_zero s hspan ρ m hρ l hv hv0

variable (q : ℕ) [ExpChar k q] (r : ℕ)
    (hρ : p.IsHighestWeight ρ
      ((q ^ r - 1) • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ
      ((q ^ r - 1) • Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hv0 : v ≠ 0)

include s hρ hv hv0 in
/-- The full actual Frobenius distribution orbit map is injective at the
supplied highest vector, using the original fixed linked word chart. -/
theorem linkedWord_distributionOrbitMap_injective
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup) :
    Function.Injective
      (FrobeniusOriginUniversality.distributionOrbitMap q r (ρ.restrict iU) v) :=
  OrderedFrobeniusCyclicity.distributionOrbitMap_injective
    (p.linkedWordUnipotentMap s hspan l hall)
    (p.linkedWordUnipotentCoordinateMap_bijective s hspan l hall hn)
    (p.oppositeRhoUnipotentAction hspan) (p.linkedWordWeight s l)
    (p.linkedWordUnipotentMap_scaling s hspan l hall) q r (ρ.restrict iU)
    p.isSplitTorus (-ν₀) (p.linkedWordWeight_pairing_pos s hspan l hall) v
    (p.linkedWordUnipotent_coefficientOperator_ne_zero s hspan l ρ hall
      (q ^ r - 1) hρ (bound q (maps).length r) (fun _ => rfl) hv hv0)

include s hρ hv hv0 in
/-- The intrinsic Frobenius-origin orbit has the full word-chart dimension. -/
theorem linkedWord_finrank_originOrbitSpan
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup) :
    Module.finrank k (FrobeniusOrderedDistributions.originOrbitSpan q r (ρ.restrict iU) v) =
      (q ^ r) ^ l.length := by
  simpa only [length_reflectionWordLoweringMaps] using
    OrderedFrobeniusCyclicity.finrank_originOrbitSpan
      (p.linkedWordUnipotentMap s hspan l hall)
      (p.linkedWordUnipotentCoordinateMap_bijective s hspan l hall hn)
      (p.oppositeRhoUnipotentAction hspan) (p.linkedWordWeight s l)
      (p.linkedWordUnipotentMap_scaling s hspan l hall) q r (ρ.restrict iU)
      p.isSplitTorus (-ν₀) (p.linkedWordWeight_pairing_pos s hspan l hall) v
      (p.linkedWordUnipotent_coefficientOperator_ne_zero s hspan l ρ hall
        (q ^ r - 1) hρ (bound q (maps).length r) (fun _ => rfl) hv hv0)

omit [Infinite k] in
/-- A word listing each positive root once has the intrinsic positive-root count. -/
theorem linkedWord_length_eq_card_positive
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup) :
    l.length = Fintype.card {j : p.rootIndex // p.base.IsPos j} := by
  let f : Fin (roots).length → {j : p.rootIndex // p.base.IsPos j} :=
    fun j => ⟨(roots).get j, (hall _).mp (List.get_mem roots j)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact (List.Nodup.get_inj_iff hn).mp (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hall j.val).mpr j.property)
      exact ⟨i, Subtype.ext hi⟩
  simpa only [Fintype.card_fin, Langlands.PositiveRootWord.length_wordRoots] using
    Fintype.card_congr (Equiv.ofBijective f hf)

include hρ hv hv0 in
/-- The pinning itself supplies the word and representatives needed to detect
the full actual Frobenius quotient at a highest vector. -/
theorem highestWeight_distributionOrbitMap_injective :
    Function.Injective
      (FrobeniusOriginUniversality.distributionOrbitMap q r (ρ.restrict iU) v) := by
  let : p.rootDatum.IsReduced := p.isReduced
  obtain ⟨l', -, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  exact p.linkedWord_distributionOrbitMap_injective p.simpleReflectionRepresentative
    hspan l' ρ q r hρ hv hv0 hall hn

include hρ hv hv0 in
/-- The actual opposite-unipotent Frobenius orbit of a supplied highest vector
has dimension `q^(r*N)`, where `N` is the number of positive roots. -/
theorem highestWeight_finrank_originOrbitSpan :
    Module.finrank k (FrobeniusOrderedDistributions.originOrbitSpan q r (ρ.restrict iU) v) =
      (q ^ r) ^ Fintype.card {j : p.rootIndex // p.base.IsPos j} := by
  let : p.rootDatum.IsReduced := p.isReduced
  obtain ⟨l', -, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  have h := p.linkedWord_finrank_originOrbitSpan p.simpleReflectionRepresentative
    hspan l' ρ q r hρ hv hv0 hall hn
  rw [p.linkedWord_length_eq_card_positive l' hall hn] at h
  exact h

include hρ hv hv0 in
/-- A separately established upper bound on the entire supplied representation
turns the actual Frobenius-origin orbit into that entire representation. -/
theorem highestWeight_originOrbitSpan_eq_top_of_finrank_le
    (hdim : Module.finrank k (n → k) ≤
      (q ^ r) ^ Fintype.card {j : p.rootIndex // p.base.IsPos j}) :
    FrobeniusOrderedDistributions.originOrbitSpan q r (ρ.restrict iU) v = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [p.highestWeight_finrank_originOrbitSpan hspan ρ q r hρ hv hv0]
  exact hdim

end Langlands.GroupScheme.SplitPinning
