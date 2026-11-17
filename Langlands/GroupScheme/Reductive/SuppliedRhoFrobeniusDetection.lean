import Langlands.GroupScheme.Reductive.SuppliedRhoRootCutoff
import Langlands.GroupScheme.Reductive.SuppliedHighestWeightFrobeniusOrbit
import Langlands.GroupScheme.Reductive.CanonicalRhoFrobeniusDetection
import Langlands.GroupScheme.Reductive.UnipotentCoordinateInvariance
import Langlands.GroupScheme.HomogeneousCharacterProducts

/-! # Whole-space Frobenius detection from supplied simple-root coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.SplitPinning

open AffineCoordinates FrobeniusRootCurveCutoff FrobeniusCovariantInvariants

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (c : p.SimpleRootCoordinateFamily) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "D" => Dynamic.Affine.unipotentScheme λ₋
local notation "iD" => Dynamic.Affine.unipotentHom λ₋
local notation "U" => Standard.unipotentScheme p.inclusion (-ν₀) ∅
local notation "iU" => Standard.unipotentHom p.inclusion (-ν₀) ∅
local notation "iP" => Dynamic.Affine.parabolicHom λ₀
local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

local instance suppliedRhoDetectionIsAffine
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance suppliedRhoDetectionUnipotentIsAffineHom : IsAffineHom (D).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

local instance suppliedRhoDetectionParabolicIsAffineHom :
    IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

include c

variable [IsAlgClosed k]

/-- Right invariance under the actual height-r origin subgroup forces a
Steinberg covariant to have its identity value on the whole opposite group. -/
theorem suppliedRho_eq_identityValue_of_originInvariant
    (q : ℕ) [ExpChar k q] (r : ℕ)
    {f : algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan (q ^ r - 1))
    (hfrob : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X)
      (h : V ⟶ (U).X), IsOriginTestPoint U q r V h →
        pointAlgebraHom G V (g * (h ≫ (iU).hom.hom)) f =
          pointAlgebraHom G V g f)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ (U).X) :
    pointAlgebraHom G V (x ≫ (iU).hom.hom) f =
      pointAlgebraHom G V 1 f := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := p.isConnectedReductive.connectedSpace
  let : Smooth (D).X.hom := (dynamicSmooth k G λ₋ D iD).2.2
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
  let hU := Standard.isRepresentedBy_unipotentHom_empty p.inclusion (-ν₀) p.isSplitTorus
  let hD := Dynamic.Affine.isRepresentedBy_unipotentHom λ₋
  let e := hU.isoOfIsRepresentedBy hD
  have he : e.hom ≫ iD = iU := hU.isoOfIsRepresentedBy_hom_comp hD
  have hei : e.inv ≫ iU = iD := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let b := p.canonicalRhoUnipotentRestriction hspan f
  have hb : ∀ (W : Over (Spec (CommRingCat.of k))) (g h : W ⟶ (D).X),
      IsOriginTestPoint D q r W h →
        pointAlgebraHom D W (g * h) b = pointAlgebraHom D W g b := by
    intro W g h hh
    have hhU := isOriginTestPoint_map q r e.inv W h hh
    have hhf := hfrob W (g ≫ (iD).hom.hom) (h ≫ e.inv.hom.hom) hhU
    dsimp only [b]
    rw [p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan W (g * h) f,
      p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan W g f]
    simpa only [MonObj.mul_comp, Category.assoc,
      ← Grp.comp_hom_hom e.inv iU, hei] using hhf
  have hgen : ∀ a ∈ simpleRelativeRoots p.inclusion (-ν₀),
      ∀ (y g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (D).X),
        y ≫ (iD).hom.hom ∈ (RelativeRoot.subgroup p.inclusion a).carrier _ →
          pointAlgebraHom D _ (y * g) b = pointAlgebraHom D _ g b := by
    intro a ha y g hy
    obtain ⟨s, rfl⟩ := p.exists_simple_of_mem_simpleRelativeRoots_oppositeRho hspan ha
    rw [← (c s).negative_represents.2] at hy
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
    have hyz : z ≫ (p.suppliedNegativeSimpleUnipotentMap c hspan s).hom.hom = y := by
      have : Mono (iD).hom.hom := hD.1
      apply (cancel_mono (iD).hom.hom).mp
      rw [Category.assoc, ← Grp.comp_hom_hom,
        suppliedNegativeSimpleUnipotentMap_comp]
      exact hz
    rw [← hyz]
    exact p.suppliedRhoUnipotentRestriction_steinberg_leftInvariant
      c hspan q r hf hb s _ z g
  have hgeneric : IsGenericCocharacter p.inclusion (-ν₀) := by
    intro a ha
    simpa only [map_neg, neg_ne_zero] using
      p.isRootDatum.polarization_rho_isGeneric p.base hspan a ha
  have hc := UnipotentCoordinateInvariance.eq_identityValue_of_simpleRoots
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus p.isRootDatum hgeneric
    iD hD (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋) b hgen
    V (x ≫ e.hom.hom.hom)
  dsimp only [b] at hc
  rw [p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan V (x ≫ e.hom.hom.hom) f,
    p.pointAlgebraHom_canonicalRhoUnipotentRestriction hspan V 1 f] at hc
  simpa only [Category.assoc, ← Grp.comp_hom_hom e.hom iD, he, MonObj.one_comp] using hc

/-- The same-height Frobenius restriction is injective on the entire
canonical covariant space, with no dimension or irreducibility premise. -/
theorem suppliedRhoFrobeniusRestriction_injective
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Function.Injective (p.canonicalRhoFrobeniusRestriction hspan q r) := by
  classical
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  by_contra hnot
  obtain ⟨f, hne, hz, hfrob⟩ :=
    exists_originInvariant_of_not_injective p.inclusion ν₀ (χ₀ ^ (q ^ r - 1))
      q r p.isSplitTorus hnot
  have hq : FrobeniusCovariantKernel.restrictionCoalgebra iU q r
      (f : algebra G) = 0 := by
    rw [FrobeniusCovariantKernel.restrictionCoalgebra_eq_oppositeUnipotentFrobeniusRestriction]
    exact hz
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  have hε : AffineLinearEmbedding.counit (corepresentation G) (f : algebra G) = 0 := by
    have hc := LinearMap.congr_fun
      (FrobeniusCovariantKernel.restrictionCoalgebra iU q r).counit_comp
      (f : algebra G)
    change Coalgebra.counit (R := k)
      (FrobeniusCovariantKernel.restrictionCoalgebra iU q r (f : algebra G)) =
        AffineLinearEmbedding.counit (corepresentation G) (f : algebra G) at hc
    rw [hq, map_zero] at hc
    exact hc.symm
  have hrest : covariantCellRestriction iP iU (χ₀ ^ (q ^ r - 1)) f = 0 := by
    apply (globalAlgHom_bijective U).1
    rw [map_zero, ← pointAlgebraHom_id_apply]
    have hc := p.suppliedRho_eq_identityValue_of_originInvariant c hspan q r
      f.property hfrob (U).X (𝟙 (U).X)
    rw [pointAlgebraHom_one, AlgHom.comp_apply, hε, map_zero] at hc
    rw [AffineHomImageHopfAdapter.pointAlgebraHom_pullback iU (U).X (𝟙 (U).X),
      AlgHom.comp_apply] at hc
    exact hc
  apply hne
  apply Dynamic.oppositeUnipotentRestriction_injective p.inclusion ν₀
    p.isConnectedReductive p.isSplitTorus (χ₀ ^ (q ^ r - 1))
  change lieCoordinateAlgEquiv U
    (covariantCellRestriction iP iU (χ₀ ^ (q ^ r - 1)) f) = _
  rw [hrest, map_zero, map_zero]

open MatrixRepresentation OrderedAdditiveCoordinates OrderedAdditiveProducts

variable (s : p.SimpleReflectionRepresentatives) (l : List p.base.support)

local notation "maps" => p.reflectionWordLoweringMaps s (p.suppliedSimpleLoweringMap c) l
local notation "roots" => Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l

/-- The full supplied word factors lifted into the standard representative of
the same opposite unipotent functor. -/
def suppliedStandardWordMap
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (j : Fin (maps).length) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ U := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  exact SubgroupFunctor.IsRepresentedBy.liftOfLE (F := Dynamic.unipotent λ₋) (i := iU)
    (Standard.isRepresentedBy_unipotentHom_empty p.inclusion (-ν₀) p.isSplitTorus)
    ((maps).get j) (p.suppliedWord_range_le_unipotent c s hspan l hall j)

omit [IsAlgClosed k] in
theorem suppliedStandardWordMap_comp
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (j : Fin (maps).length) :
    p.suppliedStandardWordMap c hspan s l hall j ≫ iU = (maps).get j := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  exact SubgroupFunctor.IsRepresentedBy.liftOfLE_comp (F := Dynamic.unipotent λ₋) (i := iU)
    (Standard.isRepresentedBy_unipotentHom_empty p.inclusion (-ν₀) p.isSplitTorus)
    ((maps).get j) (p.suppliedWord_range_le_unipotent c s hspan l hall j)

omit [IsAlgClosed k] in
/-- The standard representative's word chart has the original full-root product. -/
theorem suppliedStandardWordPoint_comp
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j)
    (A : CommAlgCat.{u} k) (t : Fin (maps).length → A) :
    orderedPoint (p.suppliedStandardWordMap c hspan s l hall) A t ≫ (iU).hom.hom =
      LocalSplitCell.orderedProduct id (maps).get ((algSpec (CommRingCat.of k)).obj (op A))
        (fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (t j)) := by
  have h := RelativeRoot.orderedPoints_map
    (p.suppliedStandardWordMap c hspan s l hall) (maps).get iU (fun _ => 𝟙 _)
    (fun j => (p.suppliedStandardWordMap_comp c hspan s l hall j).trans
      (Category.id_comp _).symm)
    (fun j => VectorGroup.affinePoint (R := CommRingCat.of k) A
      (fun _ : Fin 1 => t j))
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  apply h.trans
  unfold RelativeRoot.orderedPoints LocalSplitCell.orderedProduct LocalSplitCell.rootPoint
  simp only [id_eq, VectorGroup.affinePoint_eq_scalarPoint]

omit [IsAlgClosed k] in
/-- The standard word chart is bijective over every coefficient algebra. -/
theorem suppliedStandardWordPoint_bijective
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup)
    (A : CommAlgCat.{u} k) :
    Function.Bijective (orderedPoint (p.suppliedStandardWordMap c hspan s l hall) A) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  have hU := Standard.isRepresentedBy_unipotentHom_empty p.inclusion (-ν₀) p.isSplitTorus
  let : Mono (iU).hom.hom := hU.1
  have hchart := p.suppliedWord_orderedProduct_points c s hspan l hn hall
    ((algSpec (CommRingCat.of k)).obj (op A))
  constructor
  · intro t t' htt
    have h := congrArg (fun g => g ≫ (iU).hom.hom) htt
    rw [suppliedStandardWordPoint_comp, suppliedStandardWordPoint_comp] at h
    have he := hchart.1 h
    funext j
    have hj := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (a j)) he
    simpa using hj
  · intro g
    have hg : g ≫ (iU).hom.hom ∈ (Dynamic.unipotent λ₋).carrier
        ((algSpec (CommRingCat.of k)).obj (op A)) := by
      rw [← hU.2]
      exact SubgroupFunctor.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨w, hw⟩ := (hchart.2 _).mp hg
    refine ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (w j), ?_⟩
    apply (cancel_mono (iU).hom.hom).mp
    rw [suppliedStandardWordPoint_comp]
    simpa using hw

omit [IsAlgClosed k] in
/-- The actual standard coordinate pullback is bijective. -/
theorem suppliedStandardWordCoordinateMap_bijective
    (hall : ∀ j, j ∈ roots ↔ p.base.IsPos j) (hn : (roots).Nodup) :
    Function.Bijective (coordinateMap (p.suppliedStandardWordMap c hspan s l hall)) :=
  OrderedFrobeniusCyclicity.coordinateMap_bijective_of_orderedPoint _
    (p.suppliedStandardWordPoint_bijective c hspan s l hall hn)

/-- Detection in the supplied polynomial chart makes the whole covariant space finite. -/
theorem finite_suppliedRhoCovariantSubspace (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.Finite k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) := by
  let : p.rootDatum.IsReduced := p.isReduced
  obtain ⟨l', -, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  let x := p.suppliedStandardWordMap c hspan p.simpleReflectionRepresentative l' hall
  have hx := p.suppliedStandardWordCoordinateMap_bijective c hspan
    p.simpleReflectionRepresentative l' hall hn
  let := FrobeniusCoordinateModel.finite_quotientAlgebra U q r
    (coordinateEquiv x hx) (coordinateMap_origin x)
  exact Module.Finite.of_injective (p.canonicalRhoFrobeniusRestriction hspan q r)
    (p.suppliedRhoFrobeniusRestriction_injective c hspan q r)

/-- The full word chart gives the root-count upper bound on the whole induced space,
without computing Lie root dimensions. -/
theorem finrank_suppliedRhoCovariantSubspace_le_rootCount
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) ≤
      (q ^ r) ^ Nat.card {j : p.rootIndex // p.base.IsPos j} := by
  let : p.rootDatum.IsReduced := p.isReduced
  obtain ⟨l', -, hn, hall, -⟩ :=
    Langlands.PositiveRootWord.exists_positive_word p.rootDatum p.base
  let x := p.suppliedStandardWordMap c hspan p.simpleReflectionRepresentative l' hall
  have hx := p.suppliedStandardWordCoordinateMap_bijective c hspan
    p.simpleReflectionRepresentative l' hall hn
  let := FrobeniusCoordinateModel.finite_quotientAlgebra U q r
    (coordinateEquiv x hx) (coordinateMap_origin x)
  have h := LinearMap.finrank_le_finrank_of_injective
    (p.suppliedRhoFrobeniusRestriction_injective c hspan q r)
  rw [FrobeniusCoordinateModel.finrank_quotientAlgebra U q r
    (coordinateEquiv x hx) (coordinateMap_origin x)] at h
  simpa only [length_reflectionWordLoweringMaps,
    p.linkedWord_length_eq_card_positive l' hall hn, Nat.card_eq_fintype_card] using h

end Langlands.GroupScheme.SplitPinning
