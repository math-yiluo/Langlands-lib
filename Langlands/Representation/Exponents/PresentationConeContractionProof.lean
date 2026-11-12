import Langlands.Representation.Exponents.PresentationConeContractionStatement
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.CocharacterWeightCriterion
import Langlands.GroupScheme.Dynamic.UnipotentGradedCoordinates
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # Uniform contraction of compact subsets of `N(F)` by `C_A^+(ε)`: proof -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.ConeContraction

open Langlands.GroupScheme
open Langlands.GroupScheme.Dynamic.GradedCoordinates
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]

section Points

/-- A rational point, read as a point over the affine test scheme `Spec k`. -/
abbrev affPt {X : Over (Spec (CommRingCat.of k))}
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶ X :=
  toBase (CommAlgCat.of (CommRingCat.of k) k) ≫ x

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [IsAffine G.X.left]

/-- The chart coordinates of a rational point are the Lie coordinates of its affine point. -/
theorem pointCoordinates_affPt_chartCoordinates
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (b : Γ(G.X.left, ⊤)) :
    Lie.pointCoordinates G (affPt x) (DynamicLie.chartCoordinates G b) =
      Dynamic.AffineChart.pointRing x b := by
  have h := congrArg (fun φ => φ b) (DynamicLie.pointRing_eq_pointCoordinates (affPt x))
  simp only [CommRingCat.comp_apply] at h
  refine Eq.trans (b := Dynamic.AffineChart.pointRing (affPt x) b) h.symm ?_
  rw [affPt, Dynamic.AffineChart.pointRing_comp]
  change (Dynamic.AffineChart.pointRing x ≫ Spec.preimage
    (Spec.map (CommRingCat.ofHom (algebraMap k k)))) b = _
  rw [Spec.preimage_map]
  rfl

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem affPt_mul (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    affPt (x * y) = affPt x * affPt y :=
  MonObj.comp_mul _ _ _

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem affPt_inv (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    affPt x⁻¹ = (affPt x)⁻¹ :=
  GrpObj.comp_inv _ _

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem affPt_one : affPt (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = 1 :=
  MonObj.comp_one _

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
/-- Conjugation by a rational torus point, read on affine points, is the conjugation action. -/
theorem affPt_conj {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    affPt (rationalPoints.map i s * x * (rationalPoints.map i s)⁻¹) =
      (AutomorphicAction.conjugation i).act (affPt s) (affPt x) := by
  rw [AutomorphicAction.conjugation_act, affPt_mul, affPt_mul, affPt_inv]
  rfl

end Points

section Characters

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The Lie character value at an affine rational point is the rational character value. -/
theorem characterValue_affPt (w : characterLattice T)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X) :
    (Lie.characterValue w (affPt t) : k) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm w) t : k) := by
  change _ = (Gm.affinePointsEquiv (𝟙 _) (t ≫ (CommGroupScheme.groupHom w).hom.hom) : k)
  unfold Lie.characterValue
  rw [Gm.affinePointsEquiv_val, Gm.affinePointsEquiv_val, affPt, Category.assoc,
    Gm.pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom (algebraMap k k))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom) _ = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The same value after pushing a rational point forward along a torus homomorphism. -/
theorem characterValue_affPt_comp {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : A ⟶ T) (w : characterLattice T)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.toGrp.X) :
    (Lie.characterValue w (affPt (rationalPoints.map (CommGroupScheme.groupHom f) t)) : k) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm (f ≫ w)) t :
        k) := by
  rw [← characterValue_affPt, Lie.characterValue_comp]
  rfl

end Characters

section Structure

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

/-- The chosen split-component cocharacter, pushed into the presentation torus. -/
theorem groupHom_splitComponentCocharacter_comp :
    CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p =
      CommGroupScheme.groupHom
        (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) ≫ r.data.i := by
  change _ = (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
    CommGroupScheme.groupHom r.data.f) ≫ r.data.i
  rw [Category.assoc, r.isCompatible.factor_comp]

/-- A supplied geometric radical is the dynamic identity-limit subgroup of every standard
cocharacter of the presentation torus. -/
theorem range_radical_eq_unipotent (hG : IsConnectedReductive G)
    {U : GroupScheme (Spec (CommRingCat.of k))} {n : U ⟶ P}
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) {ζ : cocharacterLattice r.data.T}
    (hζ : IsStandardCocharacter r.data.i r.data.ν r.data.J ζ) :
    SubgroupFunctor.range (n ≫ p) =
      Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ r.data.i) := by
  have : Smooth G.X.hom := hG.smooth
  rw [r.range_comp_radical_eq hn, groupHom_splitComponentCocharacter_comp]
  have hstd := standardCocharacter k G hG r.data.T r.data.i r.isCompatible.maximalSplit
    r.data.ν r.isCompatible.generic r.data.J r.isCompatible.subset_simpleRoots
  exact (hstd.2 _ r.isStandard_splitComponentCocharacter).2.2.symm.trans (hstd.2 ζ hζ).2.2

/-- The cone of cocharacters of `A` pairing at least `K` with every restricted simple root
outside `J`. -/
def cone (K : ℤ) : Set (cocharacterLattice A) :=
  {c | ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν \ r.data.J,
    K ≤ latticePairing A (r.data.f ≫ β) c}

theorem cone_antitone {K K' : ℤ} (h : K ≤ K') : cone r K' ⊆ cone r K :=
  fun _ hc β hβ => h.trans (hc β hβ)

variable [LocallyOfFiniteType G.X.hom]

/-- A uniform bound for the pairings of the chosen standard cocharacter with the simple
roots outside `J`. -/
theorem exists_pairing_bound :
    ∃ D : ℤ, 1 ≤ D ∧ ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν \ r.data.J,
      latticePairing r.data.T β
        (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) ≤ D := by
  obtain ⟨D, hD⟩ := ((r.finite_simpleRoots.sdiff (t := r.data.J)).image
    (fun β => latticePairing r.data.T β
      (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter))).bddAbove
  exact ⟨max D 1, le_max_right _ _, fun β hβ => (hD ⟨β, hβ, rfl⟩).trans (le_max_left _ _)⟩

/-- Subtracting a bounded multiple of the chosen standard cocharacter from a point deep in
the cone leaves a standard cocharacter. -/
theorem isStandard_sub_smul {D : ℤ}
    (hD : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν \ r.data.J,
      latticePairing r.data.T β
        (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) ≤ D)
    {K m : ℤ} (hm : 0 ≤ m) (hK : m * D + 1 ≤ K) {c : cocharacterLattice A}
    (hc : c ∈ cone r K) :
    IsStandardCocharacter r.data.i r.data.ν r.data.J
      (RealTorusSpace.cocharacterMapInt r.data.f (c - m • r.splitComponentCocharacter)) := by
  have hμ := r.isStandard_splitComponentCocharacter
  refine ⟨r.isCompatible.subset_simpleRoots, fun α hα => ?_, fun α hα hαJ => ?_⟩
  · rw [map_sub, map_zsmul, map_sub, map_zsmul, hμ.2.1 α hα,
      ← RelativeRoot.latticePairing_restrict_cocharacterMapInt,
      r.selectedRoot_restrict_eq_zero hα]
    simp
  · have h1 := hc α ⟨hα, hαJ⟩
    have h2 := hD α ⟨hα, hαJ⟩
    rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt] at h1
    rw [map_sub, map_zsmul, map_sub, map_zsmul, smul_eq_mul]
    nlinarith

end Structure

section FieldTopology

variable (k) [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The powers of the chosen uniformizer converge to zero. -/
theorem tendsto_uniformizer_pow :
    Tendsto (fun n : ℕ => LocalField.uniformizer k ^ n) atTop (𝓝 0) := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  apply Valued.tendsto_zero_pow_of_v_lt_one
  change ValuativeRel.valuation k (LocalField.uniformizer k) < 1
  rw [← (ValuativeRel.valuation k).vlt_one_iff, ← FML.ord_lt_ord_iff k 1, FML.ord_one,
    LocalField.ord_uniformizer]
  exact WithTop.coe_lt_coe.mpr zero_lt_one

variable {k}

/-- High uniformizer powers move a compact set of field values into any neighbourhood
of zero. -/
theorem exists_uniformizer_pow_mul_mem {K : Set k} (hK : IsCompact K) {U : Set k}
    (hU : U ∈ 𝓝 (0 : k)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ K, LocalField.uniformizer k ^ n * y ∈ U := by
  have h : ∀ᶠ v in 𝓝 (0 : k), ∀ y ∈ K, v * y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Tendsto (fun z : k × k => z.1 * z.2) (𝓝 ((0 : k), y)) (𝓝 0) := by
      simpa using (continuous_mul.tendsto ((0 : k), y))
    exact hc hU
  exact eventually_atTop.mp ((tendsto_uniformizer_pow k).eventually h)

end FieldTopology

section PointTopology

variable [TopologicalSpace k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X

/-- The canonical topology on rational points is induced by evaluation of global sections. -/
theorem isInducing_pointRing :
    IsInducing (fun x : RationalPoint k G.X => fun b : Γ(G.X.left, ⊤) =>
      Dynamic.AffineChart.pointRing x b) := by
  let e := (rationalPointHomeomorph k G.X).trans (affineSchemePointHomeomorph k G.X k)
  have h : (fun x : RationalPoint k G.X => fun b : Γ(G.X.left, ⊤) =>
      Dynamic.AffineChart.pointRing x b) = AlgPoint.evaluation ∘ e :=
    funext fun x => funext fun b => BruhatTits.DynamicUnipotentContainment.pointRing_apply x b
  rw [h]
  exact AlgPoint.isEmbedding_evaluation.isInducing.comp e.isInducing

variable [IsAffineHom G.X.hom]

/-- Every Lie coordinate of the affine point of a rational point is continuous. -/
theorem continuous_pointCoordinates_affPt (g : CharacterUnits.Coord G) :
    Continuous fun x : RationalPoint k G.X => Lie.pointCoordinates G (affPt x) g := by
  obtain ⟨b, rfl⟩ := DynamicLie.chartCoordinates_surjective G g
  have h : (fun x : RationalPoint k G.X =>
      Lie.pointCoordinates G (affPt x) (DynamicLie.chartCoordinates G b)) =
        fun x => Dynamic.AffineChart.pointRing x b :=
    funext fun x => pointCoordinates_affPt_chartCoordinates G x b
  rw [h]
  exact BruhatTits.DynamicUnipotentContainment.continuous_pointRing_apply b

end PointTopology

section Contraction

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

local instance : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X

/-- The filter of cocharacters eventually deep inside every cone. -/
def coneFilter : Filter (cocharacterLattice A) := ⨅ K : ℤ, 𝓟 (cone r K)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsAffine G.X.left] in
theorem mem_coneFilter_of_subset {K : ℤ} {s : Set (cocharacterLattice A)}
    (h : cone r K ⊆ s) : s ∈ coneFilter r :=
  mem_iInf_of_mem K (mem_principal.2 h)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsAffine G.X.left] in
theorem exists_cone_subset_of_mem {s : Set (cocharacterLattice A)} (hs : s ∈ coneFilter r) :
    ∃ K : ℤ, cone r K ⊆ s := by
  have hdir : Directed (· ≥ ·) (fun K : ℤ => 𝓟 (cone r K)) := fun K₁ K₂ =>
    ⟨max K₁ K₂, principal_mono.2 (cone_antitone r (le_max_left _ _)),
      principal_mono.2 (cone_antitone r (le_max_right _ _))⟩
  obtain ⟨K, hK⟩ := (mem_iInf_of_directed hdir s).1 hs
  exact ⟨K, mem_principal.1 hK⟩

/-- The rational point of the presentation torus given by a cocharacter of `A` evaluated at
the uniformizer. -/
abbrev torusPoint (c : cocharacterLattice A) : rationalPoints r.data.T.toGrp :=
  rationalPoints.map (CommGroupScheme.groupHom r.data.f)
    (CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd c))

omit [IsAffine G.X.left] in
theorem characterValue_torusPoint (w : characterLattice r.data.T) (c : cocharacterLattice A) :
    (Lie.characterValue w (affPt (torusPoint r c)) : k) =
      LocalField.uniformizer k ^ latticePairing A (r.data.f ≫ w) c := by
  rw [characterValue_affPt_comp]
  change ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm
    (r.data.f ≫ w)) (CocharacterUniformizer.cocharacterPoints k A c
      (SplitTorusValuation.uniformizerUnit k)) : kˣ) : k) = _
  rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    Units.val_zpow_eq_zpow_val, SplitTorusValuation.uniformizerUnit_val]

/-- A Lie coordinate of the conjugate of a rational point by a torus point. -/
def conjCoord (g : CharacterUnits.Coord G) (z : cocharacterLattice A × RationalPoint k G.X) :
    k :=
  Lie.pointCoordinates G
    ((AutomorphicAction.conjugation r.data.i).act (affPt (torusPoint r z.1)) (affPt z.2)) g

/-- The conjugate of a rational point by a torus point. -/
abbrev conjPoint (z : cocharacterLattice A × RationalPoint k G.X) : RationalPoint k G.X :=
  rationalPoints.map r.data.i (torusPoint r z.1) * z.2 *
    (rationalPoints.map r.data.i (torusPoint r z.1))⁻¹

variable (hG : IsConnectedReductive G) {n : U ⟶ P}
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
include hG hn in
/-- A torus eigenfunction that does not vanish at a rational point of the radical has a weight
pairing positively with every standard cocharacter. -/
theorem one_le_pairing_of_ne_zero {x : RationalPoint k G.X} (hx : x ∈ pointImage (n ≫ p))
    {w : characterLattice r.data.T} {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w)
    (h0 : Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G) ≠ 0)
    {ζ : cocharacterLattice r.data.T} (hζ : IsStandardCocharacter r.data.i r.data.ν r.data.J ζ) :
    1 ≤ latticePairing r.data.T w ζ := by
  by_contra hlt
  apply h0
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hmem : affPt x ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ r.data.i)).carrier _ := by
    rw [← range_radical_eq_unipotent r hG hn hζ]
    obtain ⟨y, rfl⟩ := hx
    exact (SubgroupFunctor.range (n ≫ p)).comp_mem _ ⟨y, rfl⟩
  exact (Dynamic.CocharacterWeights.mem_unipotent_iff_weights r.data.i ζ hT (affPt x)).1
    hmem w (by omega) g hg

variable [LocallyOfFiniteType G.X.hom]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsAffine G.X.left] in
/-- Deep in the cone, a weight positive on all standard cocharacters pairs with the
cocharacter at least one more than the depth parameter. -/
theorem add_one_le_pairing {D : ℤ}
    (hD : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν \ r.data.J,
      latticePairing r.data.T β
        (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) ≤ D)
    {K m : ℤ} (hm : 0 ≤ m) (hK : m * D + 1 ≤ K) {c : cocharacterLattice A} (hc : c ∈ cone r K)
    {w : characterLattice r.data.T}
    (hw : ∀ ζ, IsStandardCocharacter r.data.i r.data.ν r.data.J ζ →
      1 ≤ latticePairing r.data.T w ζ) :
    m + 1 ≤ latticePairing A (r.data.f ≫ w) c := by
  have h1 := hw _ (isStandard_sub_smul r hD hm hK hc)
  have h2 := hw _ r.isStandard_splitComponentCocharacter
  rw [map_sub, map_zsmul, map_sub, map_zsmul, smul_eq_mul] at h1
  rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  nlinarith

include hG hn in
/-- The contraction estimate for one torus eigenfunction in the augmentation ideal. -/
theorem tendsto_conjCoord_of_mem {C : Set (RationalPoint k G.X)} (hC : IsCompact C)
    (hCN : C ⊆ pointImage (n ≫ p)) {w : characterLattice r.data.T}
    {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w) :
    Tendsto (conjCoord r (g : CharacterUnits.Coord G)) (coneFilter r ×ˢ 𝓟 C) (𝓝 0) := by
  intro V hV
  have hKc : IsCompact ((fun x : RationalPoint k G.X =>
      Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G)) '' C) :=
    hC.image (continuous_pointCoordinates_affPt _)
  obtain ⟨N, hN⟩ := exists_uniformizer_pow_mul_mem hKc hV
  obtain ⟨D, -, hD⟩ := exists_pairing_bound r
  rw [Filter.mem_map, mem_prod_principal]
  refine mem_coneFilter_of_subset r (K := (N : ℤ) * D + 1) fun c hc x hx => ?_
  change conjCoord r (g : CharacterUnits.Coord G) (c, x) ∈ V
  have he : CoordinateWeights.IsEigenfunction (AutomorphicAction.conjugation r.data.i) w
      (g : CharacterUnits.Coord G) := hg
  unfold conjCoord
  rw [he k (affPt (torusPoint r c)) (affPt x)]
  by_cases h0 : Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G) = 0
  · rw [h0, mul_zero]
    exact mem_of_mem_nhds hV
  · have hb := add_one_le_pairing r hD (Int.natCast_nonneg N) le_rfl hc
      (fun ζ hζ => one_le_pairing_of_ne_zero r hG hn (hCN hx) hg h0 hζ)
    rw [characterValue_torusPoint]
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ latticePairing A (r.data.f ≫ w) c by omega)
    rw [hj, zpow_natCast]
    exact hN j (by omega) _ ⟨x, hx, rfl⟩

include hG hn in
/-- The contraction estimate for every coordinate in the augmentation ideal. -/
theorem tendsto_conjCoord_augmentation {C : Set (RationalPoint k G.X)} (hC : IsCompact C)
    (hCN : C ⊆ pointImage (n ≫ p)) (g : CoordinateWeights.augmentation G) :
    Tendsto (conjCoord r (g : CharacterUnits.Coord G)) (coneFilter r ×ˢ 𝓟 C) (𝓝 0) := by
  classical
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have htop := (CoordinateWeights.coordinateWeightDecomposition k G inferInstance r.data.T hT
    (AutomorphicAction.conjugation r.data.i)).2.1.submodule_iSup_eq_top
  have hg : g ∈ ⨆ w, CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun g : CoordinateWeights.augmentation G =>
    Tendsto (conjCoord r (g : CharacterUnits.Coord G)) (coneFilter r ×ˢ 𝓟 C) (𝓝 0)) hg
    (fun w g hg => tendsto_conjCoord_of_mem r hG hn hC hCN hg) ?_ ?_
  · have h : conjCoord r ((0 : CoordinateWeights.augmentation G) : CharacterUnits.Coord G) =
        fun _ => 0 := funext fun z => by simp [conjCoord]
    rw [h]
    exact tendsto_const_nhds
  · intro x y hx hy
    have h : conjCoord r ((x + y : CoordinateWeights.augmentation G) : CharacterUnits.Coord G) =
        fun z => conjCoord r (x : CharacterUnits.Coord G) z +
          conjCoord r (y : CharacterUnits.Coord G) z := funext fun z => by simp [conjCoord]
    rw [h]
    simpa using hx.add hy

include hG hn in
/-- Conjugation by the cone contracts a compact subset of the radical to the identity. -/
theorem tendsto_conjPoint {C : Set (RationalPoint k G.X)} (hC : IsCompact C)
    (hCN : C ⊆ pointImage (n ≫ p)) :
    Tendsto (conjPoint r) (coneFilter r ×ˢ 𝓟 C) (𝓝 1) := by
  rw [isInducing_pointRing.tendsto_nhds_iff, tendsto_pi_nhds]
  intro b
  set g := DynamicLie.chartCoordinates G b
  set o := Lie.coordinateOrigin G g
  let g' : CoordinateWeights.augmentation G := ⟨g - algebraMap k _ o, by
    rw [CoordinateWeights.mem_augmentation, map_sub, AlgHom.commutes]
    simp [o]⟩
  have h1 : ∀ z, Dynamic.AffineChart.pointRing (conjPoint r z) b =
      o + conjCoord r (g' : CharacterUnits.Coord G) z := by
    intro z
    rw [← pointCoordinates_affPt_chartCoordinates, affPt_conj]
    change _ = o + Lie.pointCoordinates G _ (g - algebraMap k _ o)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    abel
  have h2 : Dynamic.AffineChart.pointRing (1 : RationalPoint k G.X) b = o := by
    rw [← pointCoordinates_affPt_chartCoordinates, affPt_one, Lie.pointCoordinates_one]
    rfl
  change Tendsto (fun z => Dynamic.AffineChart.pointRing (conjPoint r z) b) _
    (𝓝 (Dynamic.AffineChart.pointRing (1 : RationalPoint k G.X) b))
  simp_rw [h1, h2]
  simpa using tendsto_const_nhds.add (tendsto_conjCoord_augmentation r hG hn hC hCN g')

end Contraction

end Langlands.Aubert.General.RepresentedParabolic.ConeContraction

namespace Langlands.Aubert.General.RepresentedParabolic

open Langlands.GroupScheme ConeContraction

/-- Renard V.5.2 (iii), `N` half, in neighbourhood form for compatible represented
parabolics: conjugation by `C_A^+(ε)` moves a compact subset of `N(F)` into any prescribed
neighbourhood of the identity once `ε` is small. -/
theorem presentationConeContraction : PresentationConeContractionStatement.{u} := by
  intro k _ _ _ _ _ G hG _ _ P M N p m n _hp _hm hn _hmul A a pres Δ C hC hCN L hL
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have htend := tendsto_conjPoint pres hG hn (C := C) hC hCN
  obtain ⟨K, hK⟩ := exists_cone_subset_of_mem pres (mem_prod_principal.1 (htend hL))
  have hq : (1 : ℝ) < LocalField.residueCardinality k := by
    exact_mod_cast LocalField.residueCardinality_gt_one k
  refine ⟨(LocalField.residueCardinality k : ℝ) ^ (-K), zpow_pos (by linarith) _, ?_⟩
  rintro t ⟨⟨x, rfl⟩, ht⟩ c hc
  have hcone : Multiplicative.toAdd x ∈ cone pres K := by
    intro β hβ
    have h := ht (pres.data.f ≫ β) ⟨β, hβ, rfl⟩
    rw [← ofAdd_toAdd x, CocharacterUniformizer.characterNorm_latticeSection] at h
    have h' := (zpow_lt_zpow_iff_right₀ hq).1 h
    omega
  have hmem := hK hcone c hc
  have heq : rationalPoints.map (a ≫ m ≫ p) (CocharacterUniformizer.latticeSection k A x) =
      rationalPoints.map pres.data.i (torusPoint pres (Multiplicative.toAdd x)) := by
    rw [← pres.isCompatible.factor_comp]
    rfl
  rw [heq]
  exact hmem

end Langlands.Aubert.General.RepresentedParabolic
