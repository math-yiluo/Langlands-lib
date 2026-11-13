import Langlands.Representation.Exponents.SplitComponentOppositeContractionStatement
import Langlands.Representation.Exponents.PresentationConeContractionProof
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints

/-! # Uniform two-sided contraction by `A^+(ε)`: proof -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeContraction

open Langlands.GroupScheme
open Langlands.GroupScheme.Dynamic.GradedCoordinates
open Langlands.AlgebraicGeometry.PointTopology
open ConeContraction

variable {k : Type u} [Field k]

section Generic

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

local instance : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X

omit [IsAffine G.X.left] in
/-- Along any filter, if every coordinate of the augmentation ideal tends to zero after
conjugation, then so does every coordinate. -/
theorem tendsto_conjCoord_augmentation_of_weight
    {F : Filter (cocharacterLattice A × RationalPoint k G.X)}
    (h : ∀ (w : characterLattice r.data.T) (g : CoordinateWeights.augmentation G),
      g ∈ CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation r.data.i) w →
        Tendsto (conjCoord r (g : CharacterUnits.Coord G)) F (𝓝 0))
    (g : CoordinateWeights.augmentation G) :
    Tendsto (conjCoord r (g : CharacterUnits.Coord G)) F (𝓝 0) := by
  classical
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have htop := (CoordinateWeights.coordinateWeightDecomposition k G inferInstance r.data.T hT
    (AutomorphicAction.conjugation r.data.i)).2.1.submodule_iSup_eq_top
  have hg : g ∈ ⨆ w, CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun g : CoordinateWeights.augmentation G =>
    Tendsto (conjCoord r (g : CharacterUnits.Coord G)) F (𝓝 0)) hg
    (fun w g hg => h w g hg) ?_ ?_
  · have h0 : conjCoord r ((0 : CoordinateWeights.augmentation G) : CharacterUnits.Coord G) =
        fun _ => 0 := funext fun z => by simp [conjCoord]
    rw [h0]
    exact tendsto_const_nhds
  · intro x y hx hy
    have h0 : conjCoord r ((x + y : CoordinateWeights.augmentation G) : CharacterUnits.Coord G) =
        fun z => conjCoord r (x : CharacterUnits.Coord G) z +
          conjCoord r (y : CharacterUnits.Coord G) z := funext fun z => by simp [conjCoord]
    rw [h0]
    simpa using hx.add hy

/-- Along any filter, if every augmentation coordinate of the conjugates tends to zero, the
conjugates tend to the identity. -/
theorem tendsto_conjPoint_of_coord
    {F : Filter (cocharacterLattice A × RationalPoint k G.X)}
    (h : ∀ g : CoordinateWeights.augmentation G,
      Tendsto (conjCoord r (g : CharacterUnits.Coord G)) F (𝓝 0)) :
    Tendsto (conjPoint r) F (𝓝 1) := by
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
  simpa using tendsto_const_nhds.add (h g')

end Generic

section Opposite

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P Pbar Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  (hG : IsConnectedReductive G)
  {pbar : Pbar ⟶ G} (hpbar : IsParabolicSubgroup pbar)
  {mbar : M ⟶ Pbar} (hmbar : IsRationalLeviSubgroup mbar)
  {nbar : Nbar ⟶ Pbar} (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
  (hP : mbar ≫ pbar = l ≫ p)
  (hPP : pointImage p ⊓ pointImage pbar = pointImage (l ≫ p))

include hG hpbar hmbar hnbar hP hPP in
/-- The rational points of the opposite radical form the dynamic identity-limit subgroup of the
negative of every standard cocharacter of the presentation torus. -/
theorem pointImage_opposite_radical_eq_neg {ζ : cocharacterLattice r.data.T}
    (hζ : IsStandardCocharacter r.data.i r.data.ν r.data.J ζ) :
    pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ζ) ≫ r.data.i)).carrier
        (Over.mk (𝟙 _)) := by
  have : Smooth G.X.hom := hG.smooth
  have hstd := standardCocharacter k G hG r.data.T r.data.i r.isCompatible.maximalSplit
    r.data.ν r.isCompatible.generic r.data.J r.isCompatible.subset_simpleRoots
  have hPχ : SubgroupFunctor.range p =
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ r.data.i) :=
    r.isCompatible.parabolic_eq.trans (hstd.2 ζ hζ).1
  have hMχ : SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ r.data.i) :=
    r.isCompatible.levi_eq.trans (hstd.2 ζ hζ).2.1
  rw [pointImage_opposite_radical_eq_dynamic parabolicDynamic oppositeDynamicParabolicUniqueness
    hG _ l hPχ hMχ hpbar hmbar hnbar hP hPP, groupHom_neg_comp_eq_oppositeCocharacter]
  rfl

include hG hpbar hmbar hnbar hP hPP in
/-- A torus eigenfunction that does not vanish at a rational point of the opposite radical has
a weight pairing at most `-1` with every standard cocharacter. -/
theorem le_neg_one_pairing_of_ne_zero {x : RationalPoint k G.X}
    (hx : x ∈ pointImage (nbar ≫ pbar))
    {w : characterLattice r.data.T} {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w)
    (h0 : Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G) ≠ 0)
    {ζ : cocharacterLattice r.data.T} (hζ : IsStandardCocharacter r.data.i r.data.ν r.data.J ζ) :
    latticePairing r.data.T w ζ ≤ -1 := by
  by_contra hlt
  apply h0
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hx' := hx
  rw [pointImage_opposite_radical_eq_neg r hG hpbar hmbar hnbar hP hPP hζ] at hx'
  have hmem : affPt x ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ζ) ≫ r.data.i)).carrier _ :=
    (Dynamic.unipotent (CommGroupScheme.groupHom (-ζ) ≫ r.data.i)).comp_mem _ hx'
  refine (Dynamic.CocharacterWeights.mem_unipotent_iff_weights r.data.i (-ζ) hT (affPt x)).1
    hmem w ?_ g hg
  rw [map_neg]
  omega

variable [LocallyOfFiniteType G.X.hom]

/-- Deep in the cone, a weight at most `-1` on all standard cocharacters pairs with the
cocharacter at most minus one more than the depth parameter. -/
theorem add_one_le_neg_pairing {D : ℤ}
    (hD : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν \ r.data.J,
      latticePairing r.data.T β
        (RealTorusSpace.cocharacterMapInt r.data.f r.splitComponentCocharacter) ≤ D)
    {K m : ℤ} (hm : 0 ≤ m) (hK : m * D + 1 ≤ K) {c : cocharacterLattice A} (hc : c ∈ cone r K)
    {w : characterLattice r.data.T}
    (hw : ∀ ζ, IsStandardCocharacter r.data.i r.data.ν r.data.J ζ →
      latticePairing r.data.T w ζ ≤ -1) :
    m + 1 ≤ -latticePairing A (r.data.f ≫ w) c := by
  have h1 := hw _ (isStandard_sub_smul r hD hm hK hc)
  have h2 := hw _ r.isStandard_splitComponentCocharacter
  rw [map_sub, map_zsmul, map_sub, map_zsmul, smul_eq_mul] at h1
  rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  nlinarith

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X

include hG hpbar hmbar hnbar hP hPP in
/-- The contraction estimate for one torus eigenfunction on the opposite radical, conjugating
by the negatives of cocharacters deep in the cone. -/
theorem tendsto_conjCoord_neg_of_mem {C : Set (RationalPoint k G.X)} (hC : IsCompact C)
    (hCN : C ⊆ pointImage (nbar ≫ pbar)) {w : characterLattice r.data.T}
    {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation r.data.i) w) :
    Tendsto (fun z : cocharacterLattice A × RationalPoint k G.X =>
        conjCoord r (g : CharacterUnits.Coord G) (-z.1, z.2))
      (coneFilter r ×ˢ 𝓟 C) (𝓝 0) := by
  intro V hV
  have hKc : IsCompact ((fun x : RationalPoint k G.X =>
      Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G)) '' C) :=
    hC.image (continuous_pointCoordinates_affPt _)
  obtain ⟨N, hN⟩ := exists_uniformizer_pow_mul_mem hKc hV
  obtain ⟨D, -, hD⟩ := exists_pairing_bound r
  rw [Filter.mem_map, mem_prod_principal]
  refine mem_coneFilter_of_subset r (K := (N : ℤ) * D + 1) fun c hc x hx => ?_
  change conjCoord r (g : CharacterUnits.Coord G) (-c, x) ∈ V
  have he : CoordinateWeights.IsEigenfunction (AutomorphicAction.conjugation r.data.i) w
      (g : CharacterUnits.Coord G) := hg
  unfold conjCoord
  rw [he k (affPt (torusPoint r (-c))) (affPt x)]
  by_cases h0 : Lie.pointCoordinates G (affPt x) (g : CharacterUnits.Coord G) = 0
  · rw [h0, mul_zero]
    exact mem_of_mem_nhds hV
  · have hb := add_one_le_neg_pairing r hD (Int.natCast_nonneg N) le_rfl hc
      (fun ζ hζ => le_neg_one_pairing_of_ne_zero r hG hpbar hmbar hnbar hP hPP (hCN hx) hg h0 hζ)
    rw [characterValue_torusPoint, map_neg]
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ -latticePairing A (r.data.f ≫ w) c by omega)
    rw [hj, zpow_natCast]
    exact hN j (by omega) _ ⟨x, hx, rfl⟩

include hG hpbar hmbar hnbar hP hPP in
/-- Conjugation by the inverses of the cone contracts a compact subset of the opposite radical
to the identity. -/
theorem tendsto_conjPoint_neg {C : Set (RationalPoint k G.X)} (hC : IsCompact C)
    (hCN : C ⊆ pointImage (nbar ≫ pbar)) :
    Tendsto (fun z : cocharacterLattice A × RationalPoint k G.X => conjPoint r (-z.1, z.2))
      (coneFilter r ×ˢ 𝓟 C) (𝓝 1) := by
  refine tendsto_map'_iff.1 (tendsto_conjPoint_of_coord r fun g => ?_)
  refine tendsto_conjCoord_augmentation_of_weight r (fun w g hg => ?_) g
  exact tendsto_map'_iff.2
    (tendsto_conjCoord_neg_of_mem r hG hpbar hmbar hnbar hP hPP hC hCN hg)

end Opposite

end Langlands.Aubert.General.RepresentedParabolic.OppositeContraction

namespace Langlands.Aubert.General.RepresentedParabolic

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open ConeContraction OppositeContraction

/-- Renard V.5.2 (iii) on all of `A^+(ε)`, both halves, in neighbourhood form: conjugation by
`t ∈ A^+(ε)` moves a compact subset of `N(F)` into a prescribed neighbourhood of `1`, and
conjugation by `t⁻¹` does the same for a compact subset of `N̄(F)`, once `ε` is small. -/
theorem splitComponentOppositeContraction : SplitComponentOppositeContractionStatement.{u} := by
  intro k _ _ _ _ _ G hG _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar
    hnbar _hmulbar hP hPP A a pres Δ incG C hC hCN Cbar hCbar hCbarN L hL
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have hsplit : IsSplitTorus A.toGrp :=
    pres.isCompatible.splitComponent.isCentralSplitTorus.isSplitSubtorus.1
  have : IsAffineHom A.toGrp.X.hom := hsplit.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology k A.X
  let Ker := Plancherel.rationalCommonNormKernel A.toGrp
  have hKc : IsCompact (Ker : Set (rationalPoints A.toGrp)) :=
    Plancherel.SplitTorus.isCompact_commonNormKernel hsplit
  have hinc : Continuous incG := continuous_rationalPointMap k (a ≫ m ≫ p).hom.hom
  -- the conjugation hulls of `C` and `C̄` under the compact norm kernel
  let C' : Set (rationalPoints G) :=
    (fun z : rationalPoints A.toGrp × rationalPoints G => incG z.1 * z.2 * (incG z.1)⁻¹) ''
      ((Ker : Set (rationalPoints A.toGrp)) ×ˢ C)
  let Cbar' : Set (rationalPoints G) :=
    (fun z : rationalPoints A.toGrp × rationalPoints G => (incG z.1)⁻¹ * z.2 * incG z.1) ''
      ((Ker : Set (rationalPoints A.toGrp)) ×ˢ Cbar)
  have hC' : IsCompact C' :=
    (hKc.prod hC).image (((hinc.comp continuous_fst).mul continuous_snd).mul
      (hinc.comp continuous_fst).inv)
  have hCbar' : IsCompact Cbar' :=
    (hKc.prod hCbar).image (((hinc.comp continuous_fst).inv.mul continuous_snd).mul
      (hinc.comp continuous_fst))
  have hincP : ∀ u, incG u ∈ pointImage p := fun u =>
    ⟨rationalPoints.map (a ≫ m) u, by rw [← pointMap_comp_apply, Category.assoc]⟩
  have hincPbar : ∀ u, incG u ∈ pointImage pbar := fun u =>
    ⟨rationalPoints.map (a ≫ mbar) u, by
      rw [← pointMap_comp_apply, Category.assoc, hP]⟩
  have hC'N : C' ⊆ pointImage (n ≫ p) := by
    rintro _ ⟨⟨u, c⟩, ⟨-, hc⟩, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1
      (pointImage_le_normalizer_radical p n hn (hincP u)) c).1 (hCN hc)
  have hCbar'N : Cbar' ⊆ pointImage (nbar ≫ pbar) := by
    rintro _ ⟨⟨u, c⟩, ⟨-, hc⟩, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.1 (pointImage_le_normalizer_radical pbar nbar hnbar
      (inv_mem (hincPbar u))) c).1 (hCbarN hc)
    rw [inv_inv] at h
    exact h
  -- the two halves on the lattice part
  obtain ⟨ε₁, hε₁, h₁⟩ :=
    presentationConeContraction k G hG P M N p m n hp hm hn hmul A a pres C' hC' hC'N L hL
  have htend := tendsto_conjPoint_neg pres hG hpbar hmbar hnbar hP hPP hCbar' hCbar'N
  obtain ⟨K, hK⟩ := exists_cone_subset_of_mem pres (mem_prod_principal.1 (htend hL))
  have hq : (1 : ℝ) < LocalField.residueCardinality k := by
    exact_mod_cast LocalField.residueCardinality_gt_one k
  refine ⟨min ε₁ ((LocalField.residueCardinality k : ℝ) ^ (-K)),
    lt_min hε₁ (zpow_pos (by linarith) _), fun t ht => ?_⟩
  -- decompose `t = s * u` with `s ∈ C_A` and `u` in the compact norm kernel
  obtain ⟨x, hx, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection k A hsplit).2.2 t
  let s := CocharacterUniformizer.latticeSection k A x
  let u : rationalPoints A.toGrp := t * s⁻¹
  have hu : u ∈ Ker := hx
  have ht_eq : t = s * u := by
    change t = s * (t * s⁻¹)
    rw [mul_comm t, mul_inv_cancel_left]
  have hnorm : ∀ α, CocharacterUniformizer.characterNorm k A α t =
      CocharacterUniformizer.characterNorm k A α s := by
    intro α
    have h1 : (Plancherel.rationalNormCharacters A.toGrp
        ((rationalCharacters.equivCharacterLattice A).symm α)).toMul u = 1 :=
      (Plancherel.mem_rationalCommonNormKernel A.toGrp u).1 hu
        ((rationalCharacters.equivCharacterLattice A).symm α)
    simp only [CocharacterUniformizer.characterNorm]
    rw [ht_eq, map_mul, h1, mul_one]
  have hincmul : incG t = incG s * incG u := by rw [ht_eq, map_mul]
  have hincmul' : incG t = incG u * incG s := by rw [ht_eq, mul_comm s u, map_mul]
  constructor
  · intro c hc
    have hs : s ∈ CocharacterUniformizer.CAepsilon k A Δ ε₁ :=
      ⟨⟨x, rfl⟩, fun α hα => by
        rw [← hnorm]
        exact (ht α hα).trans_le (min_le_left _ _)⟩
    have hmem := h₁ s hs (incG u * c * (incG u)⁻¹) ⟨(u, c), ⟨hu, hc⟩, rfl⟩
    have heq : incG t * c * (incG t)⁻¹ = incG s * (incG u * c * (incG u)⁻¹) * (incG s)⁻¹ := by
      rw [hincmul]
      group
    rw [heq]
    exact hmem
  · intro c hc
    have hcone : Multiplicative.toAdd x ∈ cone pres K := by
      intro β hβ
      have h := ht (pres.data.f ≫ β) ⟨β, hβ, rfl⟩
      rw [hnorm] at h
      have h2 : CocharacterUniformizer.characterNorm k A (pres.data.f ≫ β)
          (CocharacterUniformizer.latticeSection k A
            (Multiplicative.ofAdd (Multiplicative.toAdd x))) < _ :=
        h.trans_le (min_le_right _ _)
      rw [CocharacterUniformizer.characterNorm_latticeSection] at h2
      have h' := (zpow_lt_zpow_iff_right₀ hq).1 h2
      omega
    have hy : (incG u)⁻¹ * c * incG u ∈ Cbar' := ⟨(u, c), ⟨hu, hc⟩, rfl⟩
    have hmem := hK hcone _ hy
    have hlat : rationalPoints.map pres.data.i (torusPoint pres (-Multiplicative.toAdd x)) =
        (incG s)⁻¹ := by
      have h1 : CocharacterUniformizer.latticeSection k A
          (Multiplicative.ofAdd (-Multiplicative.toAdd x)) = s⁻¹ := by
        rw [ofAdd_neg, ofAdd_toAdd, map_inv]
      rw [← map_inv]
      change rationalPoints.map pres.data.i (rationalPoints.map
        (CommGroupScheme.groupHom pres.data.f) (CocharacterUniformizer.latticeSection k A
          (Multiplicative.ofAdd (-Multiplicative.toAdd x)))) = rationalPoints.map (a ≫ m ≫ p) _
      rw [h1, ← pres.isCompatible.factor_comp]
      rfl
    have heq : (incG t)⁻¹ * c * incG t =
        rationalPoints.map pres.data.i (torusPoint pres (-Multiplicative.toAdd x)) *
          ((incG u)⁻¹ * c * incG u) *
          (rationalPoints.map pres.data.i (torusPoint pres (-Multiplicative.toAdd x)))⁻¹ := by
      rw [hlat, hincmul']
      group
    rw [heq]
    exact hmem

end Langlands.Aubert.General.RepresentedParabolic
