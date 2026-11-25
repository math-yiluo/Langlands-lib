import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalParabolicOrbitCoordinates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalChamberContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellLemma
import Langlands.Representation.Plancherel.RationalOpenCellConullProof

/-! # The actual one-sided open-cell height estimate -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix Topology
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field

/-- Extend the actual torus character order to ambient points using the
canonical choice of a torus preimage. Only values on the torus image are
used. For a monomorphic inclusion those values are independent of choice. -/
def rationalTorusCharacterOrder (i : T.toGrp ⟶ G) (alpha : characterLattice T)
    (g : rationalPoints G) : ℤ :=
  RenardLeviCones.characterOrder T alpha (Function.invFun (rationalPoints.map i) g)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- On the torus image, the extended order is the actual character order. -/
theorem rationalTorusCharacterOrder_map (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (alpha : characterLattice T) (a : rationalPoints T.toGrp) :
    rationalTorusCharacterOrder i alpha (rationalPoints.map i a) =
      RenardLeviCones.characterOrder T alpha a := by
  unfold rationalTorusCharacterOrder
  have hinj : Function.Injective (rationalPoints.map i) :=
    fun x y h => (cancel_mono i.hom.hom).mp h
  rw [Function.leftInverse_invFun hinj a]

/-- The actual compact-set coordinate estimate, step (2) of II.3.5. It
holds for every real height dominating the original closed matrix height. -/
theorem exists_mem_opposite_open_of_small_conj_on_compact
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho) (sigma : rationalPoints G → ℝ)
    (hsigma : ∀ g, rationalHeight (F := F) rho g ≤ sigma g)
    (K : Set (rationalPoints G)) (hK : IsCompact K)
    (Gamma : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints) :
    ∃ C > 0, ∀ a ∈ rationalMinimalChamber i nu,
      ∀ u ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints,
      ∀ p ∈ standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}),
      u * p ∈ K → 1 + sigma (a * (u * p) * a⁻¹) ≤
        C * (rationalTorusCharacterOrder i alpha a : ℝ) →
      u ∈ Gamma.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype := by
  have := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let J := simpleRelativeRoots i nu \ {alpha}
  let chi := CommGroupScheme.groupHom zeta ≫ i
  let Ubar := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  let P := standardParabolicPoints i nu J
  have hstd := (standardCocharacter F G hG T i hi nu hnu J Set.sdiff_subset).2 zeta hzeta
  obtain ⟨d, j, tau, characters, _, hstab, hdiag, _⟩ :=
    exists_maximalParabolic_orbitPairing_gap i hG hi nu hnu alpha halpha
  have hstabrat : tau.IsRationalLineStabilizer j P := hstab.isRationalLineStabilizer
  have hstabdyn : tau.IsRationalLineStabilizer j (Dynamic.parabolic chi).rationalPoints := by
    rw [← hstd.1]
    exact hstabrat
  have hlineJ : (tau.restrict (Standard.parabolicHom i nu J)).PreservesCoordinateLine j := by
    intro Z x
    have hx := ((Standard.isRepresentedBy_parabolicHom i nu J).pointsEquiv Z x).property
    simpa only [pointMatrix_restrict] using
      (hstab Z (x ≫ (Standard.parabolicHom i nu J).hom.hom)).mp hx
  have hP0 : standardParabolic i nu ∅ ≤ standardParabolic i nu J :=
    ((standardParabolicOrder F G hG T i hi nu hnu).1 ∅ J
      (Set.empty_subset _) Set.sdiff_subset).1.mp (Set.empty_subset _)
  have hline0 : (tau.restrict (Standard.parabolicHom i nu ∅)).PreservesCoordinateLine j := by
    intro Z x
    have hx := ((Standard.isRepresentedBy_parabolicHom i nu ∅).pointsEquiv Z x).property
    simpa only [pointMatrix_restrict] using
      (hstab Z (x ≫ (Standard.parabolicHom i nu ∅).hom.hom)).mp (hP0 Z hx)
  let e : Fin (d + 1) → ℤ := fun r => latticePairing T
    ((rationalCharacters.equivCharacterLattice T) (characters r)) zeta
  have hchi : chi ≫ tau = GeneralLinear.diagonalCocharacter (Fin (d + 1))
      (CommRingCat.of F) e := (Category.assoc _ _ _).trans (hdiag.cocharacter zeta)
  obtain ⟨C2, hC2, hb⟩ := exists_orbitCoordinate_exp_bound rho hrho tau
  obtain ⟨C3, hC3, hlower⟩ := exists_orbitCoordinate_lower_bound tau j hK
  obtain ⟨C5, hC5, hsmall⟩ :=
    hasOrbitCoordinateNeighborhoodRecovery_of_parabolic_line rho hrho tau j chi e hchi hstabdyn Gamma
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let w : rationalPoints G → Fin (d + 1) → ℝ := fun g r =>
    ‖(tau.rationalMatrix g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) r j‖
  let C4 := Real.log (LocalField.residueCardinality F : ℝ) / (latticePairing T alpha zeta : ℝ)
  have hC4 : 0 < C4 := div_pos (Real.log_pos (by exact_mod_cast LocalField.residueCardinality_gt_one F))
    (by exact_mod_cast hzeta.2.2 alpha halpha (by simp))
  refine mem_of_coordinate_bounds (i₁ := j) (w := w) (σ := sigma)
    (t := fun a => (rationalTorusCharacterOrder i alpha a : ℝ))
    (A := rationalMinimalChamber i nu) (K := K) (Ubar := (Ubar : Set (rationalPoints G)))
    (P := (P : Set (rationalPoints G)))
    (Γbar := (Gamma.toSubgroup.map Ubar.subtype : Set (rationalPoints G)))
    hC2 hC3 hC4 hC5 (fun g => (rationalHeight_nonneg rho g).trans (hsigma g)) ?_
    hlower ?_ ?_ ?_ ?_
  · intro g r
    exact (hb g r j).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by linarith [hsigma g]) hC2.le))
  · intro a ha g r hr
    obtain ⟨a0, rfl, ha0⟩ := (mem_rationalMinimalChamber_iff_order i nu a).mp ha
    rw [rationalTorusCharacterOrder_map]
    exact tau.maximalParabolic_orbit_norm_growth i hG hi nu hnu hdiag j hline0
      alpha halpha zeta hzeta hlineJ g r hr a0 ha0
  · intro u hu p hp
    exact hstabrat.orbitCoordinate_mul u p hp
  · intro u hu
    change ‖(tau.rationalMatrix u : Matrix (Fin (d + 1)) (Fin (d + 1)) F) j j‖ = 1
    rw [rationalMatrix_line_entry_eq_one_of_mem_opposite_unipotent tau chi e hchi u hu j,
      norm_one]
  · intro u hu hcoords
    exact ⟨⟨u, hu⟩, hsmall ⟨u, hu⟩ hcoords, rfl⟩


section Density

attribute [local instance] rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace

private local instance : T2Space (rationalPoints G) := rationalPoint_t2Space F G

/-- The actual opposite-unipotent/parabolic product is dense. Haar conullness
of the inverse open cell gives density in the exact rational-point topology. -/
theorem dense_oppositeUnipotent_mul_parabolic (hG : IsConnectedReductive G)
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Dense (((Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints :
      Set (rationalPoints G)) * ((Dynamic.parabolic chi).rationalPoints : Set (rationalPoints G))) := by
  have hconull := rationalDynamicOpenCellConull F G hG chi
    (MeasureTheory.Measure.haar (G := rationalPoints G)) inferInstance
  have hR : Dense (Set.range (openCellMap
      (P := (Dynamic.parabolic chi).rationalPoints)
      (V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints))) :=
    MeasureTheory.Measure.dense_of_ae («μ» := MeasureTheory.Measure.haar (G := rationalPoints G)) hconull
  have hi := hR.preimage (Homeomorph.inv (rationalPoints G)).isOpenMap
  have heq : ((fun x : rationalPoints G => x⁻¹) ⁻¹' Set.range (openCellMap
      (P := (Dynamic.parabolic chi).rationalPoints)
      (V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints))) =
      ((Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints : Set (rationalPoints G)) *
        ((Dynamic.parabolic chi).rationalPoints : Set (rationalPoints G)) := by
    ext x
    constructor
    · rintro ⟨⟨p, u⟩, hpu⟩
      change (p : rationalPoints G) * (u : rationalPoints G)⁻¹ = x⁻¹ at hpu
      refine Set.mem_mul.mpr ⟨u, u.2, (p : rationalPoints G)⁻¹, inv_mem p.2, ?_⟩
      simpa only [_root_.mul_inv_rev, inv_inv] using congrArg Inv.inv hpu
    · rintro ⟨u, hu, p, hp, rfl⟩
      exact ⟨(⟨p⁻¹, inv_mem hp⟩, ⟨u, hu⟩), by simp [openCellMap, _root_.mul_inv_rev]⟩
  change Dense ((fun x : rationalPoints G => x⁻¹) ⁻¹' Set.range (openCellMap
    (P := (Dynamic.parabolic chi).rationalPoints)
    (V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints))) at hi
  rwa [heq] at hi

/-- The full-point conclusion of step (3) of II.3.5 for the auxiliary
compact-invariant height. All density and height assumptions of the generic
lemma are discharged for the actual groups. -/
theorem exists_mem_opposite_open_mul_of_small_compactHeight
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (Gamma : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)) :
    ∃ C > 0, ∀ a ∈ rationalMinimalChamber i nu, ∀ g : rationalPoints G,
      1 + rationalCompactHeight rho K.toSubgroup g +
        rationalCompactHeight rho K.toSubgroup (a * g * a⁻¹) ≤
        C * (rationalTorusCharacterOrder i alpha a : ℝ) →
      g ∈ (Gamma.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype :
          Set (rationalPoints G)) *
        (standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}) : Set (rationalPoints G)) := by
  let J := simpleRelativeRoots i nu \ {alpha}
  let chi := CommGroupScheme.groupHom zeta ≫ i
  let Ubar := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  let P := standardParabolicPoints i nu J
  let sigma := rationalCompactHeight rho K.toSubgroup
  let GammaSet : Set (rationalPoints G) := Gamma.toSubgroup.map Ubar.subtype
  obtain ⟨D, hD, hb⟩ := rationalCompactHeight_bounds rho K.toSubgroup hK
  obtain ⟨C7, hC7, h33⟩ := exists_one_add_rationalHeight_conj_le_on_chamber hG hi hnu rho
  let C7' := (1 + 2 * D) * C7
  have hC7' : 1 ≤ C7' := one_le_mul_of_one_le_of_one_le (by linarith) hC7
  have h33' : ∀ a ∈ rationalMinimalChamber i nu, ∀ p ∈ standardParabolicPoints i nu ∅,
      1 + sigma (a * p * a⁻¹) ≤ C7' * (1 + sigma p) := by
    intro a ha p hp
    calc
      _ ≤ (1 + 2 * D) * (1 + rationalHeight (F := F) rho (a * p * a⁻¹)) := (hb _).2.2
      _ ≤ (1 + 2 * D) * (C7 * (1 + rationalHeight (F := F) rho p)) :=
        mul_le_mul_of_nonneg_left (h33 a ha p hp) (by linarith)
      _ ≤ C7' * (1 + sigma p) := by
        dsimp only [C7']
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (by linarith [(hb p).1]) (by linarith)) (by linarith)
  obtain ⟨C1, hC1, h2⟩ := exists_mem_opposite_open_of_small_conj_on_compact hG i hi nu hnu
    alpha halpha zeta hzeta rho hrho sigma (fun g => (hb g).1) K hK Gamma
  have hstd := (standardCocharacter F G hG T i hi nu hnu J Set.sdiff_subset).2 zeta hzeta
  have hP : IsClosed (P : Set (rationalPoints G)) := by
    rw [show P = (Dynamic.parabolic chi).rationalPoints from
      congrArg SubgroupFunctor.rationalPoints hstd.1]
    exact isClosed_rationalPoint_subgroup F (Dynamic.parabolic chi)
      (Dynamic.Affine.parabolicHom chi) (Dynamic.Affine.isRepresentedBy_parabolicHom chi)
      (Dynamic.Affine.isClosedSubgroup_parabolicHom chi)
  have hGammaSet : IsCompact GammaSet := by
    have hi : IsCompact ((Subtype.val : Ubar → rationalPoints G) '' (Gamma : Set Ubar)) :=
      hGamma.image continuous_subtype_val
    exact hi
  have hdense : Dense ((Ubar : Set (rationalPoints G)) * (P : Set (rationalPoints G))) := by
    rw [show P = (Dynamic.parabolic chi).rationalPoints from
      congrArg SubgroupFunctor.rationalPoints hstd.1]
    exact dense_oppositeUnipotent_mul_parabolic hG chi
  have hP0 : standardParabolicPoints i nu ∅ ≤ P :=
    ((standardParabolicOrder F G hG T i hi nu hnu).1 ∅ J
      (Set.empty_subset _) Set.sdiff_subset).1.mp (Set.empty_subset _) _
  have hiwa : ∀ g : rationalPoints G, ∃ k ∈ K.toSubgroup,
      ∃ p ∈ standardParabolicPoints i nu ∅, g = k * p := by
    intro g
    obtain ⟨p, hp, k, hk, heq⟩ := hPK g⁻¹
    refine ⟨k⁻¹, K.inv_mem hk, p⁻¹, inv_mem hp, ?_⟩
    simpa only [_root_.mul_inv_rev, inv_inv] using congrArg Inv.inv heq
  refine ⟨C1 / C7', div_pos hC1 (lt_of_lt_of_le zero_lt_one hC7'), fun a ha g hg => ?_⟩
  refine mem_mul_of_dense (σ := sigma)
    (t := fun a => (rationalTorusCharacterOrder i alpha a : ℝ))
    (A := rationalMinimalChamber i nu) (Γbar := GammaSet) (K := K.toSubgroup)
    (P₀ := standardParabolicPoints i nu ∅) (P := P) (Ubar := Ubar)
    (rationalCompactHeight_nonneg rho K.toSubgroup hK)
    (rationalCompactHeight_mul_le rho K.toSubgroup hK)
    (rationalCompactHeight_inv rho K.toSubgroup) ?_ hP0 hiwa hC7' h33' h2 hdense
    (hP.mul_left_of_isCompact hGammaSet)
    (fun a _ g => eventually_rationalCompactHeight_eq_and_conj rho K a g) ha hg
  intro k hk g
  simpa only [Subgroup.coe_one, mul_one] using
    rationalCompactHeight_mul_mul rho K.toSubgroup ⟨k, hk⟩ 1 g


/-- The actual one-sided open-cell estimate in the original arbitrary closed
matrix height. The compact-invariant auxiliary height is eliminated. -/
theorem exists_mem_opposite_open_mul_of_small_rationalHeight
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (Gamma : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)) :
    ∃ C > 0, ∀ a ∈ rationalMinimalChamber i nu, ∀ g : rationalPoints G,
      1 + rationalHeight (F := F) rho g + rationalHeight (F := F) rho (a * g * a⁻¹) ≤
        C * (rationalTorusCharacterOrder i alpha a : ℝ) →
      g ∈ (Gamma.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype :
          Set (rationalPoints G)) *
        (standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}) : Set (rationalPoints G)) := by
  obtain ⟨C, hC, hmem⟩ := exists_mem_opposite_open_mul_of_small_compactHeight hG i hi nu hnu
    alpha halpha zeta hzeta rho hrho K hK hPK Gamma hGamma
  obtain ⟨D, hD, hb⟩ := rationalCompactHeight_bounds rho K.toSubgroup hK
  have hfactor : 0 < 1 + 4 * D := by linarith
  refine ⟨C / (1 + 4 * D), div_pos hC hfactor, fun a ha g hg => hmem a ha g ?_⟩
  have hsum : 1 + rationalCompactHeight rho K.toSubgroup g +
        rationalCompactHeight rho K.toSubgroup (a * g * a⁻¹) ≤
      (1 + 4 * D) * (1 + rationalHeight (F := F) rho g +
        rationalHeight (F := F) rho (a * g * a⁻¹)) := by
    have h1 := (hb g).2.1
    have h2 := (hb (a * g * a⁻¹)).2.1
    have h3 := rationalHeight_nonneg rho g
    have h4 := rationalHeight_nonneg rho (a * g * a⁻¹)
    nlinarith
  refine hsum.trans ((mul_le_mul_of_nonneg_left hg hfactor.le).trans_eq ?_)
  field_simp

end Density

/-- The closed actual-point one-sided height prerequisite for II.3.5. -/
def RationalOneSidedOpenCellHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (nu : cocharacterLattice T) (_hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (_halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (_hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho) (K : OpenSubgroup (rationalPoints G))
    (_hK : IsCompact (K : Set (rationalPoints G)))
    (_hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (Gamma : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (_hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)),
    ∃ C > 0, ∀ a ∈ rationalMinimalChamber i nu, ∀ g : rationalPoints G,
      1 + rationalHeight (F := F) rho g + rationalHeight (F := F) rho (a * g * a⁻¹) ≤
        C * (rationalTorusCharacterOrder i alpha a : ℝ) →
      g ∈ (Gamma.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype :
          Set (rationalPoints G)) *
        (standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}) : Set (rationalPoints G))

/-- The exact one-sided closed proposition, proved uniformly in every choice. -/
theorem rationalOneSidedOpenCellHeight : RationalOneSidedOpenCellHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG T i hi nu hnu alpha halpha zeta hzeta N _ rho hrho K hK hPK Gamma hGamma
  exact exists_mem_opposite_open_mul_of_small_rationalHeight hG i hi nu hnu alpha halpha
    zeta hzeta rho hrho K hK hPK Gamma hGamma


end Langlands.HarishChandraSchwartz
