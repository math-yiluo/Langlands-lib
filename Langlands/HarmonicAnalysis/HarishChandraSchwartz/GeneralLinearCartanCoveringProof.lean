import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearCartanCoveringStatement
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer
import Langlands.GroupScheme.Rational.GeneralLinearStandardParabolicProof
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Group.GL.CartanProof

/-! # Matrix Cartan factorizations on actual general linear points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

open GroupScheme.GeneralLinear
open Langlands.GeneralLinear
open Aubert.General (characterNorm_latticeSection)
open Aubert.General.RationalPointFamily (FiniteCartanCovering)

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
local notation "iD" => diagonalTorus (Fin N) (CommRingCat.of F)
local notation "ϖ" => SplitTorusValuation.uniformizerUnit F
set_option quotPrecheck false in
local notation "K₀" => IntegralModel.integralPoints (standardIntegralModel ↥𝒪[F] F (Fin N))
local notation "eG" => rationalPointsEquiv N (CommRingCat.of F)

private def torusPoint (w : Fin N → ℤ) : rationalPoints (𝔻).toGrp :=
  CocharacterUniformizer.latticeSection F 𝔻 (Multiplicative.ofAdd (cocharacterOfWeights F w))

private theorem canonicalUniformizingElement :
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ := by
  let e := FML.normalizedMultiplicativeValuation F
  have hϖ0 : (ϖ : F) ≠ 0 := Units.ne_zero _
  have hϖexp : e (ϖ : F) = WithZero.exp (-1) := by
    have h := LocalField.ord_uniformizer F
    change FML.ord F (ϖ : F) = ((1 : ℤ) : WithTop ℤ) at h
    rw [FML.ord_of_ne_zero F hϖ0, WithTop.coe_inj] at h
    change -WithZero.log (e (ϖ : F)) = 1 at h
    have hlog : WithZero.log (e (ϖ : F)) = -1 := by omega
    rw [← hlog, WithZero.exp_log (e.ne_zero_iff.mpr hϖ0)]
  refine ⟨?_, fun x hx => ?_⟩
  · apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono.lt_iff_lt.mp
    change e (ϖ : F) < e 1
    rw [hϖexp, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · refine ⟨-WithZero.log (e x), ?_⟩
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective
    rw [map_zpow₀]
    change e x = e (ϖ : F) ^ (-WithZero.log (e x))
    rw [hϖexp, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
      WithZero.exp_log (e.ne_zero_iff.mpr hx)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mem_integralPoints_iff (g : rationalPoints (groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ K₀ ↔ eG g ∈ Iwasawa.integralRange (ValuativeRel.valuation F) N :=
  mem_standardIntegralModel_integralPoints_iff ↥𝒪[F] F g

set_option maxHeartbeats 800000 in
private theorem matrix_uniformizerPower (w : Fin N → ℤ) :
    eG (rationalPoints.map iD (torusPoint F N w)) = Iwasawa.torus ϖ w := by
  let x := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm ϖ
  change eG ((x ≫ (CommGroupScheme.groupHom (cocharacterOfWeights F w)).hom.hom) ≫
    (iD).hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, cocharacterOfWeights_comp_diagonalTorus]
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
    (pointsEquiv (Fin N) (CommRingCat.of F) _
      (x ≫ (diagonalCocharacter (Fin N) (CommRingCat.of F) w).hom.hom)) = _
  rw [pointsEquiv_diagonalCocharacter]
  erw [map_diagonalUnits]
  change diagonalUnits F w (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F))) x) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem uniformizerPower_mem_chamber (J : Set (characterLattice 𝔻)) (w : Fin N → ℤ)
    (h : ∀ α ∈ J, 0 ≤ latticePairing 𝔻 α (cocharacterOfWeights F w)) :
    torusPoint F N w ∈ CocharacterUniformizer.CAplus F 𝔻 J := by
  refine ⟨⟨_, rfl⟩, fun α hα => ?_⟩
  unfold torusPoint
  rw [characterNorm_latticeSection]
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (LocalField.residueCardinality_gt_one F).le)
    (neg_nonpos.mpr (h α hα))

private theorem ambientCover (ν : cocharacterLattice 𝔻)
    (hν : StrictAnti (cocharacterCoordEquiv (Fin N) F ν)) :
    FiniteCartanCovering F iD ν K₀ := by
  classical
  refine ⟨{1}, fun g => ?_⟩
  obtain ⟨w, hw, k₁, hk₁, k₂, hk₂, hg⟩ :=
    (Langlands.GeneralLinear.Cartan.cartanDecomposition F _
      (ValuativeRel.valuation F) ϖ (canonicalUniformizingElement F) N (eG g)).exists
  refine ⟨(eG).symm k₁, (eG).symm k₂, 1, torusPoint F N w, ?_, ?_,
    Finset.mem_singleton_self _, ?_, ?_⟩
  · exact (mem_integralPoints_iff F N _).mpr (by simpa only [MulEquiv.apply_symm_apply])
  · exact (mem_integralPoints_iff F N _).mpr (by simpa only [MulEquiv.apply_symm_apply])
  · apply uniformizerPower_mem_chamber
    intro α hα
    rw [simpleRelativeRoots_diagonalTorus F ν hν] at hα
    obtain ⟨j, rfl⟩ := hα
    rw [latticePairing_simpleRootCharacter, cocharacterCoordEquiv_cocharacterOfWeights]
    apply sub_nonneg.mpr (hw _)
    change j.val ≤ j.val + 1
    omega
  · apply (eG).injective
    simp only [Subgroup.coe_one, mul_one, map_mul, MulEquiv.apply_symm_apply]
    rwa [matrix_uniformizerPower]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem leviEmbedding_mem_integralRange (B : BlockShape N) (k : B.Levi F)
    (hk : ∀ b, k b ∈ Iwasawa.integralRange (ValuativeRel.valuation F) (B.size b)) :
    B.leviEmbedding F k ∈ Iwasawa.integralRange (ValuativeRel.valuation F) N := by
  choose k₀ hk₀ using fun b => MonoidHom.mem_range.mp (hk b)
  refine ⟨B.leviEmbedding ↥𝒪[F] k₀, ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨⟨b, x⟩, rfl⟩ := B.indexEquiv.surjective i
  obtain ⟨⟨c, y⟩, rfl⟩ := B.indexEquiv.surjective j
  change Matrix.GeneralLinearGroup.map _ (B.leviEmbedding ↥𝒪[F] k₀)
    (B.index b x) (B.index c y) = B.leviEmbedding F k (B.index b x) (B.index c y)
  rw [Matrix.GeneralLinearGroup.map_apply]
  by_cases h : b = c
  · subst c
    rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same, ← hk₀ b,
      Matrix.GeneralLinearGroup.map_apply]
  · rw [B.leviEmbedding_apply_ne _ _ x y h, B.leviEmbedding_apply_ne _ _ x y h, map_zero]

private theorem matrix_blockTorus (B : BlockShape N) (w : Fin N → ℤ) :
    B.leviEmbedding F (fun b => Iwasawa.torus ϖ (fun x => w (B.index b x))) =
      Iwasawa.torus ϖ w := by
  apply Units.ext
  ext i j
  obtain ⟨⟨b, x⟩, rfl⟩ := B.indexEquiv.surjective i
  obtain ⟨⟨c, y⟩, rfl⟩ := B.indexEquiv.surjective j
  change B.leviEmbedding F _ (B.index b x) (B.index c y) =
    (Iwasawa.torus ϖ w).val (B.index b x) (B.index c y)
  by_cases h : b = c
  · subst c
    rw [B.leviEmbedding_apply_same]
    simp only [Iwasawa.torus_val, Matrix.diagonal_apply, (B.index b).injective.eq_iff]
  · have hne : B.index b x ≠ B.index c y := fun hxy =>
      h (congrArg Sigma.fst (B.indexEquiv.injective hxy))
    rw [B.leviEmbedding_apply_ne _ _ x y h, Iwasawa.torus_val, Matrix.diagonal_apply_ne _ hne]

private theorem blockChamber (B : BlockShape N)
    (weights : ∀ b : Fin B.length, Fin (B.size b) → ℤ)
    (hweights : ∀ b, Antitone (weights b)) :
    let w := fun x : Fin N => weights (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
    torusPoint F N w ∈ CocharacterUniformizer.CAplus F 𝔻 (blockSimpleRoots F B) := by
  dsimp only
  apply uniformizerPower_mem_chamber
  rintro _ ⟨j, hj, rfl⟩
  rw [latticePairing_simpleRootCharacter, cocharacterCoordEquiv_cocharacterOfWeights]
  apply sub_nonneg.mpr
  let x := (adjacentRootPair j).val.1
  let y := (adjacentRootPair j).val.2
  have hxy : x ≤ y := by
    change j.val ≤ j.val + 1
    omega
  have hblock : (B.indexEquiv.symm x).1 = (B.indexEquiv.symm y).1 :=
    (blockIndex_adjacent_eq_iff B j).mpr ((BlockShape.mem_uncuts_iff B j).mp hj)
  obtain ⟨⟨b, r⟩, hr⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨c, s⟩, hs⟩ := B.indexEquiv.surjective y
  change (B.index b r : Fin N) = x at hr
  change (B.index c s : Fin N) = y at hs
  rw [← hr, ← hs] at hxy hblock
  change B.index b r ≤ B.index c s at hxy
  change (B.indexEquiv.symm (B.indexEquiv ⟨b, r⟩)).1 =
    (B.indexEquiv.symm (B.indexEquiv ⟨c, s⟩)).1 at hblock
  simp only [Equiv.symm_apply_apply] at hblock
  subst c
  have hrs : r ≤ s := (Langlands.Geometric.index_strictMono B b).le_iff_le.mp hxy
  change weights (B.indexEquiv.symm y).1 (B.indexEquiv.symm y).2 ≤
    weights (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
  rw [← hr, ← hs]
  change weights (B.indexEquiv.symm (B.indexEquiv ⟨b, s⟩)).1
      (B.indexEquiv.symm (B.indexEquiv ⟨b, s⟩)).2 ≤
    weights (B.indexEquiv.symm (B.indexEquiv ⟨b, r⟩)).1
      (B.indexEquiv.symm (B.indexEquiv ⟨b, r⟩)).2
  rw [B.indexEquiv.symm_apply_apply ⟨b, s⟩, B.indexEquiv.symm_apply_apply ⟨b, r⟩]
  exact hweights b hrs

set_option maxHeartbeats 800000 in
private theorem leviCover (ν : cocharacterLattice 𝔻)
    (hν : StrictAnti (cocharacterCoordEquiv (Fin N) F ν))
    (J : Set (characterLattice 𝔻)) (hJ : J ⊆ simpleRelativeRoots iD ν) :
    StandardLeviCartanCovering F iD ν J K₀ := by
  classical
  have hgeneric : IsGenericCocharacter iD ν :=
    (isGenericCocharacter_diagonalTorus_iff F ν).mpr hν.injective
  obtain ⟨_, hLevi, hBlocks⟩ := generalLinearStandardParabolic F N ν hgeneric hν
  obtain ⟨B, rfl, -⟩ := hBlocks J hJ
  have hmem := (hLevi B).2.2.2.2.1
  rw [← rationalPointsEquiv_toMonoidHom] at hmem
  refine ⟨{1}, fun m hm => ?_⟩
  rw [hmem] at hm
  obtain ⟨b, hb⟩ := hm
  change B.leviEmbedding F b = eG m at hb
  have hcartan (j : Fin B.length) :=
    (Langlands.GeneralLinear.Cartan.cartanDecomposition F _
      (ValuativeRel.valuation F) ϖ (canonicalUniformizingElement F) (B.size j) (b j)).exists
  choose lam hlam k₁ hk₁ k₂ hk₂ heq using hcartan
  let w := fun x : Fin N => lam (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
  have htorus : B.leviEmbedding F (fun j => Iwasawa.torus ϖ (lam j)) = Iwasawa.torus ϖ w := by
    rw [← matrix_blockTorus F N B w]
    congr 1
    funext j
    congr 1
    funext x
    change lam j x = lam (B.indexEquiv.symm (B.indexEquiv ⟨j, x⟩)).1
      (B.indexEquiv.symm (B.indexEquiv ⟨j, x⟩)).2
    rw [Equiv.symm_apply_apply]
  have hk (k : B.Levi F)
      (hk : ∀ j, k j ∈ Iwasawa.integralRange (ValuativeRel.valuation F) (B.size j)) :
      (eG).symm (B.leviEmbedding F k) ∈ K₀ ⊓ standardLeviPoints iD ν (blockSimpleRoots F B) := by
    constructor
    · apply (mem_integralPoints_iff F N _).mpr
      rw [MulEquiv.apply_symm_apply]
      exact leviEmbedding_mem_integralRange F N B k hk
    · rw [hmem]
      exact ⟨k, (eG).apply_symm_apply _ |>.symm⟩
  refine ⟨(eG).symm (B.leviEmbedding F k₁), (eG).symm (B.leviEmbedding F k₂), 1,
    torusPoint F N w, hk k₁ hk₁, hk k₂ hk₂, Finset.mem_singleton_self _,
    blockChamber F N B lam hlam, ?_⟩
  apply (eG).injective
  simp only [Subgroup.coe_one, mul_one, map_mul, MulEquiv.apply_symm_apply]
  rw [matrix_uniformizerPower, ← htorus, ← map_mul, ← map_mul, ← hb]
  congr 1
  exact funext heq

/-- The actual integral-model subgroup realizes both Cartan coverings. -/
theorem generalLinearCartanCovering : GeneralLinearCartanCoveringStatement.{u} := by
  intro F _ _ _ _ N
  dsimp only
  intro ν hν
  exact ⟨ambientCover F N ν hν, leviCover F N ν hν⟩

end Langlands.HarishChandraSchwartz
