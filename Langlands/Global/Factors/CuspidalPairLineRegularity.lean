import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementLine
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.BlockCharacterProof
import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralProduct

/-! # Regularity of Shahidi's line for the upper two-block parabolic

For the chosen root presentation `blockRootData` of the scheme block parabolic of type
`(r + 1, t + 1)` in `GL_N`, the parameters `s λ₁` of the line `lineParameter` are `R`-regular in
the sense of `IsRegularParameter` once `Re s` is large. The proof shows that `λ₁`, restricted to
the split component, is a positive multiple of every root of the split component in the unipotent
radical, for the Weyl-induced positive form. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear

variable (F : Type u) [Field F] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "wt" => blockShapeWeight B
local notation "mG" => blockLeviHom (Fin n) 𝕜 wt

/-- The block determinant characters of the parabolic restrict to those of the Levi. -/
theorem characterRestrict_blockLeviInclusion_parabolicBlockCharacter (i : Fin B.length) :
    characterRestrict (blockLeviInclusion F B) (parabolicBlockCharacter B 𝕜 i) =
      blockDeterminantCharacter 𝕜 B i := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [characterEval_characterRestrict, parabolicBlockCharacter, characterEval_characterRestrict,
    characterEval_determinantCharacter, pointsEquiv_parabolicBlockHom]
  apply Units.ext
  rw [characterEval_blockDeterminantCharacter, Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, B.leviProjection_apply, blockParabolicTestPointsEquiv_val,
    Category.assoc, ← Grp.comp_hom_hom, blockLeviInclusion_comp]

/-- An endomorphism of `𝔾_m` that is the `m`-th power on all points has `gmEndEquiv` value
`m`. -/
theorem gmEndEquiv_eq_of_points {f : Gm (Spec 𝕜) ⟶ Gm (Spec 𝕜)} (m : ℤ)
    (h : ∀ (U : Over (Spec 𝕜)) (x : U ⟶ (Gm (Spec 𝕜)).X),
      x ≫ (CommGroupScheme.groupHom f).hom.hom = x ^ m) :
    gmEndEquiv F f = m := by
  have hf : f = (gmEndEquiv F).symm m := by
    apply CommGroupScheme.hom_ext_points
    intro U x
    rw [h, gmEndEquiv_symm_comp]
  rw [hf, AddEquiv.apply_symm_apply]

/-- The pairing of a block determinant, restricted to a commutative group scheme mapping to the
block Levi, with a cocharacter whose image in `GL_n` is diagonal with weight `c` on the block. -/
theorem latticePairing_restrict_blockDeterminantCharacter {A : CommGroupScheme (Spec 𝕜)}
    (j : A.toGrp ⟶ blockLeviScheme (Fin n) 𝕜 wt) (e : Fin n → ℤ) (ν : cocharacterLattice A)
    (hν : CommGroupScheme.groupHom ν ≫ j ≫ mG = diagonalCocharacter (Fin n) 𝕜 e)
    (i : Fin B.length) (c : ℤ) (hc : ∀ a, e (B.index i a) = c) :
    latticePairing A (characterRestrict j (blockDeterminantCharacter 𝕜 B i)) ν =
      (B.size i : ℤ) * c := by
  rw [latticePairing_apply]
  apply gmEndEquiv_eq_of_points
  intro U x
  apply (Gm.pointsEquiv (Spec 𝕜) U).injective
  rw [map_zpow]
  change characterEval (blockDeterminantCharacter 𝕜 B i) U
    (x ≫ (CommGroupScheme.groupHom ν ≫ j).hom.hom) = _
  apply Units.ext
  rw [characterEval_blockDeterminantCharacter, Category.assoc, ← Grp.comp_hom_hom,
    Category.assoc, hν, pointsEquiv_diagonalCocharacter, coe_diagonalUnits,
    Matrix.submatrix_diagonal _ _ (B.index i).injective, Matrix.det_diagonal]
  simp only [Function.comp_apply, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm]

section RootData

local notation "M" => blockLeviScheme (Fin n) 𝕜 wt

local instance blockRegularityLeviAffineHom : IsAffineHom (M).X.hom :=
  (blockLevi_isConnectedReductive F B).isAffineHom

/-- The defining diagonal cocharacter of the block parabolic lifts to the chosen split
component. -/
theorem exists_diagonalCocharacter_lift :
    ∃ eta : cocharacterLattice (blockRootData F B).A,
      CommGroupScheme.groupHom eta ≫ (blockRootData F B).a ≫ mG =
        diagonalCocharacter (Fin n) 𝕜 wt :=
  (blockRootData F B).root.isCompatible.splitComponent.exists_cocharacter_factor_of_dynamicCentralizer
    _ (isRepresentedBy_centralizer_diagonalCocharacter (Fin n) 𝕜 wt)

/-- The scalar torus, as a cocharacter of the block Levi. -/
def scalarLeviCocharacter : (Gm (Spec 𝕜)).toGrp ⟶ M :=
  (isRepresentedBy_blockLevi (Fin n) 𝕜 wt).factorHom (scalarTorus (Fin n) 𝕜) <| by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine (mem_blockLevi wt).mpr fun i j hij => ?_
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    rw [scalarTorus_eq_diagonalCocharacter, pointsEquiv_diagonalCocharacter, coe_diagonalUnits,
      Matrix.diagonal_apply_ne _ hne]

theorem scalarLeviCocharacter_comp : scalarLeviCocharacter F B ≫ mG = scalarTorus (Fin n) 𝕜 :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The scalar torus lifts to the chosen split component. -/
theorem exists_scalarTorus_lift :
    ∃ z : cocharacterLattice (blockRootData F B).A,
      CommGroupScheme.groupHom z ≫ (blockRootData F B).a ≫ mG = scalarTorus (Fin n) 𝕜 := by
  have hc : IsCentral (scalarLeviCocharacter F B) :=
    CoverPreimage.isCentral_of_comp_mono isCentral_scalarTorus mG (scalarLeviCocharacter F B)
      (scalarLeviCocharacter_comp F B)
  obtain ⟨g, hg⟩ := (blockRootData F B).root.isCompatible.splitComponent.exists_factor
    isSplitTorus_gm hc
  refine ⟨Additive.ofMul g, ?_⟩
  change g ≫ (blockRootData F B).a ≫ mG = _
  rw [← Category.assoc, hg, scalarLeviCocharacter_comp]

/-- The restrictions of the block determinants to the split component, as real characters. -/
def restrictedBlockDeterminant (i : Fin B.length) : RealTorusSpace.Vstar (blockRootData F B).A :=
  (1 : ℝ) ⊗ₜ[ℤ] rationalCharacters.equivCharacterLattice _
    (characterRestrict (blockRootData F B).a (blockDeterminantCharacter 𝕜 B i))

/-- The restricted block determinants span the real character space of the split component. -/
theorem mem_span_restrictedBlockDeterminant (y : RealTorusSpace.Vstar (blockRootData F B).A) :
    y ∈ Submodule.span ℝ (Set.range (restrictedBlockDeterminant F B)) := by
  set V := Submodule.span ℝ (Set.range (restrictedBlockDeterminant F B))
  have hidx := (blockRootData F B).root.isCompatible.splitComponent.finiteIndex_range_characterRestrict
    (blockLevi_isConnectedReductive F B)
  have hone : ∀ χ : characterLattice (blockRootData F B).A, (1 : ℝ) ⊗ₜ[ℤ] χ ∈ V := by
    intro χ
    have hmem := AddSubgroup.nsmul_index_mem (characterRestrict (blockRootData F B).a).range χ
    obtain ⟨ψ, hψ⟩ := hmem
    obtain ⟨m, rfl⟩ := blockDetCombination_surjective B 𝕜 ψ
    have hne : ((characterRestrict (blockRootData F B).a).range.index : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hidx.index_ne_zero
    have hsum : ((characterRestrict (blockRootData F B).a).range.index : ℝ) •
        ((1 : ℝ) ⊗ₜ[ℤ] χ) = ∑ i, (m i : ℝ) • restrictedBlockDeterminant F B i := by
      have h1 := map_nsmul (TensorProduct.mk ℤ ℝ (characterLattice (blockRootData F B).A) 1)
        (characterRestrict (blockRootData F B).a).range.index χ
      calc ((characterRestrict (blockRootData F B).a).range.index : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] χ)
          = (characterRestrict (blockRootData F B).a).range.index • ((1 : ℝ) ⊗ₜ[ℤ] χ) :=
            Nat.cast_smul_eq_nsmul ℝ _ _
        _ = (1 : ℝ) ⊗ₜ[ℤ] ((characterRestrict (blockRootData F B).a).range.index • χ) :=
            h1.symm
        _ = (1 : ℝ) ⊗ₜ[ℤ] (characterRestrict (blockRootData F B).a
              (blockDetCombination B 𝕜 m) : characterLattice (blockRootData F B).A) := by
            rw [hψ]
        _ = ∑ i, (m i : ℝ) • restrictedBlockDeterminant F B i := by
            rw [blockDetCombination_apply, map_sum, TensorProduct.tmul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_zsmul]
            exact (map_zsmul (TensorProduct.mk ℤ ℝ _ 1) (m i) _).trans
              (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have h := congrArg (fun v => (((characterRestrict (blockRootData F B).a).range.index : ℝ))⁻¹ • v)
      hsum
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
    rw [h]
    exact V.smul_mem _ (V.sum_mem fun i _ => V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  induction y using TensorProduct.inductionOn with
  | tmul c χ =>
    have : c ⊗ₜ[ℤ] χ = c • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact V.smul_mem c (hone χ)
  | add y y' hy hy' => exact V.add_mem hy hy'

end RootData

end Langlands.Global.AdelicBlockEisensteinGeometry

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints RealTorusSpace

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

local notation "𝕜" => CommRingCat.of F
local notation "Bk" => blockShape r t
local notation "D" => blockRootData F (blockShape r t)

theorem univ_blocks :
    (Finset.univ : Finset (Fin (blockShape r t).length)) = {firstBlock r t, secondBlock r t} := by
  ext i
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_firstBlock_or_eq_secondBlock r t i

/-- The restriction of the real part of `λ₁` to the split component. -/
def lineRestriction : Vstar (D).A :=
  realParameterRestriction ((D).a ≫ blockLeviInclusion F Bk)
    (parameterRealPart F _ (lineParameter F r t))

omit [NumberField F] in
theorem lineRestriction_eq :
    lineRestriction F r t =
      ((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) • restrictedBlockDeterminant F Bk (firstBlock r t) +
        (-((r + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ)) •
          restrictedBlockDeterminant F Bk (secondBlock r t) := by
  have hre : ∀ (c : ℝ) (χ), parameterRealPart F
      (blockParabolicScheme (Fin (r + t + 2)) 𝕜 (blockShapeWeight Bk)) ((c : ℂ) ⊗ₜ[ℤ] χ) =
      c ⊗ₜ[ℤ] χ := fun c χ => by
    rw [parameterRealPart_tmul, Complex.ofReal_re]
  have hres : ∀ (c : ℝ) (i : Fin (blockShape r t).length),
      realParameterRestriction ((D).a ≫ blockLeviInclusion F Bk)
        (c ⊗ₜ[ℤ] parabolicBlockCharacter Bk 𝕜 i) = c • restrictedBlockDeterminant F Bk i := by
    intro c i
    rw [restrictedBlockDeterminant, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change c ⊗ₜ[ℤ] (characterRestrict ((D).a ≫ blockLeviInclusion F Bk)
      (parabolicBlockCharacter Bk 𝕜 i)) = _
    rw [characterRestrict_comp, AddMonoidHom.comp_apply,
      characterRestrict_blockLeviInclusion_parabolicBlockCharacter]
    rfl
  have h0 : (((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) =
      (((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have h1 : (-(((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) =
      ((-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
  rw [lineRestriction, lineParameter, h0, h1, map_add, hre, hre, map_add, hres, hres]

local notation "mN" => blockLeviHom (Fin (r + t + 2)) 𝕜 (blockShapeWeight (blockShape r t))

/-- A lift of the scalar torus to the split component. -/
def scalarLift : cocharacterLattice (D).A := (exists_scalarTorus_lift F Bk).choose

omit [NumberField F] in
theorem scalarLift_spec :
    CommGroupScheme.groupHom (scalarLift F r t) ≫ (D).a ≫ mN =
      scalarTorus (Fin (r + t + 2)) 𝕜 :=
  (exists_scalarTorus_lift F Bk).choose_spec

/-- A lift of the defining diagonal cocharacter to the split component. -/
def diagonalLift : cocharacterLattice (D).A := (exists_diagonalCocharacter_lift F Bk).choose

omit [NumberField F] in
theorem diagonalLift_spec :
    CommGroupScheme.groupHom (diagonalLift F r t) ≫ (D).a ≫ mN =
      diagonalCocharacter (Fin (r + t + 2)) 𝕜 (blockShapeWeight Bk) :=
  (exists_diagonalCocharacter_lift F Bk).choose_spec

omit [NumberField F] in
theorem pair_restrictedBlockDeterminant_scalarLift (i : Fin (blockShape r t).length) :
    pair (D).A (restrictedBlockDeterminant F Bk i) ((1 : ℝ) ⊗ₜ[ℤ] scalarLift F r t) =
      ((blockShape r t).size i : ℝ) := by
  rw [restrictedBlockDeterminant, MaximalLeviConeComplementLine.pair_one_tmul_one_tmul]
  have h := latticePairing_restrict_blockDeterminantCharacter F Bk (D).a (fun _ => 1)
    (scalarLift F r t) (by rw [scalarLift_spec, scalarTorus_eq_diagonalCocharacter]) i 1
    (fun _ => rfl)
  change ((latticePairing (D).A (characterRestrict (D).a (blockDeterminantCharacter 𝕜 Bk i))
    (scalarLift F r t) : ℤ) : ℝ) = _
  rw [h, mul_one, Int.cast_natCast]

omit [NumberField F] in
theorem pair_restrictedBlockDeterminant_diagonalLift (i : Fin (blockShape r t).length) :
    pair (D).A (restrictedBlockDeterminant F Bk i) ((1 : ℝ) ⊗ₜ[ℤ] diagonalLift F r t) =
      ((blockShape r t).size i : ℝ) * (-((i : ℕ) : ℝ)) := by
  rw [restrictedBlockDeterminant, MaximalLeviConeComplementLine.pair_one_tmul_one_tmul]
  have h := latticePairing_restrict_blockDeterminantCharacter F Bk (D).a (blockShapeWeight Bk)
    (diagonalLift F r t) (diagonalLift_spec F r t) i (-((i : ℕ) : ℤ))
    (fun a => blockShapeWeight_index Bk i a)
  change ((latticePairing (D).A (characterRestrict (D).a (blockDeterminantCharacter 𝕜 Bk i))
    (diagonalLift F r t) : ℤ) : ℝ) = _
  rw [h]
  push_cast
  ring

omit [NumberField F] in
theorem pair_lineRestriction_scalarLift :
    pair (D).A (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] scalarLift F r t) = 0 := by
  rw [lineRestriction_eq, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, pair_restrictedBlockDeterminant_scalarLift,
    pair_restrictedBlockDeterminant_scalarLift]
  have hN : ((r + t + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  change ((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) +
    (-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ) * ((t + 1 : ℕ) : ℝ) = 0
  field_simp
  ring

omit [NumberField F] in
theorem pair_lineRestriction_diagonalLift :
    pair (D).A (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] diagonalLift F r t) =
      ((r + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) / ((r + t + 2 : ℕ) : ℝ) := by
  rw [lineRestriction_eq, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, pair_restrictedBlockDeterminant_diagonalLift,
    pair_restrictedBlockDeterminant_diagonalLift]
  change ((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) * (-((0 : ℕ) : ℝ))) +
    (-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ) * (((t + 1 : ℕ) : ℝ) * (-((1 : ℕ) : ℝ))) = _
  push_cast
  ring

section Regularity

local notation "GN" => groupScheme (Fin (r + t + 2)) 𝕜
local notation "pN" => blockParabolicHom (Fin (r + t + 2)) 𝕜 (blockShapeWeight (blockShape r t))

local instance lineRegularityGLAffineHom : IsAffineHom (GN).X.hom :=
  isAffineHom_groupScheme (n := Fin (r + t + 2)) (R := 𝕜)

local instance lineRegularityGLFiniteType : LocallyOfFiniteType (GN).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin (r + t + 2))).smooth
  inferInstance

local instance lineRegularityTorusMono : Mono (D).root.data.i.hom.hom.left := (D).torus_mono

local instance lineRegularityFactorMono :
    Mono (CommGroupScheme.groupHom (D).root.data.f).hom.hom.left := (D).factor_mono

local instance lineRegularityWeylFinite : Fintype (relativeWeylGroup (D).root.data.i) :=
  @Fintype.ofFinite _ (D).finite_weylGroup

omit [NumberField F] in
/-- **The central-annihilator line.** A real character of the split component vanishing on
every central cocharacter is a multiple of `lineRestriction`. -/
theorem lineRestriction_line (y : Vstar (D).A)
    (hy : ∀ ν : cocharacterLattice (D).A,
      IsCentral (CommGroupScheme.groupHom ν ≫ (D).a ≫ blockLeviInclusion F Bk ≫ pN) →
        pair (D).A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) :
    y ∈ Submodule.span ℝ {lineRestriction F r t} := by
  have hz : IsCentral (CommGroupScheme.groupHom (scalarLift F r t) ≫ (D).a ≫
      blockLeviInclusion F Bk ≫ pN) := by
    rw [blockLeviInclusion_comp, scalarLift_spec]
    exact isCentral_scalarTorus
  have h0 := hy _ hz
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_restrictedBlockDeterminant F Bk y)
  rw [univ_blocks, Finset.sum_pair (firstBlock_ne_secondBlock r t)] at hc
  rw [← hc, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, pair_restrictedBlockDeterminant_scalarLift,
    pair_restrictedBlockDeterminant_scalarLift] at h0
  change c (firstBlock r t) * ((r + 1 : ℕ) : ℝ) + c (secondBlock r t) * ((t + 1 : ℕ) : ℝ) = 0
    at h0
  have ht : ((t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hN : ((r + t + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  refine Submodule.mem_span_singleton.mpr
    ⟨c (firstBlock r t) * ((r + t + 2 : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ), ?_⟩
  rw [← hc, lineRestriction_eq]
  have hc1 : c (secondBlock r t) =
      -(c (firstBlock r t) * ((r + 1 : ℕ) : ℝ)) / ((t + 1 : ℕ) : ℝ) := by
    field_simp
    linarith
  rw [hc1]
  match_scalars <;> field_simp

omit [NumberField F] in
/-- **Positivity of `λ₁` on the unipotent roots.** -/
theorem weylInducedCharacterForm_lineRestriction_pos {α : characterLattice (D).A}
    (hα : α ∈ (D).root.unipotentRoots) :
    0 < Langlands.Plancherel.weylInducedCharacterForm (D).splitComponent (D).splitTorus
      (D).root.data.f (D).root.data.i (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  obtain ⟨hα0, β, hβ, rfl⟩ := hα
  obtain ⟨c, hc⟩ := MaximalLeviConeComplementLine.exists_smul_eq_of_line
    (lineRestriction_line F r t) (D).root.data.i (D).root.data.f
    (D).root.isCompatible.factor_comp (positiveRelativeRoots_subset_relativeRoots _ _ hβ)
  have hint := ((D).root.restrict_positive_eq_zero_or_mem hβ).resolve_left hα0
  have hle : Dynamic.parabolic (CommGroupScheme.groupHom (D).root.splitComponentCocharacter ≫
      (D).a ≫ blockLeviInclusion F Bk ≫ pN) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom (diagonalLift F r t) ≫ (D).a ≫
        blockLeviInclusion F Bk ≫ pN) := by
    rw [← (D).root.parabolic_eq_splitComponentCocharacter, blockLeviInclusion_comp,
      diagonalLift_spec,
      ← (isRepresentedBy_parabolic_diagonalCocharacter (Fin (r + t + 2)) 𝕜
        (blockShapeWeight Bk)).2]
  have hnn := RelativeRoot.nonnegative_rootSupport_of_parabolic_le (D).splitComponent
    ((D).a ≫ blockLeviInclusion F Bk ≫ pN) _ _ hle _ hint.1 hint.2.le
  have hpx := pair_lineRestriction_diagonalLift F r t
  have hpos : 0 < pair (D).A (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] diagonalLift F r t) := by
    rw [hpx]
    positivity
  have hceta : c * pair (D).A (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] diagonalLift F r t) =
      (latticePairing (D).A ((D).root.data.f ≫ β) (diagonalLift F r t) : ℝ) := by
    rw [← MaximalLeviConeComplementLine.pair_one_tmul_one_tmul, ← hc, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have h := MaximalLeviConeComplementLine.pair_one_tmul_one_tmul ((D).root.data.f ≫ β)
      (D).root.splitComponentCocharacter
    rw [← hc, map_zero, LinearMap.zero_apply] at h
    have h2 := hint.2
    exact absurd (Int.cast_eq_zero.mp h.symm) h2.ne'
  have hcpos : 0 < c := by
    rcases lt_or_gt_of_ne hc0 with hneg | hpos'
    · have : c * pair (D).A (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] diagonalLift F r t) < 0 :=
        mul_neg_of_neg_of_pos hneg hpos
      rw [hceta] at this
      have hnn' : (0 : ℝ) ≤ (latticePairing (D).A ((D).root.data.f ≫ β) (diagonalLift F r t) : ℝ) := by
        exact_mod_cast hnn
      exact absurd hnn' (not_le.mpr this)
    · exact hpos'
  have hx0 : lineRestriction F r t ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hpos
    exact lt_irrefl 0 hpos
  rw [← hc, map_smul, smul_eq_mul]
  exact mul_pos hcpos (Langlands.Plancherel.weylInducedCharacterForm_pos _ _ _ _ hx0)

omit [NumberField F] in
theorem parameterRealPart_smul_lineParameter (s : ℂ) :
    parameterRealPart F _ (s • lineParameter F r t) =
      s.re • parameterRealPart F _ (lineParameter F r t) := by
  have hre : ∀ (c : ℝ) (χ : GroupScheme.rationalCharacters
      (blockParabolicScheme (Fin (r + t + 2)) 𝕜 (blockShapeWeight Bk))),
      parameterRealPart F _ (s • ((c : ℂ) ⊗ₜ[ℤ] χ)) =
        s.re • parameterRealPart F _ ((c : ℂ) ⊗ₜ[ℤ] χ) := by
    intro c χ
    rw [TensorProduct.smul_tmul', smul_eq_mul, parameterRealPart_tmul, parameterRealPart_tmul,
      Complex.re_mul_ofReal, Complex.ofReal_re, TensorProduct.smul_tmul', smul_eq_mul]
  have h0 : (((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) =
      (((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have h1 : (-(((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) =
      ((-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
  rw [lineParameter, h0, h1, smul_add, map_add, map_add, hre, hre, smul_add]

omit [NumberField F] in
/-- **Regularity of Shahidi's line.** For every threshold `R` there is `σ` such that the
parameter `s • lineParameter F r t` is `R`-regular for the chosen presentation of the block
parabolic whenever `σ < Re s`. -/
theorem exists_isRegularParameter_lineParameter (R : ℝ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (D).root.IsRegularParameter (D).splitComponent (D).splitTorus R
        (s • lineParameter F r t) := by
  have hfin : (D).root.unipotentRoots.Finite :=
    (((D).splitTorus.finite_positiveRelativeRoots (D).root.data.i (D).root.data.ν).image
      fun χ => (D).root.data.f ≫ χ).subset fun _ h => h.2
  let L : characterLattice (D).A → ℝ := fun α =>
    Langlands.Plancherel.weylInducedCharacterForm (D).splitComponent (D).splitTorus
      (D).root.data.f (D).root.data.i (lineRestriction F r t) ((1 : ℝ) ⊗ₜ[ℤ] α)
  obtain ⟨C, hC⟩ := (hfin.image fun α => R / L α).bddAbove
  refine ⟨C, fun s hs α hα => ?_⟩
  have hreal : realParameterRestriction ((D).a ≫ blockLeviInclusion F Bk)
      (parameterRealPart F _ (s • lineParameter F r t)) = s.re • lineRestriction F r t := by
    rw [parameterRealPart_smul_lineParameter, map_smul]
    rfl
  rw [hreal, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hL : 0 < L α := weylInducedCharacterForm_lineRestriction_pos F r t hα
  have hle : R / L α ≤ C := hC ⟨α, hα, rfl⟩
  exact (div_lt_iff₀ hL).mp (lt_of_le_of_lt hle hs)

end Regularity

section Statement

local instance lineStatementTorusMono (F : Type u) [Field F] [NumberField F] (r t : ℕ) :
    Mono (blockRootData F (blockShape r t)).root.data.i.hom.hom.left :=
  (blockRootData F (blockShape r t)).torus_mono

local instance lineStatementFactorMono (F : Type u) [Field F] [NumberField F] (r t : ℕ) :
    Mono (CommGroupScheme.groupHom (blockRootData F (blockShape r t)).root.data.f).hom.hom.left :=
  (blockRootData F (blockShape r t)).factor_mono

local instance lineStatementWeylFinite (F : Type u) [Field F] [NumberField F] (r t : ℕ) :
    Fintype (relativeWeylGroup (blockRootData F (blockShape r t)).root.data.i) :=
  @Fintype.ofFinite _ (blockRootData F (blockShape r t)).finite_weylGroup

/-- **Regularity of Shahidi's line.** For every number field `F : Type u`, all `r t : ℕ` and
every threshold `R`, there is `σ` such that for `Re s > σ` the parameter
`s • lineParameter F r t` of the scheme block parabolic of type `(r + 1, t + 1)` in `GL_N`,
`N = r + t + 2`, is `R`-regular for the presentation `blockRootData`: `R < B(Re(s λ₁)|_A, α)` for
every root `α` of the split component `A` in the unipotent radical, where `B` is the
Weyl-induced positive form of the presentation. -/
def CuspidalPairLineRegularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r t : ℕ) (R : ℝ), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    (blockRootData F (blockShape r t)).root.IsRegularParameter
      (blockRootData F (blockShape r t)).splitComponent
      (blockRootData F (blockShape r t)).splitTorus R (s • lineParameter F r t)

theorem cuspidalPairLineRegularity : CuspidalPairLineRegularityStatement.{u} :=
  fun F _ _ r t R => exists_isRegularParameter_lineParameter F r t R

end Statement

end Langlands.Global.CuspidalPairEisenstein
