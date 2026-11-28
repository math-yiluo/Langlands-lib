import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.ArthurParabolicSpacesProof
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurTruncationRay
import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Relative coroot coordinates of the truncated Eisenstein pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

local notation "T" => fam.T
local notation "P" => fam.P Q
local notation "Pstd" => Standard.parabolicScheme fam.i fam.ν Q.val
local notation "pstd" => Standard.parabolicHom fam.i fam.ν Q.val
local notation "Δ" => simpleRelativeRoots fam.i fam.ν

/-- The kernel of the actual split logarithm projection is the Levi coroot subspace. -/
theorem ker_splitDual : LinearMap.ker (fam.splitDual Q) = ArthurRelative.corootSubspace fam.coroots Q.val := by
  let := fam.isClosedImmersion_p Q
  let rep : (standardParabolic fam.i fam.ν Q.val).IsRepresentedBy (fam.p Q) :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible Q).parabolic_eq⟩
  let can := Standard.isRepresentedBy_parabolicHom fam.i fam.ν Q.val
  let e : Pstd ≅ P := can.isoOfIsRepresentedBy rep
  have he : e.hom ≫ fam.p Q = pstd := can.isoOfIsRepresentedBy_hom_comp rep
  have ht : torusToParabolic F fam.i fam.ν Q.val ≫ e.hom = fam.torus Q ≫ fam.l Q := by
    apply rep.hom_ext
    rw [Category.assoc, he, torusToParabolic_comp, Category.assoc, fam.torus_comp]
  have hmap (v : V T) : fam.splitDual Q v =
      realCharacterDualMap F Pstd P e.hom (toCharacterDual F fam.i fam.ν Q.val v) := by
    apply AddMonoidHom.ext
    intro χ
    change pair T (realParameterRestriction (fam.torus Q ≫ fam.l Q) ((1 : ℝ) ⊗ₜ[ℤ] χ)) v =
      pair T (restrictToTorus F fam.i fam.ν Q.val ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict e.hom χ)) v
    rw [← ht]
    change pair T (rationalCharacterRestrictReal (torusToParabolic F fam.i fam.ν Q.val ≫ e.hom)
      ((1 : ℝ) ⊗ₜ[ℤ] χ)) v = _
    rw [← rationalCharacterRestrictReal_comp_apply, rationalCharacterRestrictReal_tmul]
    rfl
  have hker : LinearMap.ker (toCharacterDual F fam.i fam.ν Q.val) =
      Submodule.span ℝ (fam.coroots.realCorootsOf Q.val) :=
    (parabolicSpacesComparison F G fam.connectedReductive T fam.i fam.maximalSplit
    fam.ν fam.generic fam.coroots Q.val Q.property).2.2.2.1
  change LinearMap.ker (fam.splitDual Q) = Submodule.span ℝ (fam.coroots.realCorootsOf Q.val)
  rw [← hker]
  apply Submodule.ext
  intro v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, hmap]
  constructor
  · intro hv
    have h := congrArg (realCharacterDualMap F P Pstd e.inv) hv
    rw [realCharacterDualMap_comp_apply, e.hom_inv_id, realCharacterDualMap_id_apply] at h
    exact h
  · intro hv
    rw [hv]
    rfl

/-- Projecting the cocharacter to the split summand preserves its character logarithm. -/
theorem splitDual_levelProjection (v : V T) :
    fam.splitDual Q
      (ArthurRelative.levelProjection fam.connectedReductive fam.maximalSplit fam.ν fam.coroots Q.val v) =
        fam.splitDual Q v := by
  have h := ArthurRelative.sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit
    (ν := fam.ν) fam.coroots Q.val v
  change _ ∈ ArthurRelative.corootSubspace fam.coroots Q.val at h
  rw [← fam.ker_splitDual Q, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h.symm

/-- On the relative coroot span, the split logarithm is the sum of the projected coroots
with the full fundamental weights outside the Levi as coefficients. -/
theorem splitDual_eq_sum_relativeCoroot {v : V T} (hv : v ∈ fam.coroots.realCorootSpan) :
    fam.splitDual Q v = ∑ α : fam.relativeSimpleRoots Q,
      fam.weightCoordinate Q v α • fam.relativeCoroot Q α := by
  let hG := fam.connectedReductive
  let hi := fam.maximalSplit
  let D := fam.coroots
  let b := ArthurRelative.base hG hi fam.generic D
  let c (j : b.support) := D.realCoroot ⟨j.1.1, j.1.2.1⟩
  let w := ArthurRelative.weight hG hi fam.ν D Δ
  let := ArthurRelative.finite_indivisibleRoots hG hi
  have hα (j : b.support) : j.1.1 ∈ Δ :=
    (ArthurRelative.mem_support_base hG hi fam.generic D).mp j.2
  have hw (j : b.support) :
      b.toCoweightBasis.repr (⟨v, hv⟩ : D.realCorootSpan) j = w j.1.1 v := by
    rw [ArthurCombinatorics.toCoweightBasis_repr_eq b]
    change _ = ArthurRelative.weight hG hi fam.ν D Δ j.1 v
    rw [ArthurRelative.weight_coe, ArthurRelative.standardIndex_simpleRelativeRoots hG hi D fam.generic,
      show ArthurRelative.toCorootSpan hG hi D v = ⟨v, hv⟩ from
        ArthurRelative.toCorootSpan_apply_coe hG hi D ⟨v, hv⟩]
  have hsum : v = ∑ j : b.support, w j.1.1 v • c j := by
    have he := congrArg Subtype.val (b.toCoweightBasis.sum_repr (⟨v, hv⟩ : D.realCorootSpan))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, RootPairing.Base.toCoweightBasis_apply,
      ArthurRelative.rootPairing_coroot, hw, c] using he.symm
  have hL (j : b.support) (hj : j.1.1 ∈ Q.val) : fam.splitDual Q (c j) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [fam.ker_splitDual Q]
    exact Submodule.subset_span ⟨⟨j.1.1, j.1.2.1⟩, hj, rfl⟩
  let term (j : b.support) := w j.1.1 v • fam.splitDual Q (c j)
  have hsum' : fam.splitDual Q v = ∑ j : b.support, term j := by
    conv_lhs => rw [hsum]
    simp only [term, map_sum, map_smul]
  let out : Set ↥b.support := {j | j.1.1 ∉ Q.val}
  have hfilter : (∑ j : b.support, term j) =
      ∑ j ∈ Finset.univ.filter (fun j => j ∈ out), term j := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => ?_)
    have hmem : j.1.1 ∈ Q.val := by simpa [out] using hj
    simp only [term, hL j hmem, smul_zero]
  have hindex (a : fam.relativeSimpleRoots Q) : (a : characterLattice T) ∈ Δ :=
    (ArthurTruncation.mem_simpleFinset hG hi).mp (Finset.mem_filter.mp a.2).1
  let e : out ≃ fam.relativeSimpleRoots Q :=
    { toFun := fun j => ⟨j.1.1.1, Finset.mem_filter.mpr
        ⟨(ArthurTruncation.mem_simpleFinset hG hi).mpr (hα j.1), j.2⟩⟩
      invFun := fun a => ⟨⟨⟨a.val, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots
          hG hi fam.ν (hindex a)⟩, (ArthurRelative.mem_support_base hG hi fam.generic D).mpr
          (hindex a)⟩, (Finset.mem_filter.mp a.2).2⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl))
      right_inv := fun _ => Subtype.ext rfl }
  rw [hsum', hfilter, Finset.sum_subtype (p := fun j => j ∈ out) _ (fun j => by simp) term]
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  change term j.val = fam.weightCoordinate Q v (e j) • fam.relativeCoroot Q (e j)
  unfold weightCoordinate
  rw [ArthurTruncation.coe_simpleFinset hG hi]
  rfl

/-- The projected truncation coordinates for every standard parabolic are positive on a
strictly dominant direction, including each surviving coordinate outside the Levi. -/
theorem weightCoordinate_pos_of_simple_pos {v : V T} (hv : ∀ β ∈ Δ, 0 < eval T β v)
    (α : fam.relativeSimpleRoots Q) : 0 < fam.weightCoordinate Q v α := by
  unfold weightCoordinate
  rw [ArthurTruncation.coe_simpleFinset fam.connectedReductive fam.maximalSplit]
  exact ArthurTruncation.fullWeight_pos_of_simple_pos fam.connectedReductive fam.maximalSplit
    fam.generic fam.coroots hv ((ArthurTruncation.mem_simpleFinset fam.connectedReductive
      fam.maximalSplit).mp (Finset.mem_filter.mp α.property).1)

/-- The split projection ignores Levi coroots and expands in the remaining projected coroots.
Its weight coordinates grow linearly on any dominant truncation ray. -/
def RelativeTruncationCoordinatesStatement : Prop :=
  LinearMap.ker (fam.splitDual Q) = ArthurRelative.corootSubspace fam.coroots Q.val ∧
  (∀ v ∈ fam.coroots.realCorootSpan, fam.splitDual Q v = ∑ α : fam.relativeSimpleRoots Q,
      fam.weightCoordinate Q v α • fam.relativeCoroot Q α) ∧
  ∀ v : V T, (∀ β ∈ Δ, 0 < eval T β v) → ∀ α : fam.relativeSimpleRoots Q,
  0 < fam.weightCoordinate Q v α ∧
    ∀ r : ℝ, fam.weightCoordinate Q (r • v) α = r * fam.weightCoordinate Q v α

theorem relativeTruncationCoordinates : RelativeTruncationCoordinatesStatement fam Q := by
  refine ⟨fam.ker_splitDual Q, fun _ hv => fam.splitDual_eq_sum_relativeCoroot Q hv,
    fun v hv α => ⟨fam.weightCoordinate_pos_of_simple_pos Q hv α, ?_⟩⟩
  intro r
  simp only [weightCoordinate, map_smul, smul_eq_mul]

end Langlands.Global.StandardParabolicFamily
