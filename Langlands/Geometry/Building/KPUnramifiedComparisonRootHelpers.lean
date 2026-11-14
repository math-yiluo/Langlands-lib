import Langlands.Geometry.Building.KPUnramifiedApartmentLift
import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Root-filtration calculations for a concrete unramified apartment lift -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance comparisonRootHelpersAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "fK" =>
  CategoryTheory.Functor.map
    (CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))) t.f
local notation "aK" a =>
  characterLattice.baseChange (algebraBaseMap F (UnramifiedClosure F)) P.S a

/-- Upper roots restricting to positive integral multiples of the lower
character. -/
def rootFiber (a : characterLattice P.S) : Set (characterLattice L.buildingData.S) :=
  relativeRoots t.upstairsInclusion ∩
    (RelativeRoot.characterSemigroupPreimage fK (RelativeRoot.cyclicTail (aK a) 1) :
      Set (characterLattice t.upstairsTorus))

set_option maxHeartbeats 1000000 in
/-- The positive restriction fibre is closed under positive root combinations. -/
theorem rootFiber_closed (a : characterLattice P.S) :
    L.buildingData.IsClosedRootSet (L.rootFiber a) := by
  refine ⟨fun _ hb => hb.1, ?_⟩
  intro b hb c hc p q hp hq hroot
  obtain ⟨m, _, hm, hbEq⟩ := hb.2
  obtain ⟨n, _, hn, hcEq⟩ := hc.2
  have hpm : 0 < p * m := Nat.mul_pos hp hm
  change m • (aK a) = fK ≫ b at hbEq
  change n • (aK a) = fK ≫ c at hcEq
  refine ⟨hroot, p * m + q * n, by omega, by positivity, ?_⟩
  change _ = (characterLattice.comapHom (CommGroupScheme.groupHom fK))
    (p • b + q • c)
  rw [map_add, map_nsmul, map_nsmul]
  change _ = p • (fK ≫ b) + q • (fK ≫ c)
  rw [← hbEq, ← hcEq, smul_smul, smul_smul, add_smul]

/-- Evaluation on a transported lower vector scales by the restriction
multiplier on each root in the fibre. -/
theorem eval_rootFiber (a : characterLattice P.S) (v : V P.S)
    {b : characterLattice L.buildingData.S} (hb : b ∈ L.rootFiber a) :
    ∃ m : ℕ, 0 < m ∧
      eval L.buildingData.S b
          (descentCocharacterMap F (UnramifiedClosure F) t.f
            P.isMaximalSplitTorus.isSplitSubtorus.1 v) =
        m * eval P.S a v := by
  obtain ⟨m, _, hm, heq⟩ := hb.2
  change m • (aK a) = fK ≫ b at heq
  refine ⟨m, hm, ?_⟩
  rw [eval_descentCocharacterMap, ← heq, eval_nsmul_char,
    eval_splitCocharacterBaseChange]

/-- A lower vector positive on the root is positive on its entire upper fibre. -/
theorem rootFiber_pos (a : characterLattice P.S) (v : V P.S)
    (hv : 0 < eval P.S a v) :
    ∀ b ∈ L.rootFiber a,
      0 < eval L.buildingData.S b
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 v) := by
  intro b hb
  obtain ⟨m, hm, heq⟩ := L.eval_rootFiber a v hb
  rw [heq]
  exact mul_pos (by exact_mod_cast hm) hv

/-- The opposite lower fibre lies in the negative half-space of the same vector. -/
theorem neg_rootFiber_subset_negativePairingRoots (a : characterLattice P.S) (v : V P.S)
    (hv : 0 < eval P.S a v) :
    L.rootFiber (-a) ⊆ L.buildingData.negativePairingRoots
      (descentCocharacterMap F (UnramifiedClosure F) t.f
        P.isMaximalSplitTorus.isSplitSubtorus.1 v) := by
  intro b hb
  refine ⟨hb.1, ?_⟩
  obtain ⟨m, hm, heq⟩ := L.eval_rootFiber (-a) v hb
  rw [heq, eval_neg_char]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hm) (neg_neg_of_pos hv)

/-- The actual special-torus factorization after scalar extension. -/
theorem fieldFactorization :
    CommGroupScheme.groupHom fK ≫ t.upstairsInclusion =
      (GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map P.i := by
  rw [← t.factor, Functor.map_comp]
  rfl

/-- The downstairs root filtration is the exact preimage of the upper root
filtrations at the intrinsic positive integral restriction multipliers. -/
theorem filtration_eq_restrictedDepth (y : P.Apartment) (a : relativeRoots P.i)
    (r : ℝ) :
    P.filtration y a r =
      (torusRestrictedRootDepthSubgroup
        (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map t.f)
        (characterLattice.baseChange (algebraBaseMap F (UnramifiedClosure F)) P.S a) r).comap
          (rationalExtend F (UnramifiedClosure F) G) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  apply SetLike.coe_injective
  change rootFiltration P.i y.val a r = _
  rw [L.restrict y]
  exact rootFiltration_torusFieldRestrictedRootFunctionFamily P.i
    P.isMaximalSplitTorus.isSplitSubtorus.1 t.isMaximalSplitTorus.isSplitSubtorus.1
    L.oppositeFactorPairs (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
    _ (fieldFactorization (t := t)) a a.2 r

set_option maxHeartbeats 1000000 in
/-- Extension sends the entire lower root group into the upper positive
restriction fibre. -/
theorem root_mem_rootFiber (a : relativeRoots P.i) (g : rationalPoints G)
    (hg : g ∈ P.rootGroup a) :
    rationalExtend F (UnramifiedClosure F) G g ∈
      L.buildingData.rootGroupSpan (L.rootFiber a) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hS := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hT := t.isMaximalSplitTorus.isSplitSubtorus.1
  have hroot := rationalExtend_mem_rootGroupPoints (K := UnramifiedClosure F) P.i a hg
  rw [← fieldFactorization (t := t)] at hroot
  change rationalExtend F (UnramifiedClosure F) G g ∈
    (RelativeRoot.subgroup (CommGroupScheme.groupHom fK ≫ t.upstairsInclusion)
      (aK a)).carrier (Over.mk (𝟙 _)) at hroot
  have haK : (aK a) ≠ 0 :=
    ((mem_roots_baseChange_iff (K := UnramifiedClosure F) G P.S hS P.i a).mpr a.2).1
  rw [RelativeRoot.subgroup_comp_torusHom_carrier_eq_iSup
    (hS.baseChange (algebraBaseMap F (UnramifiedClosure F))) hT fK t.upstairsInclusion
      L.oppositeFactorPairs (aK a) haK] at hroot
  exact (show (⨆ b : {b : characterLattice t.upstairsTorus |
      b ∈ relativeRoots t.upstairsInclusion ∧
        fK ≫ b ∈ RelativeRoot.cyclicTail (aK a) 1},
      (RelativeRoot.subgroup t.upstairsInclusion b.val).carrier (Over.mk (𝟙 _))) ≤
      L.buildingData.rootGroupSpan (L.rootFiber a) from
    iSup_le fun b => le_iSup_of_le b.val (le_iSup_of_le b.property le_rfl)) hroot

set_option maxHeartbeats 1000000 in
/-- Extension sends the opposite lower root group into the negative half-space
of any transported lower vector positive on the chosen root. -/
theorem neg_mem_negativePairingRoots (a : relativeRoots P.i) (v : V P.S)
    (hv : 0 < eval P.S a v) (g : rationalPoints G)
    (hg : g ∈ P.rootGroup (-a.val)) :
    rationalExtend F (UnramifiedClosure F) G g ∈
      L.buildingData.rootGroupSpan (L.buildingData.negativePairingRoots
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 v)) := by
  have hneg : -a.val ∈ relativeRoots P.i :=
    relativeRootNegation F G P.isConnectedReductive P.S P.i
      P.isMaximalSplitTorus a a.property
  have hmem := L.root_mem_rootFiber ⟨-a.val, hneg⟩ g hg
  have hle : L.buildingData.rootGroupSpan (L.rootFiber (-a.val)) ≤
      L.buildingData.rootGroupSpan (L.buildingData.negativePairingRoots
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 v)) :=
    iSup_le fun b => iSup_le fun hb => le_iSup_of_le b
      (le_iSup_of_le (L.neg_rootFiber_subset_negativePairingRoots a v hv hb) le_rfl)
  exact hle hmem

/-- A lower root admits a real cocharacter positive on it. -/
theorem exists_root_positive_vector (a : relativeRoots P.i) :
    ∃ v : V P.S, 0 < eval P.S a v := by
  obtain ⟨d, hd, ζ, hζ⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_pairing_eq_pos a.property.1
  refine ⟨(1 : ℝ) ⊗ₜ[ℤ] ζ, ?_⟩
  rw [eval_tmul, one_mul, hζ]
  exact_mod_cast hd

set_option maxHeartbeats 1000000 in
/-- Nonnegative lower depth is contained in the same, unscaled upper depth
span: every positive multiplier makes the upper generator at least as deep. -/
theorem filtration_mem_rootFiber (y : P.Apartment) (a : relativeRoots P.i)
    (s : ℝ≥0) (g : rationalPoints G) (hg : g ∈ P.filtration y a s) :
    rationalExtend F (UnramifiedClosure F) G g ∈
      L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) s := by
  rw [L.filtration_eq_restrictedDepth y a s] at hg
  have hle : torusRestrictedRootDepthSubgroup
      (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) fK (aK a) s ≤
      L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) s := by
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    have hms : (s : ℝ) ≤ (m : ℝ) * s := by
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [s.coe_nonneg]
    have hbF : b ∈ L.rootFiber a := ⟨hb, m, by omega, hm, heq.symm⟩
    exact le_iSup_of_le b (le_iSup_of_le hbF
      (L.apartment.filtration_antitone (L.e y) b hms))
  exact hle (Subgroup.mem_comap.mp hg)

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
