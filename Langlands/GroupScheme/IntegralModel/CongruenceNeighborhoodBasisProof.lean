import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisStatement
import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.RingTheory.Filtration

/-! # Neighborhood bases from the actual integral-model congruence tower -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

section Coordinates

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

private instance congruenceModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- Evaluate an original model coordinate on an original integral section. -/
def integralCoordinateAlgHom (x : M.integralSections) :
    AffineCoordinateRing R M.group.X →ₐ[R] R :=
  (affineSchemePointEquiv R M.group.X R (rationalPointEquiv R M.group.X x)).toAlgHom

private theorem reductionAt_project (n : ℕ+) (x : M.integralSections) :
    baseChangeBasePointsEquiv (congruenceBaseMap R n) M.group (M.reductionAt n x) =
      (rationalPointEquiv R M.group.X x).changeRing
        (Algebra.ofId R (congruenceRing R n)) := by
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left]
  change (baseChangeSectionHom (congruenceBaseMap R n) M.group x).left ≫
      pullback.fst M.group.X.hom (congruenceBaseMap R n) = _
  rw [baseChangeSectionHom_fst]
  change congruenceBaseMap R n ≫ x.left =
    (ringTestMap R (Algebra.ofId R (congruenceRing R n))).left ≫
      (rationalPointEquiv R M.group.X x).left
  rw [rationalPointEquiv_left]
  rfl

/-- Actual quotient reductions agree exactly when all coordinate differences
belong to the actual maximal ideal power. -/
theorem reductionAt_eq_iff_integralCoordinates (n : ℕ+) (x y : M.integralSections) :
    M.reductionAt n x = M.reductionAt n y ↔
      ∀ a : AffineCoordinateRing R M.group.X,
        M.integralCoordinateAlgHom x a - M.integralCoordinateAlgHom y a ∈
          (IsLocalRing.maximalIdeal R) ^ (n : ℕ) := by
  have h (x : M.integralSections) :
      affineSchemePointEquiv R M.group.X (congruenceRing R n)
          (baseChangeBasePointsEquiv (congruenceBaseMap R n) M.group
            (M.reductionAt n x)) =
        AlgPoint.mapCoefficients (Algebra.ofId R (congruenceRing R n))
          (affineSchemePointEquiv R M.group.X R (rationalPointEquiv R M.group.X x)) := by
    rw [reductionAt_project, affineSchemePointEquiv_changeRing]
  constructor
  · intro hxy a
    have heq := congrArg (fun z =>
      affineSchemePointEquiv R M.group.X (congruenceRing R n)
        (baseChangeBasePointsEquiv (congruenceBaseMap R n) M.group z)) hxy
    rw [h, h] at heq
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (congrArg (fun p : AlgPoint R (AffineCoordinateRing R M.group.X)
        (congruenceRing R n) => p a) heq)
  · intro hxy
    apply (baseChangeBasePointsEquiv (congruenceBaseMap R n) M.group).injective
    apply (affineSchemePointEquiv R M.group.X (congruenceRing R n)).injective
    rw [h, h]
    apply AlgPoint.ext
    intro a
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hxy a)

/-- A generating set suffices to test actual quotient reductions. -/
theorem reductionAt_eq_iff_of_adjoin_eq_top
    {s : Set (AffineCoordinateRing R M.group.X)} (hs : Algebra.adjoin R s = ⊤)
    (n : ℕ+) (x y : M.integralSections) :
    M.reductionAt n x = M.reductionAt n y ↔
      ∀ a ∈ s, M.integralCoordinateAlgHom x a - M.integralCoordinateAlgHom y a ∈
        (IsLocalRing.maximalIdeal R) ^ (n : ℕ) := by
  constructor
  · intro h a _
    exact (M.reductionAt_eq_iff_integralCoordinates n x y).mp h a
  · intro h
    have heq :
        (Algebra.ofId R (congruenceRing R n)).comp (M.integralCoordinateAlgHom x) =
        (Algebra.ofId R (congruenceRing R n)).comp (M.integralCoordinateAlgHom y) := by
      apply AlgHom.ext_of_adjoin_eq_top hs
      intro a ha
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (h a ha)
    apply (M.reductionAt_eq_iff_integralCoordinates n x y).mpr
    intro a
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (AlgHom.congr_fun heq a)

/-- All positive reductions separate the original integral sections. -/
theorem eq_of_reductionAt_eq [IsNoetherianRing R] (x y : M.integralSections)
    (hxy : ∀ n : ℕ+, M.reductionAt n x = M.reductionAt n y) : x = y := by
  apply (rationalPointEquiv R M.group.X).injective
  apply (affineSchemePointEquiv R M.group.X R).injective
  apply AlgPoint.ext
  intro a
  apply sub_eq_zero.mp
  have hm : M.integralCoordinateAlgHom x a - M.integralCoordinateAlgHom y a ∈
      ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n := by
    refine Ideal.mem_iInf.mpr fun n => ?_
    cases n with
    | zero => simp
    | succ n =>
      exact (M.reductionAt_eq_iff_integralCoordinates ⟨n + 1, Nat.succ_pos n⟩ x y).mp
        (hxy _) a
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    at hm
  exact hm

end Coordinates

section CompactBase

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [CompactSpace R]
  [IsNoetherianRing R]

local instance congruenceSectionTopology : TopologicalSpace M.integralSections :=
  rationalPointTopology R M.group.X

omit [IsLocalRing R] [IsTopologicalRing R] [T2Space R] [CompactSpace R]
  [IsNoetherianRing R] in
/-- Original coordinate evaluations are continuous on the original sections. -/
theorem continuous_integralCoordinateAlgHom_apply
    (a : AffineCoordinateRing R M.group.X) :
    Continuous fun x : M.integralSections => M.integralCoordinateAlgHom x a :=
  (AlgPoint.continuous_eval a).comp
    ((affineSchemePointHomeomorph R M.group.X R).continuous.comp
      (rationalPointHomeomorph R M.group.X).continuous)

/-- Finite generation and openness of ideal powers make every actual kernel open. -/
theorem isOpen_congruenceKernelAt (n : ℕ+) :
    IsOpen (M.congruenceKernelAt n : Set M.integralSections) := by
  obtain ⟨s, hs⟩ := (inferInstance :
    Algebra.FiniteType R (AffineCoordinateRing R M.group.X)).out
  have heq : (M.congruenceKernelAt n : Set M.integralSections) =
      ⋂ a ∈ s, (fun x => M.integralCoordinateAlgHom x a -
        M.integralCoordinateAlgHom 1 a) ⁻¹'
          (((IsLocalRing.maximalIdeal R) ^ (n : ℕ) : Ideal R) : Set R) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, mem_congruenceKernelAt]
    rw [← map_one (M.reductionAt n), M.reductionAt_eq_iff_of_adjoin_eq_top hs]
    rfl
  rw [heq]
  exact isOpen_biInter_finset fun a _ =>
    (IsLocalRing.isOpen_maximalIdeal_pow R (n : ℕ)).preimage
      ((M.continuous_integralCoordinateAlgHom_apply a).sub continuous_const)

/-- Closed coordinate conditions make every actual kernel closed. -/
theorem isClosed_congruenceKernelAt (n : ℕ+) :
    IsClosed (M.congruenceKernelAt n : Set M.integralSections) := by
  have heq : (M.congruenceKernelAt n : Set M.integralSections) =
      ⋂ a, (fun x => M.integralCoordinateAlgHom x a -
        M.integralCoordinateAlgHom 1 a) ⁻¹'
          (((IsLocalRing.maximalIdeal R) ^ (n : ℕ) : Ideal R) : Set R) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, mem_congruenceKernelAt]
    rw [← map_one (M.reductionAt n), M.reductionAt_eq_iff_integralCoordinates]
  rw [heq]
  exact isClosed_iInter fun a =>
    (IsNoetherianRing.isClosed_ideal _).preimage
      ((M.continuous_integralCoordinateAlgHom_apply a).sub continuous_const)

variable [IsAffine G.X.left] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

local instance congruenceGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology K G.X

private instance congruenceGenericT2 : T2Space (rationalPoints G) := by
  let : T2Space (RingPoint K G.X K) :=
    (affineSchemePointHomeomorph K G.X K).isEmbedding.t2Space
  exact (rationalPointHomeomorph K G.X).isEmbedding.t2Space

omit [T2Space K] in
/-- The actual generic image of every positive kernel is compact. -/
theorem isCompact_congruenceSubgroupAt (hRK : Continuous (algebraMap R K)) (n : ℕ+) :
    IsCompact (M.congruenceSubgroupAt n : Set (rationalPoints G)) := by
  let := M.compactSpace_integralSections
  exact (M.isClosed_congruenceKernelAt n).isCompact.image
    (M.continuous_integralPointMap hRK)

/-- An open integral image transports the open actual kernels into the ambient group. -/
theorem isOpen_congruenceSubgroupAt (hRK : Continuous (algebraMap R K))
    (hopen : IsOpen (M.integralPoints : Set (rationalPoints G))) (n : ℕ+) :
    IsOpen (M.congruenceSubgroupAt n : Set (rationalPoints G)) := by
  let := M.compactSpace_integralSections
  have hemb := (M.continuous_integralPointMap hRK).isClosedEmbedding
    M.integralPointMap_injective
  exact hemb.isEmbedding.isInducing.isOpenMap hopen _
    (M.isOpen_congruenceKernelAt n)

omit [T2Space K] in
/-- Compactness and separation force the actual positive tower into every
ambient identity neighborhood. -/
theorem congruenceSubgroupAt_cofinal (hRK : Continuous (algebraMap R K))
    (U : Set (rationalPoints G)) (hU : U ∈ 𝓝 (1 : rationalPoints G)) :
    ∃ n : ℕ+, (M.congruenceSubgroupAt n : Set (rationalPoints G)) ⊆ U := by
  let := M.compactSpace_integralSections
  obtain ⟨V, hVU, hV, h1V⟩ := mem_nhds_iff.mp hU
  have hc := M.continuous_integralPointMap hRK
  have hcompact : IsCompact ((M.integralPointMap ⁻¹' V)ᶜ) :=
    (hV.preimage hc).isClosed_compl.isCompact
  have hdisj : Disjoint ((M.integralPointMap ⁻¹' V)ᶜ)
      (⋂ n : ℕ+, (M.congruenceKernelAt n : Set M.integralSections)) := by
    refine Set.disjoint_left.mpr fun x hx hxi => ?_
    have heq : x = 1 := M.eq_of_reductionAt_eq x 1 fun n => by
      have hn := Set.mem_iInter.mp hxi n
      exact ((M.mem_congruenceKernelAt n x).mp hn).trans (map_one _).symm
    subst x
    exact hx (by simpa using h1V)
  have hdir : Directed (· ⊇ ·)
      (fun n : ℕ+ => (M.congruenceKernelAt n : Set M.integralSections)) := by
    intro n k
    exact ⟨max n k, M.congruenceKernelAt_antitone (le_max_left _ _),
      M.congruenceKernelAt_antitone (le_max_right _ _)⟩
  obtain ⟨n, hn⟩ := hcompact.elim_directed_family_closed _
    M.isClosed_congruenceKernelAt hdisj hdir
  refine ⟨n, ?_⟩
  rintro g ⟨x, hx, rfl⟩
  apply hVU
  by_contra hxV
  exact Set.disjoint_left.mp hn hxV hx

end CompactBase

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme.LocalFieldIntegralModel

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual integral-model congruence tower is a compact open neighborhood
basis over every nonarchimedean local field, in arbitrary universe. -/
theorem congruenceNeighborhoodBasis_proof : CongruenceNeighborhoodBasisStatement.{u} := by
  intro F _ _ _ _ G _ M
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : T2Space F := inferInstance
  refine ⟨M.isCompact_integralPoints_localField, M.isOpen_integralPoints_localField,
    ?_, ?_⟩
  · intro n
    exact ⟨M.isCompact_congruenceSubgroupAt continuous_subtype_val n,
      M.isOpen_congruenceSubgroupAt continuous_subtype_val
        M.isOpen_integralPoints_localField n, inferInstance⟩
  · exact M.congruenceSubgroupAt_cofinal continuous_subtype_val

end Langlands.GroupScheme.LocalFieldIntegralModel
