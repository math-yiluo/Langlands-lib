import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityStatement
import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing
import Langlands.Representation.Exponents.DynamicLeviNormalizer
import Langlands.Representation.Aubert.General.NormalizerRegularity
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Representation.Twist.RealPower

/-! # Regular unitary unramified twists on the literal Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance regularTwistAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance regularTwistAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance regularTwistLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [IsAffine M.X.left] in
/-- Rational points of the literal Levi image conjugated by `g`. -/
theorem rationalPoints_map_comp_innerIso (g : rationalPoints G) (x : rationalPoints M) :
    rationalPoints.map (l ≫ p ≫ (G.innerIso g).hom) x =
      g * rationalPoints.map (l ≫ p) x * g⁻¹ := by
  rw [← Category.assoc, RepresentedParabolic.pointMap_comp_apply, rationalPoints_map_innerIso]
  rfl

include pres in
omit [IsAffine M.X.left] in
/-- An abstract normalizer of the literal Levi point subgroup normalizes the
Levi as a group scheme, by the density of its rational points. -/
theorem exists_leviIso_of_mem_normalizer (g : rationalPoints G)
    (hg : g ∈ Subgroup.normalizer (parabolicLeviPointSubgroup p l : Set (rationalPoints G))) :
    ∃ φ : M ≅ M, φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom := by
  have hM := pres.isCompatible.levi.isConnectedReductive
  have := hM.smooth
  have := hM.isAffineHom
  have := hM.connectedSpace
  have : IsReduced M.X.left :=
    AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field F M.X.left M.X.hom
  have hdense : HasDenseRationalPoints F M.X := hasDenseRationalPoints_of_localField F M
  have hj : IsClosedSubgroup (l ≫ p) :=
    pres.isCompatible.levi.isClosedSubgroup.comp pres.isCompatible.parabolic.isClosedSubgroup
  have hint : IsClosedSubgroup (G.innerIso g).hom := by
    have : IsIso (G.innerIso g).hom.hom.hom :=
      (inferInstance : IsIso ((Grp.forget (Over (Spec (CommRingCat.of F)))).mapIso
        (G.innerIso g)).hom)
    have : IsIso (G.innerIso g).hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).map (G.innerIso g).hom.hom.hom))
    change IsClosedImmersion (G.innerIso g).hom.hom.hom.left
    infer_instance
  have hjg : IsClosedSubgroup (l ≫ p ≫ (G.innerIso g).hom) := by
    rw [← Category.assoc]
    exact hj.comp hint
  have h1 : SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) ≤
      SubgroupFunctor.range (l ≫ p) := by
    apply SubgroupFunctor.range_le_of_dense_rationalPoints hdense hj
    rw [← RepresentedParabolic.pointImage_eq_range_carrier,
      ← RepresentedParabolic.pointImage_eq_range_carrier]
    rintro _ ⟨x, rfl⟩
    rw [rationalPoints_map_comp_innerIso]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨x, rfl⟩
  have h2 : SubgroupFunctor.range (l ≫ p) ≤
      SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) := by
    apply SubgroupFunctor.range_le_of_dense_rationalPoints hdense hjg
    rw [← RepresentedParabolic.pointImage_eq_range_carrier,
      ← RepresentedParabolic.pointImage_eq_range_carrier]
    rintro _ ⟨x, rfl⟩
    have hx : g⁻¹ * rationalPoints.map (l ≫ p) x * g⁻¹⁻¹ ∈
        RepresentedParabolic.pointImage (l ≫ p) :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    rw [rationalPoints_map_comp_innerIso, hy]
    group
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hj
  have : IsClosedImmersion (l ≫ p ≫ (G.innerIso g).hom).hom.hom.left := hjg
  have hi : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hi' : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p ≫ (G.innerIso g).hom) :=
    ⟨Over.mono_of_mono_left _, le_antisymm h1 h2⟩
  exact ⟨SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hi' hi,
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hi' hi⟩

section Helpers

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- The twist of a representation with a central character by a character has
the product central character. -/
theorem twist_hasCentralCharacter (π : SmoothRep.{0, u, uV} ℂ H)
    (ω : Subgroup.center H →* ℂˣ) (hω : π.HasCentralCharacter ω)
    (ψ : H →* ℂˣ) (hψ : IsOpen (ψ.ker : Set H)) :
    (π.twist ψ hψ).HasCentralCharacter ((ψ.comp (Subgroup.center H).subtype) * ω) := by
  intro z v
  change (ψ z : ℂ) • π.representation z v = ((ψ z : ℂ) * (ω z : ℂ)) • v
  rw [hω z v, smul_smul]

end Helpers

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine M.X.left] in
/-- An automorphism of `M` maps central rational points to central rational points. -/
theorem rationalPoints_map_iso_mem_center (φ : M ≅ M) {x : rationalPoints M}
    (hx : x ∈ Subgroup.center (rationalPoints M)) :
    rationalPoints.map φ.hom x ∈ Subgroup.center (rationalPoints M) := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  have hy : rationalPoints.map φ.hom (rationalPoints.map φ.inv y) = y := by
    rw [← RepresentedParabolic.pointMap_comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hy, ← map_mul, ← map_mul, hx]

/-- The norm-power evaluation separates a point outside the common norm kernel
from the constants: evaluation at a point with a nontrivial rational-character
norm minus any constant is a nonzero regular function. -/
theorem unramifiedEvaluationRegular_sub_algebraMap_ne_zero
    (b : rationalPoints M) (α : rationalCharacters M)
    (hα : (rationalNormCharacters M α).toMul b ≠ 1) (κ : ℂ) :
    unramifiedEvaluationRegular (fun ψ => (rationalNormCharacters M ψ).toMul) b -
      algebraMap ℂ _ κ ≠ 0 := by
  intro h
  let ν : rationalCharacters M → (rationalPoints M →* ℝ≥0ˣ) :=
    fun ψ => (rationalNormCharacters M ψ).toMul
  let χ1 : rationalPoints M →ₜ* ℂˣ :=
    { toMonoidHom := positiveUnitsToComplex.comp (rationalNormCharacters M α).toMul
      continuous_toFun := ((isLocallyConstant_rationalNormCharacter M α).comp
        (fun y => positiveUnitsToComplex y)).continuous }
  have hχ1 : χ1 ∈ unramifiedCharacters ν := by
    intro m hm
    have hm' := (mem_commonNormKernel ν m).mp hm α
    change positiveUnitsToComplex ((rationalNormCharacters M α).toMul m) = 1
    rw [show (rationalNormCharacters M α).toMul m = 1 from hm', map_one]
  have h' := sub_eq_zero.mp h
  have e0 := congrArg (fun f : unramifiedRegularFunctions ν => f.val 1) h'
  have e1 := congrArg (fun f : unramifiedRegularFunctions ν => f.val ⟨χ1, hχ1⟩) h'
  change ((1 : ℂˣ) : ℂ) = κ at e0
  change ((positiveUnitsToComplex ((rationalNormCharacters M α).toMul b) : ℂˣ) : ℂ) = κ at e1
  rw [← e0, coe_positiveUnitsToComplex, Units.val_one] at e1
  have e2 : (((rationalNormCharacters M α).toMul b : ℝ≥0) : ℝ) = 1 := by exact_mod_cast e1
  apply hα
  apply Units.ext
  rw [Units.val_one]
  exact NNReal.coe_eq_one.mp e2

section Main

variable [NonarchimedeanGroup (rationalPoints G)]

include pres in
set_option maxHeartbeats 1600000 in
/-- A nontrivial representation of the literal Levi with a central character has
a norm-one unramified twist that is regular for the literal normalizer. -/
theorem exists_unitary_twist_isNormalizerRegular (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) [Nontrivial π]
    (ω : Subgroup.center (parabolicLeviPointSubgroup p l) →* ℂˣ)
    (hω : π.HasCentralCharacter ω) :
    ∃ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters pres),
      (∀ m, ‖(χ.val m : ℂ)‖ = 1) ∧
      IsNormalizerRegular (π.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters pres) χ)) := by
  classical
  have := hG.smooth
  have hM := pres.isCompatible.levi.isConnectedReductive
  have : LocallyOfFiniteType M.X.hom := by
    have := hM.smooth
    infer_instance
  let e := parabolicLeviPointHomeomorph pres
  let j : rationalPoints M →* rationalPoints G := rationalPoints.map (l ≫ p)
  have hpc := pres.isCompatible.parabolic.isClosedSubgroup
  let := hpc.mono
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom pres.splitComponentCocharacter ≫
      a ≫ l ≫ p)).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, pres.parabolic_eq_splitComponentCocharacter⟩
  obtain ⟨n, gs, hRnorm, hRfac⟩ :=
    pres.isCompatible.levi.exists_finite_normalizer_representatives_of_dynamicParabolic hG
      pres.isCompatible.parabolic _ hP
  choose φ hφ using hRnorm
  have hmove : ∀ t, ∃ x : rationalPoints M, x ∈ Subgroup.center (rationalPoints M) ∧
      (gs t ∉ RepresentedParabolic.pointImage (l ≫ p) → ∃ α : rationalCharacters M,
        (rationalNormCharacters M α).toMul (rationalPoints.map (φ t).hom x) ≠
          (rationalNormCharacters M α).toMul x) := by
    intro t
    by_cases ht : gs t ∈ RepresentedParabolic.pointImage (l ≫ p)
    · exact ⟨1, Subgroup.one_mem _, fun h => (h ht).elim⟩
    · by_contra hcon
      push Not at hcon
      exact ht (pres.isCompatible.levi.mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic
        hG _ hP (hφ t) fun y hy ψ => ((hcon y hy).2 ψ))
  choose x hxZ hα using hmove
  let ν : rationalCharacters M → (rationalPoints M →* ℝ≥0ˣ) :=
    fun ψ => (rationalNormCharacters M ψ).toMul
  have hem (m : rationalPoints M) (hm : m ∈ Subgroup.center (rationalPoints M)) :
      e m ∈ Subgroup.center (parabolicLeviPointSubgroup p l) := by
    rw [← Subgroup.map_center_eq e.toMulEquiv]
    exact Subgroup.mem_map_of_mem _ hm
  let ex : Fin n → Subgroup.center (parabolicLeviPointSubgroup p l) :=
    fun t => ⟨e (x t), hem _ (hxZ t)⟩
  let ey : Fin n → Subgroup.center (parabolicLeviPointSubgroup p l) :=
    fun t => ⟨e (rationalPoints.map (φ t).hom (x t)),
      hem _ (rationalPoints_map_iso_mem_center (φ t) (hxZ t))⟩
  let κ : Fin n → ℂˣ := fun t => ω (ex t) * (ω (ey t))⁻¹
  let b : Fin n → rationalPoints M := fun t => rationalPoints.map (φ t).hom (x t) * (x t)⁻¹
  let f : Fin n → unramifiedRegularFunctions ν :=
    fun t => unramifiedEvaluationRegular ν (b t) - algebraMap ℂ _ (κ t : ℂ)
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun t => gs t ∉ RepresentedParabolic.pointImage (l ≫ p))
  have hf : ∀ t ∈ s, f t ≠ 0 := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    obtain ⟨α, hα'⟩ := hα t ht'
    apply unramifiedEvaluationRegular_sub_algebraMap_ne_zero (b t) α
    intro h1
    apply hα'
    have h2 : ν α (b t) = 1 := h1
    simp only [b, map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  obtain ⟨χu, hχu⟩ := rationalUnramifiedRegular_exists_unitary_finset_ne_zero M hM s f hf
  let χ0 : unramifiedCharacters ν := ⟨χu.val, χu.property.1⟩
  let ψ := parabolicLeviUnramifiedCharactersHomeomorph pres χ0
  refine ⟨ψ, fun m => χu.property.2 (e.symm m), ?_⟩
  let ψ0 := ψ.val.toMonoidHom
  have hψ0 := unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters pres) ψ
  have : Nontrivial (π.twist ψ0 hψ0) := inferInstanceAs (Nontrivial π)
  apply isNormalizerRegular_of_centralCharacter _ _ (twist_hasCentralCharacter π ω hω ψ0 hψ0)
  intro ng hng heq
  obtain ⟨φg, hφg⟩ := exists_leviIso_of_mem_normalizer pres ng.1 ng.2
  obtain ⟨t, mm, hfac⟩ := hRfac ng.1 φg hφg
  have ht : gs t ∉ RepresentedParabolic.pointImage (l ≫ p) := by
    intro h
    apply hng
    change (ng : rationalPoints G) ∈ RepresentedParabolic.pointImage (l ≫ p)
    rw [hfac]
    exact Subgroup.mul_mem _ h ⟨mm, rfl⟩
  have hts : t ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  apply hχu t hts
  have h1 : j (rationalPoints.map (φ t).hom (x t)) = gs t * j (x t) * (gs t)⁻¹ := by
    have h := congrArg (fun q => rationalPoints.map q (x t)) (hφ t)
    rw [RepresentedParabolic.pointMap_comp_apply (φ t).hom (l ≫ p)] at h
    rw [show j (rationalPoints.map (φ t).hom (x t)) =
        rationalPoints.map (l ≫ p) (rationalPoints.map (φ t).hom (x t)) from rfl, h,
      rationalPoints_map_comp_innerIso]
  have h2 : j (x t) * j mm = j mm * j (x t) := by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hxZ t) mm]
  have hconj : (ng : rationalPoints G)⁻¹ * j (rationalPoints.map (φ t).hom (x t)) * ng =
      j (x t) := by
    rw [h1, hfac]
    calc (gs t * j mm)⁻¹ * (gs t * j (x t) * (gs t)⁻¹) * (gs t * j mm)
        = (j mm)⁻¹ * (j (x t) * j mm) := by group
      _ = j (x t) := by rw [h2]; group
  have hcc : Subgroup.centerCongr (normalizerConjugation ng).toMulEquiv (ey t) = ex t := by
    apply Subtype.ext
    apply Subtype.ext
    exact hconj
  have hval := congrArg (fun c : Subgroup.center (parabolicLeviPointSubgroup p l) →* ℂˣ =>
    c (ey t)) heq
  change ((ψ0.comp (Subgroup.center _).subtype) * ω)
      (Subgroup.centerCongr (normalizerConjugation ng).toMulEquiv (ey t)) =
    ((ψ0.comp (Subgroup.center _).subtype) * ω) (ey t) at hval
  rw [hcc] at hval
  have hψe (m : rationalPoints M) : ψ0 (e m) = χu.val m := by
    change χu.val (e.symm (e m)) = χu.val m
    rw [e.symm_apply_apply]
  have key : χu.val (b t) = κ t := by
    have hb : χu.val (b t) = ψ0 (e (rationalPoints.map (φ t).hom (x t))) *
        (ψ0 (e (x t)))⁻¹ := by
      rw [hψe, hψe]
      exact map_mul_inv χu.val _ _
    rw [hb]
    change ψ0 (e (x t)) * ω (ex t) = ψ0 (e (rationalPoints.map (φ t).hom (x t))) * ω (ey t)
      at hval
    change _ = ω (ex t) * (ω (ey t))⁻¹
    rw [mul_inv_eq_iff_eq_mul, mul_comm, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact hval.symm
  change (χu.val (b t) : ℂ) - (κ t : ℂ) = 0
  rw [key, sub_self]

end Main

/-- In the structural context of `ConditionalParabolicGenericIrreducibilityStatement`,
every nontrivial smooth representation of the literal Levi with a central
character has a norm-one unramified twist, for the full rational-norm family,
that is regular for the literal normalizer of the Levi in `G(F)`. -/
def RegularUnitaryTwistExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [NonarchimedeanGroup (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a)
      (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) [Nontrivial π]
      (ω : Subgroup.center (parabolicLeviPointSubgroup p l) →* ℂˣ),
      π.HasCentralCharacter ω →
        ∃ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r),
          (∀ m, ‖(χ.val m : ℂ)‖ = 1) ∧
          IsNormalizerRegular (π.twist χ.val.toMonoidHom
            (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ))

/-- The existence of regular unitary twists holds. -/
theorem regularUnitaryTwistExistence : RegularUnitaryTwistExistenceStatement.{u, uV} := by
  intro F _ _ _ _ G hG _ A M P _ p l a r π _ ω hω
  have := hG.isAffineHom
  exact exists_unitary_twist_isNormalizerRegular r hG π ω hω

end Langlands.Plancherel
