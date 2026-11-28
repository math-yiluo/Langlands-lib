import Langlands.Automorphic.GroupSchemeArchimedeanHarishChandraFiniteness
import Langlands.Automorphic.GroupSchemeFixedProfileConstantTerm
import Langlands.Automorphic.GroupSchemeFixedProfileCuspidalFiniteness
import Langlands.Automorphic.GroupSchemeHarishChandraParabolicReduction
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeStandardConstantTermCuspidality
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicIwasawaWithInfiniteCompact
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration
import Langlands.GroupScheme.Torus.NormalSubgroupMaximalProof
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Harish-Chandra finiteness on the rational adelic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme Langlands.Global Langlands.CompactIwasawa AdelicGroupPoints
  InfiniteAdelicGroupPoints

section FixedProfile

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local notation "V" => FinitePlotSmoothRationalFunctions F G
local notation "A" => AdelicGroupPoints F G

private local instance : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ

private theorem isInfiniteSubgroupFiniteFunction_of_profiles
    (H : Subgroup (InfiniteAdelicGroupPoints F G)) (E : Submodule ℂ (H → ℂ))
    [FiniteDimensional ℂ E] (f : A → ℂ)
    (hf : ∀ g, (fun k : H => f (g * ofInfinite F G k.val)) ∈ E) :
    IsInfiniteSubgroupFiniteFunction F G H f := by
  let T : Module.Dual ℂ E →ₗ[ℂ] (A → ℂ) :=
    { toFun := fun z g => z ⟨_, hf g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact ⟨(LinearMap.proj k).comp E.subtype, rfl⟩

private def fixedProfileRationalSpace {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (H : Subgroup (InfiniteAdelicGroupPoints F G))
    (J : Ideal (AdelicEnvelopingCenter F G hsmooth)) (E : Submodule ℂ (H → ℂ)) : Submodule ℂ V where
  carrier := {f | f.val ∈ levelSubmodule F G L.toSubgroup ∧
    (∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0) ∧
    (∀ g : A, (fun k : H => evaluate F G f.val (g * ofInfinite F G k.val)) ∈ E) ∧
    HasHeightGrowth rho (evaluate F G f.val)}
  zero_mem' := ⟨(levelSubmodule F G L.toSubgroup).zero_mem, fun _ _ => map_zero _,
    fun _ => E.zero_mem, HasHeightGrowth.zero⟩
  add_mem' {f h} hf hh := by
    refine ⟨(levelSubmodule F G L.toSubgroup).add_mem hf.1 hh.1, ?_, ?_, hf.2.2.2.add hN hh.2.2.2⟩
    · intro z hz
      change adelicCenterAction F G hsmooth hcalc z (f + h) = 0
      rw [map_add, hf.2.1 z hz, hh.2.1 z hz, add_zero]
    · exact fun g => E.add_mem (hf.2.2.1 g) (hh.2.2.1 g)
  smul_mem' c f hf := by
    refine ⟨(levelSubmodule F G L.toSubgroup).smul_mem c hf.1, ?_, ?_, hf.2.2.2.smul c⟩
    · intro z hz
      change adelicCenterAction F G hsmooth hcalc z (c • f) = 0
      rw [map_smul, hf.2.1 z hz, smul_zero]
    · exact fun g => E.smul_mem c (hf.2.2.1 g)

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

omit [NumberField F] in
private theorem standardLevi_dimension_lt (fam : StandardParabolicFamily F G)
    (I : StandardIndex F G fam.i fam.ν) (hI : I ≠ fam.top) :
    haveI := (fam.isCompatible I).levi.isConnectedReductive.isAffineHom
    Lie.dimension (fam.M I) < Lie.dimension G := by
  let hl := (fam.isCompatible I).levi
  let : IsAffineHom (fam.M I).X.hom := hl.isConnectedReductive.isAffineHom
  let : Smooth (fam.M I).X.hom := hl.isConnectedReductive.smooth
  apply Lie.dimension_lt_of_proper_closedSubgroup (fam.l I ≫ fam.p I)
    (hl.isClosedSubgroup.comp (fam.isCompatible I).parabolic.isClosedSubgroup)
  intro hIso
  let := hIso
  have hRange := SubgroupFunctor.range_comp_le (fam.l I) (fam.p I)
  rw [LeviGluing.range_eq_top_of_isIso] at hRange
  apply hI
  apply le_antisymm (fam.le_top I)
  apply (fam.le_iff_range_le fam.top I).mpr
  rw [standardParabolicFamily_range_top fam]
  exact hRange

set_option maxHeartbeats 1600000 in
private theorem finite_fixedProfileRationalSpace
    (hG : IsConnectedReductive G) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (H : Subgroup (InfiniteAdelicGroupPoints F G))
    (hH : IsMaximalCompact H) (J : Ideal (AdelicEnvelopingCenter F G hsmooth))
    (hJ : Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ))
    (E : Submodule ℂ (H → ℂ)) (hE : FiniteDimensional ℂ E)
    (hCenter : ParabolicLeviCenterRestrictionStatement.{u})
    (hLevi : ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M),
      haveI := hM.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      Lie.dimension M < Lie.dimension G → RationalHarishChandraFinitenessFor F M) :
    Module.Finite ℂ (fixedProfileRationalSpace rho hN hsmooth hcalc L H J E) := by
  classical
  obtain ⟨T, i, ν, hi, hν⟩ :=
    Langlands.Aubert.General.RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  let W := fixedProfileRationalSpace rho hN hsmooth hcalc L H J E
  let I₀ := StandardIndex F G fam.i fam.ν
  let Iproper := {I : I₀ // I ≠ fam.top}
  let : Fintype I₀ := ((fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots
    fam.i fam.ν).finite_subsets).fintype
  let : Finite Iproper := Finite.of_injective Subtype.val Subtype.val_injective
  let : FiniteDimensional ℂ E := hE
  have hGrowth (f : W) : HasModerateGrowthFunction F G rho (evaluate F G f.val.val) :=
    (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr f.property.2.2.2
  let CT (I : Iproper) : W →ₗ[ℂ] (A → ℂ) :=
    (parabolicConstantTermLinear (fam.p I.val) (fam.iU I.val) (fam.isUnipotentRadical I.val)).comp W.subtype
  have finiteConstantTerm (I : Iproper) : Module.Finite ℂ (LinearMap.range (CT I)) := by
    let I' := I.val
    let hp := (fam.isCompatible I').parabolic
    let hl := (fam.isCompatible I').levi
    let hu := fam.isUnipotentRadical I'
    let r : ParabolicRootPresentation (fam.p I') (fam.l I') (fam.a I') :=
      ⟨_, fam.isCompatible I'⟩
    have hmul : IsIso (subgroupMultiplication (fam.l I') (fam.iU I')) :=
      r.isIso_subgroupMultiplication_of_radical hu
    let : IsClosedImmersion (fam.p I').hom.hom.left := hp.isClosedSubgroup
    obtain ⟨K, hK, hKinfinite⟩ := iwasawaWithInfiniteCompact F G (fam.P I') (fam.p I') hG hp H hH
    subst H
    have hAt : RationalHarishChandraFinitenessFor F (fam.M I') :=
      hLevi _ hl.isConnectedReductive (standardLevi_dimension_lt fam I' I.property)
    have hCT := parabolicHarishChandraFiniteness_of_rational_at_levi hCenter F G
      (fam.P I') (fam.M I') (fam.U I') (fam.p I') (fam.iU I') (fam.l I') hG hp hu hl hmul hAt
      K hK.1 hK.isIwasawaCompact rho hsmooth hcalc hρ J hJ L.toSubgroup L.isOpen E hE
    rw [← Submodule.span_eq (LinearMap.range (CT I))]
    refine @Submodule.finiteDimensional_of_le ℂ (A → ℂ) _ _ _ _ _ hCT ?_
    apply Submodule.span_mono
    rintro _ ⟨f, rfl⟩
    obtain ⟨hinv, hsm, hgrow, hfix, hann, hprof⟩ :=
      parabolicConstantTermLinear_fixedProfile (fam.p I') (fam.iU I') hu
        (fam.l I') rho hN hsmooth hcalc L _ J E f.val (hGrowth f)
        f.property.1 f.property.2.1 f.property.2.2.1
    exact ⟨⟨hinv, hsm, isInfiniteSubgroupFiniteFunction_of_profiles _ E _ hprof,
      ⟨J, hJ, hann⟩, hgrow⟩, hfix, hann, hprof⟩
  let : ∀ I : Iproper, Module.Finite ℂ (LinearMap.range (CT I)) := finiteConstantTerm
  let : FiniteDimensional ℂ (∀ I : Iproper, LinearMap.range (CT I)) :=
    FiniteDimensional.finiteDimensional_pi' ℂ (fun I => ↥(LinearMap.range (CT I)))
  let C : W →ₗ[ℂ] (∀ I : Iproper, LinearMap.range (CT I)) :=
    LinearMap.pi fun I => (CT I).rangeRestrict
  let W₀ := (LinearMap.ker C).map W.subtype
  have hW₀ : W₀ ≤ W := by
    rintro _ ⟨f, _, rfl⟩
    exact f.property
  have hCusp (f : V) (hf : f ∈ W₀) : ArthurTruncation.HasCuspidalConstantTerms (evaluate F G f.val) := by
    obtain ⟨w, hw, rfl⟩ := hf
    have he := LinearMap.mem_ker.mp hw
    apply hasCuspidalConstantTerms_of_standard F G fam w.val.val
    intro I hI
    let j : Iproper := ⟨I, hI⟩
    have h := congrArg (fun v : ∀ I : Iproper, LinearMap.range (CT I) => (v j).val) he
    change CT j w = 0 at h
    exact (funext (parabolicConstantTermLinear_apply (fam.p I) (fam.iU I)
      (fam.isUnipotentRadical I) w.val)).symm.trans h
  let : Module.Finite ℂ W₀ := fixedProfileCuspidalFiniteness F G rho hN hρ hG
    hsmooth hcalc L H hH J hJ E hE W₀
    (fun _ hf => (hW₀ hf).1) (fun _ hf => (hW₀ hf).2.1)
    (fun f hf b a => by
      have h := (hW₀ hf).2.2.1 (pair F G a b)
      convert h using 1
      ext k
      change (finitePlotSmoothSlice F G b f).val (a * k.val) = _
      rw [finitePlotSmoothSlice_apply, ofInfinite_eq_pair, pair_mul, mul_one])
    (fun f hf => hGrowth ⟨f, hW₀ hf⟩) hCusp
  let : Module.Finite ℂ (LinearMap.ker C) :=
    Module.Finite.equiv (Submodule.equivMapOfInjective W.subtype W.injective_subtype _).symm
  let : Module.Finite ℂ (LinearMap.range C) :=
    FiniteDimensional.finiteDimensional_submodule (LinearMap.range C)
  let : Module.Finite ℂ (W ⧸ LinearMap.ker C) := Module.Finite.equiv C.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker C)

set_option maxHeartbeats 1000000 in
private theorem rationalAt_of_properLevis
    (hG : IsConnectedReductive G) (hCenter : ParabolicLeviCenterRestrictionStatement.{u})
    (hLevi : ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M),
      haveI := hM.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      Lie.dimension M < Lie.dimension G → RationalHarishChandraFinitenessFor F M) :
    RationalHarishChandraFinitenessFor F G := by
  intro _ N d rho hρ hsmooth hcalc L H hH J hJ E hE
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · let : IsClosedImmersion rho.hom.hom.left := hρ
    let : Mono rho.hom.hom := Over.mono_of_mono_left _
    let : Subsingleton A :=
      ⟨fun x y => rho.pointMatrix_injective _ (Subsingleton.elim _ _)⟩
    let : Finite A := Finite.of_injective (fun _ => ()) (fun _ _ _ => Subsingleton.elim _ _)
    infer_instance
  · let W := fixedProfileRationalSpace rho hN hsmooth hcalc L H J E
    let : Module.Finite ℂ W :=
      finite_fixedProfileRationalSpace hG rho hN hρ hsmooth hcalc L H hH J hJ E hE hCenter hLevi
    let ev := finitePlotSmoothEvaluation F G
    let : Module.Finite ℂ (W.map ev) := Module.Finite.map _ _
    apply Submodule.finiteDimensional_of_le (S₂ := W.map ev)
    apply Submodule.span_le.mpr
    intro f hf
    rcases hf with ⟨hinv, hsm, hgrow, hlevel, hann, hprof⟩
    let v := ofRationalSmoothFunction F G f hinv hsm
    refine Submodule.mem_map.mpr ⟨v, ?_, rfl⟩
    refine ⟨?_, ?_, hprof, (hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hgrow⟩
    · intro l
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact hlevel l.val l.property g
    · intro z hz
      apply finitePlotSmoothSlice_injective F G
      funext b
      change finitePlotSmoothSlice F G b (finitePlotSmoothCenterAction F G hsmooth hcalc z v) =
        finitePlotSmoothSlice F G b 0
      rw [finitePlotSmoothSlice_centerAction, map_zero]
      exact hann z hz b (hsm.2.1 b)

end FixedProfile

/-- Finite restriction of the actual enveloping center to proper Levis suffices
for Harish-Chandra finiteness on the rational adelic quotient. -/
theorem rationalHarishChandraFiniteness_of_leviCenterRestriction
    (hCenter : ParabolicLeviCenterRestrictionStatement.{u}) :
    RationalHarishChandraFinitenessStatement.{u} := by
  intro F _ _ G _ hG
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let motive (B : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
    ∀ hB : IsConnectedReductive B,
      haveI := hB.isAffineHom
      haveI : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
      RationalHarishChandraFinitenessFor F B
  have h : motive G := by
    refine smoothConnectedAffineGroup_lieDimension_induction motive ?_ G
    intro B _ _ _ ih hB
    let : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
    apply rationalAt_of_properLevis hB hCenter
    intro M hM
    let : Smooth M.X.hom := hM.smooth
    let : IsAffineHom M.X.hom := hM.isAffineHom
    let : ConnectedSpace M.X.left := hM.connectedSpace
    intro hLt
    exact ih M hLt hM
  exact @h hG hG

end Langlands.Automorphic.GroupSchemeFunctions
