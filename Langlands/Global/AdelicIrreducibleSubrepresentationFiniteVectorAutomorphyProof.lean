import Langlands.Global.AdelicIrreducibleSubrepresentationFormReduction
import Langlands.Global.AdelicHilbertReproduction
import Langlands.Global.AdelicQuotientConvolutionEnveloping
import Langlands.Global.AdelicQuotientConvolutionGrowth
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule
import Langlands.Representation.Archimedean.HilbertSubmoduleAction

/-! # Automorphy of the finite vectors in an irreducible subrepresentation of `L²([G])` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Manifold ContDiff InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Archimedean
open AdelicGroupPoints InfiniteAdelicGroupPoints RestrictionSplitCentre PositiveRealTorus

private theorem irreducible_invariantSubmodule {A H : Type*} [Group A] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (R : A →* (H →L[ℂ] H)) (V : Submodule ℂ H)
    (hV : Langlands.Analysis.IsIrreducibleSubrepresentation
      (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R) V) :
    IsTopologicallyIrreducible (invariantSubmoduleRepresentation R V (fun g v => hV.2.2.1 g v v.property)) := by
  obtain ⟨hVc, hVne, hVi, hVmin⟩ := hV
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff V).mp hVne
  refine ⟨⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩, fun W hW hWi => ?_⟩
  have hWc : IsClosed ((W.map V.subtype : Submodule ℂ H) : Set H) :=
    hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hW
  have hle : W.map V.subtype ≤ V := by
    rintro _ ⟨u, _, rfl⟩
    exact u.property
  have hinv (g : A) : ∀ u ∈ W.map V.subtype, R g u ∈ W.map V.subtype := by
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.mem_map_of_mem (hWi g u hu)
  rcases hVmin _ hle hWc hinv with hz | ht
  · left
    apply Submodule.map_injective_of_injective V.subtype_injective
    rw [hz, Submodule.map_bot]
  · right
    apply Submodule.map_injective_of_injective V.subtype_injective
    rw [ht, Submodule.map_top, Submodule.range_subtype]

section CompactFiniteness

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (J : Type) [Fintype J] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "A" => AdelicGroupPoints F G
local notation "Rfull" => haarQuotientL2BoundedRightAction F G T i hi J e hc

include hi J e hc in
private theorem finite_representative_of_finite_class (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (w : Lp ℂ 2 dq) (φ : A → ℂ) (hφc : Continuous φ) (hφi : IsLeftInvariantUnder F G Γ φ)
    (hrep : (w : Q → ℂ) =ᵐ[dq] fun q => φ q.out)
    (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => Rfull (ofInfinite F G k.val) w))) :
    IsInfiniteSubgroupFiniteFunction F G K φ := by
  let f : C(Q, ℂ) := ⟨LeftCosetSpace.lift Γ φ (fun r => hφi r r.property), hφc.quotient_lift _⟩
  have hfun (q : Q) : f q = φ q.out := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hfae : (w : Q → ℂ) =ᵐ[dq] f := hrep.trans (ae_of_all _ fun q => (hfun q).symm)
  let v : continuousL2Submodule F G T i dq := ⟨f, (Lp.memLp w).ae_eq hfae⟩
  let j := continuousL2ToLp F G T i dq
  have hj : Function.Injective j := haarContinuousL2ToLp_injective F G T i hi J e hc
  have hjv : j v = w := Lp.ext ((coeFn_continuousL2ToLp F G T i dq v).trans hfae.symm)
  let R := continuousL2RightAction F G T i dq (haarQuotientMeasureRightInvariant F G T i hi J e hc)
  let W : Submodule ℂ (continuousL2Submodule F G T i dq) :=
    Submodule.span ℂ (Set.range fun k : K => R (ofInfinite F G k.val) v)
  have himage : W.map j = Submodule.span ℂ (Set.range fun k : K => Rfull (ofInfinite F G k.val) w) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span ℂ)
    apply congrArg Set.range
    funext k
    change continuousL2ToLp F G T i dq (R (ofInfinite F G k.val) v) = _
    rw [continuousL2ToLp_rightAction, hjv]
    rfl
  letI : FiniteDimensional ℂ (W.map j) := himage.symm ▸ hK
  letI : Module.Finite ℂ ↥W := Module.Finite.equiv (Submodule.equivMapOfInjective j hj W).symm
  let ev : continuousL2Submodule F G T i dq →ₗ[ℂ] (A → ℂ) :=
    { toFun := fun f x => f.val (LeftCosetSpace.mk Γ x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : W.map ev = Submodule.span ℂ (Set.range fun k : K => fun g : A => φ (g * ofInfinite F G k.val)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span ℂ)
    apply congrArg Set.range
    funext k g
    change f (LeftCosetSpace.rightTranslate Γ (ofInfinite F G k.val) (LeftCosetSpace.mk Γ g)) = _
    rw [LeftCosetSpace.rightTranslate_mk]
    rfl
  unfold IsInfiniteSubgroupFiniteFunction
  rw [← he]
  exact Module.Finite.map W ev

end CompactFiniteness

/-- The finite vectors of an irreducible subrepresentation of `L²([G])` have representatives
that are automorphic in the smoothness and common-level convention of `IsAutomorphicFunctionOn`. -/
theorem irreducibleSubrepresentationFiniteVectorAutomorphy :
    IrreducibleSubrepresentationFiniteVectorAutomorphyStatement := by
  classical
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hK hrho V hV w hw hwfin
  letI := fun p : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F p
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  let I := 𝓘(ℝ, smoothModel F d)
  let M := InfiniteAdelicGroupPoints F G
  letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  let A := AdelicGroupPoints F G
  let B := FiniteAdelicGroupPoints F G
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  by_cases hw0 : w = 0
  · subst w
    refine ⟨0, (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth hcalc).zero_mem,
      fun _ _ _ => rfl, Lp.coeFn_zero _ _ _⟩
  obtain ⟨n, rho', hn, hrho', hpos⟩ := exists_positiveMatrixEmbedding_of_isClosedSubgroup rho hrho hsmooth hcalc
  let T := canonicalTorus F G
  let i := canonicalComponent F G
  have hs : IsSplitComponent i := isSplitComponent_canonicalComponent F G
  obtain ⟨J, hJ, ⟨e⟩⟩ := hs.1.1.1
  letI : Fintype J := Fintype.ofFinite J
  letI := canonical_finiteIndex F G hG
  letI := normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  let hi := canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  let hc := hs.1.2
  let Γ := positiveRationalSubgroup F G T i
  let Q := PositiveRationalQuotient F G T i
  let dq := positiveRationalQuotientHaarMeasure F G T i
  letI := positiveRationalQuotient_borelSpace F G T i hi J e hc
  letI := haarQuotientMeasure_isOpenPosMeasure F G T i hi J e hc
  let R := canonicalL2BoundedRightAction hG
  have hV' : Langlands.Analysis.IsIrreducibleSubrepresentation
      (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R) V := hV
  letI : CompleteSpace V := hV.1.completeSpace_coe
  let π := invariantSubmoduleRepresentation R V (fun g v => hV'.2.2.1 g v v.property)
  have hirr : IsTopologicallyIrreducible π := irreducible_invariantSubmodule R V hV'
  have hnπ (g : A) (v : V) : ‖π g v‖ = ‖v‖ := by
    change ‖canonicalL2RightAction F G centralSplitTorusCharacter hG g v.val‖ = ‖v.val‖
    exact norm_canonicalL2RightAction hG g v.val
  have huπ (g : A) (u v : V) : ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ :=
    (show V →ₗᵢ[ℂ] V from ⟨(π g).toLinearMap, hnπ g⟩).inner_map_map _ _
  have hcπ (v : V) : Continuous fun g : A => π g v :=
    (continuous_canonicalL2RightAction_orbit hG v).subtype_mk _
  have hπ := continuous_action_of_isometric_orbits π hnπ hcπ
  let E := canonicalL2Equiv F G
  let j : V →L[ℂ] Lp ℂ 2 dq := E.symm.toLinearIsometry.toContinuousLinearMap.comp V.subtypeL
  let R' := haarQuotientL2BoundedRightAction F G T i hi J e hc
  let hR' := haarQuotientMeasureRightInvariant F G T i hi J e hc
  have hj (g : A) (v : V) : j (π g v) = R' g (j v) := by
    apply E.injective
    calc
      E (j (π g v)) = canonicalL2RightAction F G centralSplitTorusCharacter hG g v.val :=
        E.apply_symm_apply _
      _ = canonicalL2RightAction F G centralSplitTorusCharacter hG g (E (j v)) :=
        congrArg (canonicalL2RightAction F G centralSplitTorusCharacter hG g)
          (E.apply_symm_apply v.val).symm
      _ = E (R' g (j v)) :=
        (canonicalL2Equiv_rightAction F G centralSplitTorusCharacter hG hR' g (j v)).symm
  let w' : V := ⟨w, hw⟩
  have hwne : w' ≠ 0 := fun hz => hw0 (congrArg Subtype.val hz)
  have hWfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf => π (ofInfinite F G k.val) w')) := by
    let S := Submodule.span ℂ (Set.range fun k : Kinf => π (ofInfinite F G k.val) w')
    have he : S.map V.subtype = Submodule.span ℂ
        (Set.range fun k : Kinf => canonicalL2RightAction F G centralSplitTorusCharacter hG (ofInfinite F G k.val) w) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    letI : FiniteDimensional ℂ (S.map V.subtype) := he.symm ▸ hwfin.1
    exact Module.Finite.equiv (Submodule.equivMapOfInjective V.subtype V.subtype_injective S).symm
  obtain ⟨L, hLo, hwL⟩ := hwfin.2
  let U := L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup
  have hUo : IsOpen (U : Set B) := hLo.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hUc : IsCompact (U : Set B) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      (U.isClosed_of_isOpen hUo) inter_subset_right
  obtain ⟨h, u, hhk, hhd, huL, hconv⟩ := exists_archimedean_smooth_convolution_of_adelicFinite
    hsmooth hcalc π hG huπ hnπ hcπ hirr Kinf hK.isMaximalCompact_comap_ofInfinite U hUo w' hwne hWfin
    (fun l hl => Subtype.ext (hwL l hl.1))
  let f := liftArchimedeanKernel U h
  let φ := positiveQuotientLpSmoothing T i f (j u)
  have hf := liftArchimedeanKernel_isTestFunction hsmooth U hUo hUc h hhk hhd
  obtain ⟨hφs, hgrowth⟩ := positiveQuotientLpSmoothing_smooth_moderateGrowth T i hi J e hc
    hsmooth rho' hn hrho' hf (j u)
  have hφi : IsLeftInvariantUnder F G Γ φ := fun g hg =>
    positiveQuotientLpSmoothing_invariant T i f (j u) ⟨g, hg⟩
  obtain ⟨hws, hdiff⟩ := exists_convolution_enveloping_representative hsmooth hcalc T i hi J e hc
    π j hπ hj U hUo hUc u huL h hhk w' hconv hhd hφs
  obtain ⟨φ', _, _, hae, hslice⟩ := hdiff 1
  have hφ' : φ' = φ := by
    funext x
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = pair F G a b := ⟨_, _, (pair_projections F G x).symm⟩
    have he := congrFun (hslice b) a
    change functionInfiniteSlice F G φ' b a = functionInfiniteSlice F G φ b a
    simpa only [map_one, Module.End.one_apply] using he.symm
  have hrep : (j w' : Q → ℂ) =ᵐ[dq] fun q => φ q.out := by
    simpa only [map_one, Module.End.one_apply, hφ'] using hae
  have hΓr : IsLeftInvariantUnder F G (rationalSubgroup F G) φ := fun g hg =>
    hφi g (rationalSubgroup_le_positiveRationalSubgroup F G T i hg)
  have hΓa : IsLeftInvariantUnder F G (canonicalSubgroup F G) φ := fun g hg =>
    hφi g (imageSubgroup_le_positiveRationalSubgroup F G T i
      ((canonicalSubgroup_eq_imageSubgroup F G) ▸ hg))
  have hφK : IsInfiniteSubgroupFiniteFunction F G Kinf φ := by
    apply finite_representative_of_finite_class T i hi J e hc Kinf (j w') φ hφs.1 hφi hrep
    let S := Submodule.span ℂ (Set.range fun k : Kinf => π (ofInfinite F G k.val) w')
    have he : S.map j.toLinearMap = Submodule.span ℂ
        (Set.range fun k : Kinf => R' (ofInfinite F G k.val) (j w')) := by
      rw [Submodule.map_span, ← Set.range_comp]
      apply congrArg (Submodule.span ℂ)
      apply congrArg Set.range
      funext k
      exact hj _ _
    letI : FiniteDimensional ℂ S := hWfin
    rw [← he]
    exact Module.Finite.map S j.toLinearMap
  have hZ : IsCenterFiniteFunction F G hsmooth hcalc φ := by
    let σ := π.comp (ofInfinite F G).toMonoidHom
    let w₀ : Langlands.Archimedean.smoothVectors I σ := ⟨w', hws⟩
    let W := ProductSmoothVectors.smoothSubspace (smoothModel F d)
      (ofInfinite F G).toMonoidHom (ofFinite F G).toMonoidHom π
    have hwW : w' ∈ W := ⟨hws, L, hLo, fun l hl => Subtype.ext (hwL l hl)⟩
    have hWne : W ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨w', hwW, hwne⟩
    let C := AdelicEnvelopingCenter F G hsmooth
    let D := SmoothVectorEnveloping.envelopingAction σ hcalc
    let D₀ : C →ₗ[ℂ] V :=
      { toFun := fun z => (D z.val w₀ : V)
        map_add' := fun z z' => by simp only [Subalgebra.coe_add, map_add, LinearMap.add_apply, Submodule.coe_add]
        map_smul' := fun c z => by simp only [Subalgebra.coe_smul, map_smul, LinearMap.smul_apply,
          Submodule.coe_smul, RingHom.id_apply] }
    let P : Ideal C :=
      { carrier := {z | D z.val w₀ = 0}
        zero_mem' := by simp
        add_mem' := fun {z z'} hz hz' => by
          change D z.val w₀ = 0 at hz
          change D z'.val w₀ = 0 at hz'
          change D (z + z').val w₀ = 0
          simp only [Subalgebra.coe_add, map_add, LinearMap.add_apply, hz, hz', add_zero]
        smul_mem' := fun c z hz => by
          change D z.val w₀ = 0 at hz
          change D (c * z).val w₀ = 0
          simp only [Subalgebra.coe_mul, map_mul, Module.End.mul_apply, hz, map_zero] }
    have hP : P.restrictScalars ℂ = LinearMap.ker D₀ := by
      apply Submodule.ext
      intro z
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hline : LinearMap.range D₀ ≤ ℂ ∙ w' := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨c, hz⟩ := adelicSmoothCenterActsByScalar hsmooth hcalc hG π huπ hirr hWne z
      exact Submodule.mem_span_singleton.mpr ⟨c, (hz ⟨w', hwW⟩).symm⟩
    letI : FiniteDimensional ℂ (LinearMap.range D₀) := Submodule.finiteDimensional_of_le hline
    refine ⟨P, hP.symm ▸ Module.Finite.equiv D₀.quotKerEquivRange.symm, ?_⟩
    intro z hz b hb
    obtain ⟨ψ, hψc, hψi, hψae, hsψ⟩ := hdiff z.val
    have hzero : (D z.val w₀ : V) = 0 := congrArg Subtype.val (show D z.val w₀ = 0 from hz)
    have hzeroae : (0 : Q → ℂ) =ᵐ[dq] fun q => ψ q.out := by
      change (j (D z.val w₀) : Q → ℂ) =ᵐ[dq] (fun q => ψ q.out) at hψae
      rw [hzero, map_zero] at hψae
      exact (Lp.coeFn_zero _ _ _).symm.trans hψae
    have hqcont : Continuous (fun q : Q => ψ q.out) :=
      LeftCosetSpace.continuous_out_of_invariant _ (fun _ : Unit => ψ) (hψc.comp continuous_snd)
        (fun _ => hψi) |>.comp ((continuous_const (y := ())).prodMk continuous_id)
    have hψzero := Measure.eq_of_ae_eq hzeroae continuous_const hqcont
    apply Subtype.ext
    change ((plotSmoothEnvelopingAction F G hsmooth hcalc z.val ⟨functionInfiniteSlice F G φ b, hb⟩ :
      InfinitePlotSmoothFunctions F G) : M → ℂ) = 0
    rw [hsψ b]
    funext a
    have he := congrFun hψzero (LeftCosetSpace.mk Γ (pair F G a b))
    change 0 = ψ (LeftCosetSpace.mk Γ (pair F G a b)).out at he
    rw [LeftCosetSpace.out_mk_of_invariant Γ ψ hψi] at he
    exact he.symm
  refine ⟨φ, (hpos _ _ _).mpr ⟨hΓr, hφs, hφK, hZ, hgrowth⟩, hΓa, ?_⟩
  let eqQ := positiveToCanonicalQuotient hs
  have hq := measurePreserving_positiveToCanonicalQuotient hs
  have he : E (j w') = w := E.apply_symm_apply w
  rw [← he]
  have hj' : (E (j w') : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G] (j w' : Q → ℂ) ∘ eqQ.symm :=
    coeFn_quotientL2Equiv F G (canonicalSubgroup_eq_imageSubgroup F G) (j w')
  refine hj'.trans ((hq.symm eqQ).quasiMeasurePreserving.ae_eq_comp hrep |>.trans ?_)
  exact ae_of_all _ fun q => by
    have hqmk : eqQ (LeftCosetSpace.mk Γ q.out) = LeftCosetSpace.mk (canonicalRationalSubgroup F G) q.out :=
      quotientMeasurableEquiv_mk F G (canonicalSubgroup_eq_imageSubgroup F G) q.out
    have ht : eqQ.symm q = LeftCosetSpace.mk Γ q.out := by
      rw [MeasurableEquiv.symm_apply_eq, hqmk]
      exact (Quotient.out_eq q).symm
    simp only [Function.comp_apply, ht, LeftCosetSpace.out_mk_of_invariant Γ φ hφi]

end Langlands.Global
