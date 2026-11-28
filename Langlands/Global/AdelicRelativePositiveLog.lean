import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicRelativeLeviHaar
import Langlands.Global.ArthurTruncationCentralTranslation
import Langlands.Global.AdelicTruncatedEisensteinPairing

/-! # Logarithmic coordinates of the relative positive split component -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set Topology
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative

namespace PositiveRealTorus

variable {F : Type} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The real cocharacter space of a split torus is the real dual of its integral characters. -/
def cocharacterFunctionalEquiv (hT : IsSplitTorus T.toGrp) : V T ≃ₗ[ℝ] RealCharacterDual F T.toGrp := by
  let l : V T →ₗ[ℝ] RealCharacterDual F T.toGrp :=
    { toFun := cocharacterFunctional
      map_add' := fun x y => AddMonoidHom.ext fun c => (pair T ((1 : ℝ) ⊗ₜ[ℤ] c)).map_add x y
      map_smul' := fun r x => AddMonoidHom.ext fun c => (pair T ((1 : ℝ) ⊗ₜ[ℤ] c)).map_smul r x }
  refine LinearEquiv.ofBijective l ⟨?_, exists_cocharacterFunctional_eq hT⟩
  intro x y hxy
  have := isPerfPair_of_isSplitTorus hT
  apply (LinearMap.IsPerfPair.bijective_right (pair T)).injective
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    have h := congrArg (fun h : RealCharacterDual F T.toGrp => h c) hxy
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] c) x = pair T ((1 : ℝ) ⊗ₜ[ℤ] c) y at h
    rw [show r ⊗ₜ[ℤ] c = r • ((1 : ℝ) ⊗ₜ[ℤ] c) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simpa only [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] using
      congrArg (r * ·) h
  | add z w hz hw => simp only [LinearMap.flip_apply, map_add] at hz hw ⊢; rw [hz, hw]

@[simp] theorem cocharacterFunctionalEquiv_apply (hT : IsSplitTorus T.toGrp) (v : V T) :
    cocharacterFunctionalEquiv hT v = cocharacterFunctional v := rfl

variable [NumberField F]

/-- The ambient norm-one condition on a torus point is the annihilator of the
restricted real-character space. -/
theorem map_mem_normOne_iff_log_mem_annihilator
    {G : GroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (t : AdelicGroupPoints F T.toGrp) (v : V T)
    (ht : characterLog F T.toGrp t = cocharacterFunctional v) :
    map F T.toGrp G i t ∈ normOneSubgroup F G ↔
      v ∈ cocharacterAnnihilator (rationalCharacterRestrictReal i).range := by
  rw [← characterLog_eq_zero_iff, characterLog_map, ht, mem_cocharacterAnnihilator]
  constructor
  · intro hz z hzmem
    have hz' (c : RealCharacterParameter F G) : pair T (rationalCharacterRestrictReal i c) v = 0 := by
      induction c using TensorProduct.inductionOn with
      | tmul r c =>
        have h := congrArg (fun f : RealCharacterDual F G => f c) hz
        change pair T ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict i c) v = 0 at h
        rw [rationalCharacterRestrictReal_tmul, show r ⊗ₜ[ℤ] characterRestrict i c =
          r • ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict i c) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul, LinearMap.smul_apply, h, smul_zero]
      | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, add_zero]
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hzmem
    exact hc ▸ hz' c
  · intro hv
    apply AddMonoidHom.ext
    intro c
    exact hv _ ⟨(1 : ℝ) ⊗ₜ[ℤ] c, rfl⟩

end PositiveRealTorus

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {nT : ℕ} (eT : V fam.T ≃ₗ[ℝ] (Fin nT → ℝ))

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "A" => fam.A J
local notation "j" => fam.l J ≫ fam.p J
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)

/-- The actual relative split coroot space, with the topology of a finite real chart. -/
def relativePositiveRealChart : Submodule ℝ (Fin nT → ℝ) :=
  (aSpace fam.T J.val ⊓ fam.coroots.realCorootSpan).map eT.toLinearMap

private theorem normOne_torus_iff {t : AdelicGroupPoints F fam.T.toGrp} (v : V fam.T)
    (ht : characterLog F fam.T.toGrp t = cocharacterFunctional v) :
    map F fam.T.toGrp G fam.i t ∈ normOneSubgroup F G ↔ v ∈ fam.coroots.realCorootSpan := by
  have hi := fam.maximalSplit
  obtain ⟨C, hC⟩ := exists_isWeylInvariantInnerProduct fam.connectedReductive hi
  rw [map_mem_normOne_iff_log_mem_annihilator fam.i t v ht,
    fam.coroots.realCorootSpan_eq_annihilator hi.isSplitSubtorus.1
      (isCompl_relativeRootSpanReal fam.connectedReductive hi) C hC]

/-- The actual relative positive points have logarithms precisely in the intersection of the
split directions of `J` with the ambient coroot span. The logarithm in the parabolic agrees
with the restricted functional `splitDual`. -/
def RelativePositiveLogCoordinatesStatement : Prop :=
  ∃ L : B ≃ₜ* Multiplicative (fam.relativePositiveRealChart J eT),
    ∀ b : B,
      let v := eT.symm (L b).toAdd.val
      (∃ t : intrinsicSubgroup F fam.T,
        map F M G (j) (positivePointMap F M A (fam.a J) b.val) = map F fam.T.toGrp G fam.i t.val ∧
        characterLog F fam.T.toGrp t.val = cocharacterFunctional v) ∧
      characterLog F P (map F M P (fam.l J) (positivePointMap F M A (fam.a J) b.val)) =
        fam.splitDual J v

set_option maxHeartbeats 1500000 in
/-- Use the split component's closed embedding into the maximal split torus. Restrict the
full torus logarithm to the kernel of the ambient character logarithm. -/
theorem relativePositiveLogCoordinates : fam.RelativePositiveLogCoordinatesStatement J eT := by
  have hcompat := fam.isCompatible J
  have hclosed : IsClosedSubgroup (j) := hcompat.levi.isClosedSubgroup.comp hcompat.parabolic.isClosedSubgroup
  let : IsClosedImmersion (j).hom.hom.left := hclosed
  have hrep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (j) :=
    ⟨Over.mono_of_mono_left _, hcompat.levi_eq⟩
  obtain ⟨_, f, hf, _, hfinj, hfrange, _⟩ :=
    (standardLeviCentralDirections.2 F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic J.val J.property M (j) hclosed hrep).2 A (fam.a J) hcompat.splitComponent
  have hfrange' : (cocharacterMapReal f).range = aSpace fam.T J.val := hfrange
  have hA : IsSplitTorus (A).toGrp := hcompat.splitComponent.1.1.1
  obtain ⟨I, hI, ⟨eA⟩⟩ := hcompat.splitComponent.1.1.1
  let : Fintype I := Fintype.ofFinite I
  let eDual := cocharacterFunctionalEquiv hA
  let eLog := positiveLogCoordinateEquiv F A I eA
  let eCoord := dualCoordinatesEquiv F A I eA
  let L : (I → ℝ) →ₗ[ℝ] (Fin nT → ℝ) :=
    eT.toLinearMap.comp ((cocharacterMapReal f).comp (eDual.symm.toLinearMap.comp eCoord.symm.toLinearMap))
  have hLinj : Function.Injective L :=
    eT.injective.comp (hfinj.comp (eDual.symm.injective.comp eCoord.symm.injective))
  let eRange := (LinearEquiv.ofInjective L hLinj).toContinuousLinearEquiv
  let eFull : intrinsicSubgroup F A ≃ₜ* Multiplicative L.range := eLog.trans
    { toMulEquiv := eRange.toLinearEquiv.toAddEquiv.toMultiplicative
      continuous_toFun := eRange.continuous
      continuous_invFun := eRange.symm.continuous }
  let C := fam.relativePositiveRealChart J eT
  have hSub : C ≤ L.range := by
    rintro _ ⟨v, hv, rfl⟩
    have ha : v ∈ aSpace fam.T J.val := hv.1
    rw [← hfrange'] at ha
    obtain ⟨w, rfl⟩ := ha
    refine ⟨eCoord (eDual w), ?_⟩
    change eT (cocharacterMapReal f (eDual.symm (eCoord.symm (eCoord (eDual w))))) = _
    rw [eCoord.symm_apply_apply, eDual.symm_apply_apply]
    rfl
  let inclC : C →ₗ[ℝ] L.range := Submodule.inclusion hSub
  have hlog (b : intrinsicSubgroup F A) :
      (eFull b).toAdd.val = eT (cocharacterMapReal f (eDual.symm (characterLog F (A).toGrp b.val))) := by
    change eT (cocharacterMapReal f (eDual.symm
      (eCoord.symm (eCoord (characterLog F (A).toGrp b.val))))) = _
    rw [eCoord.symm_apply_apply]
  let t (b : intrinsicSubgroup F A) : AdelicGroupPoints F fam.T.toGrp :=
    map F (A).toGrp fam.T.toGrp (CommGroupScheme.groupHom f) b.val
  have ht (b : intrinsicSubgroup F A) : t b ∈ intrinsicSubgroup F fam.T :=
    map_intrinsicSubgroup_le F A fam.T f ⟨b.val, b.property, rfl⟩
  have htLog (b : intrinsicSubgroup F A) :
      characterLog F fam.T.toGrp (t b) = cocharacterFunctional (eT.symm (eFull b).toAdd.val) := by
    change characterLog F fam.T.toGrp (map F (A).toGrp fam.T.toGrp (CommGroupScheme.groupHom f) b.val) = _
    rw [hlog, eT.symm_apply_apply, characterLog_map, cocharacterFunctional_cocharacterMapReal,
      ← cocharacterFunctionalEquiv_apply hA, eDual.apply_symm_apply]
  have hGcmp (b : intrinsicSubgroup F A) :
      map F M G (j) (positivePointMap F M A (fam.a J) b) = map F fam.T.toGrp G fam.i (t b) := by
    change map F M G (j) (map F (A).toGrp M (fam.a J) b.val) =
      map F fam.T.toGrp G fam.i (map F (A).toGrp fam.T.toGrp (CommGroupScheme.groupHom f) b.val)
    rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom, hf]
  have hmem (b : intrinsicSubgroup F A) : (eFull b).toAdd.val ∈ C ↔ b ∈ B := by
    change (eFull b).toAdd.val ∈ (aSpace fam.T J.val ⊓ fam.coroots.realCorootSpan).map eT.toLinearMap ↔ _
    have hChart : (eFull b).toAdd.val ∈ (aSpace fam.T J.val ⊓ fam.coroots.realCorootSpan).map eT.toLinearMap ↔
        eT.symm (eFull b).toAdd.val ∈ aSpace fam.T J.val ⊓ fam.coroots.realCorootSpan := by
      constructor
      · rintro ⟨v, hv, he⟩
        change eT v = _ at he
        rw [← he, eT.symm_apply_apply]
        exact hv
      · intro hv
        exact ⟨_, hv, eT.apply_symm_apply _⟩
    rw [hChart]
    have ha : eT.symm (eFull b).toAdd.val ∈ aSpace fam.T J.val := by
      rw [hlog, eT.symm_apply_apply, ← hfrange']
      exact ⟨_, rfl⟩
    change (eT.symm (eFull b).toAdd.val ∈ aSpace fam.T J.val ∧
      eT.symm (eFull b).toAdd.val ∈ fam.coroots.realCorootSpan) ↔
      map F M G (j) (positivePointMap F M A (fam.a J) b) ∈ normOneSubgroup F G
    rw [and_iff_right ha, hGcmp, fam.normOne_torus_iff _ (htLog b)]
  let embedC : Multiplicative C → Multiplicative L.range :=
    fun x => Multiplicative.ofAdd (inclC x.toAdd)
  have hembedC : Continuous embedC :=
    (continuous_subtype_val : Continuous (Subtype.val : C → (Fin nT → ℝ))).subtype_mk _
  let w : B ≃ₜ* Multiplicative C :=
    { toFun := fun b => Multiplicative.ofAdd ⟨(eFull b.val).toAdd.val, (hmem b.val).mpr b.property⟩
      invFun := fun x => ⟨eFull.symm (embedC x), (hmem _).mp (by
        rw [eFull.apply_symm_apply]
        exact x.toAdd.property)⟩
      left_inv := fun b => Subtype.ext (eFull.symm_apply_apply b.val)
      right_inv := fun x => Subtype.ext (congrArg (fun y : Multiplicative L.range => y.toAdd.val)
        (eFull.apply_symm_apply (embedC x)))
      map_mul' := fun b b' => Subtype.ext (congrArg (fun y : Multiplicative L.range => y.toAdd.val)
        (eFull.map_mul b.val b'.val))
      continuous_toFun := ((continuous_subtype_val : Continuous (Subtype.val : L.range → (Fin nT → ℝ))).comp
        (eFull.continuous.comp continuous_subtype_val)).subtype_mk _
      continuous_invFun := (eFull.symm.continuous.comp hembedC).subtype_mk _ }
  refine ⟨w, fun b => ⟨⟨⟨t b.val, ht b.val⟩, hGcmp b.val, htLog b.val⟩, ?_⟩⟩
  let u := map F M P (fam.l J) (positivePointMap F M A (fam.a J) b.val)
  let u' := map F fam.T.toGrp P (fam.torus J ≫ fam.l J) (t b.val)
  have hu : u = u' := by
    let : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
    apply (isClosedEmbedding_map F P G (fam.p J)).injective
    change map F P G (fam.p J) (map F M P (fam.l J) (positivePointMap F M A (fam.a J) b.val)) =
      map F P G (fam.p J) (map F fam.T.toGrp P (fam.torus J ≫ fam.l J) (t b.val))
    rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom, Category.assoc, fam.torus_comp]
    exact hGcmp b.val
  change characterLog F P u = _
  rw [hu, show u' = map F fam.T.toGrp P (fam.torus J ≫ fam.l J) (t b.val) from rfl,
    characterLog_map, htLog]
  rfl

/-- The cocharacter read from the torus logarithm is its ambient minimal Iwasawa height. -/
theorem minimalHeight_eq_of_torusLog
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (t : AdelicGroupPoints F fam.T.toGrp) (v : V fam.T)
    (ht : characterLog F fam.T.toGrp t = cocharacterFunctional v) :
    ArthurTruncation.height fam.maximalSplit (fam.isIwasawaCompact_standardBot hK)
      fam.bijective_restrictToTorus_bot (map F fam.T.toGrp G fam.i t) = v := by
  apply (cocharacterFunctionalEquiv fam.maximalSplit.isSplitSubtorus.1).injective
  apply AddMonoidHom.ext
  intro c
  let χ : characterLattice fam.T := c
  change pair fam.T ((1 : ℝ) ⊗ₜ[ℤ] χ)
    (ArthurTruncation.height fam.maximalSplit (fam.isIwasawaCompact_standardBot hK)
      fam.bijective_restrictToTorus_bot (map F fam.T.toGrp G fam.i t)) = cocharacterFunctional v χ
  rw [← eval_eq_pair, ArthurTruncation.eval_height_torus, realParameterPairing_tmul, one_mul, ht]

end StandardParabolicFamily

end Langlands.Global
