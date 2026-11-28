import Langlands.Global.AdelicCharacteristicShellRegions
import Langlands.Global.AdelicParabolicPeriodVanishing
import Langlands.Global.LeftCosetDiscreteProjectionRestriction

/-! # Unfolding the characteristic shell into the rational parabolic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set TensorProduct Topology Function
open scoped CategoryTheory.MonObj Pointwise TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  ArthurParabolicSpaces AdelicGroupPoints AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "A₁" => normOneSubgroup F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "Idx" => Langlands.Global.StandardIndex F G i ν
local notation "ΓQ[" J "]" =>
  parabolicRationalNormOneSubgroup (F := F) (Standard.parabolicHom i ν (Subtype.val J))
local notation "Δ" => simpleRelativeRoots i ν
local notation "Δ₀" => simpleFinset ν hG hi
local notation "H₀" => height hi hK hρ

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- Membership in the rational parabolic on the norm-one group agrees with membership of
the underlying adelic point in its rational image. -/
theorem mem_standardParabolicRationalNormOneSubgroup (J : Idx) (x : A₁) :
    x ∈ ΓQ[J] ↔ x.val ∈ parabolicRationalImage (Standard.parabolicHom i ν J.val) := by
  rw [mem_parabolicRationalImage_iff]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨rationalNormOne F _ q, ⟨q, rfl⟩, Subtype.ext hq⟩

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- The rational parabolic norm-one subgroup is contained in the ambient rational one. -/
theorem standardParabolicRationalNormOneSubgroup_le (J : Idx) : ΓQ[J] ≤ Γ := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact ⟨_, (mapNormOne_rationalNormOne F _ _ (Standard.parabolicHom i ν J.val) q).symm⟩

/-- The image of the characteristic shell product in the rational parabolic quotient. -/
def characteristicShellLift (J : Idx) (T₀ Tp S : V T) : Set (LeftCosetSpace (ΓQ[J])) :=
  LeftCosetSpace.mk (ΓQ[J]) '' (Subtype.val ⁻¹' characteristicHeightProduct hi hK hρ C
    (characteristicShell hG hi D J T₀ Tp S))

omit [LocallyOfFiniteType G.X.hom] in
/-- The parabolic quotient shell projects onto the characteristic shell in the ambient
rational quotient. -/
theorem projection_image_characteristicShellLift (J : Idx) (T₀ Tp S : V T) :
    LeftCosetSpace.projectionOfLE (standardParabolicRationalNormOneSubgroup_le J) ''
      characteristicShellLift hG hi D hK hρ C J T₀ Tp S =
        characteristicShellRegion hG hi D hK hρ C J T₀ Tp S := by
  rw [characteristicShellLift, characteristicShellRegion, Set.image_image]
  rfl

include hν in
/-- For a common sufficiently regular start, the projection of each parabolic quotient
shell is injective. -/
theorem exists_injOn_projection_characteristicShellLift
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ : V T) :
    ∃ R > 0, ∀ (Tp S : V T), (∀ α ∈ Δ, R ≤ eval T α Tp) → ∀ J : Idx,
      InjOn (LeftCosetSpace.projectionOfLE (standardParabolicRationalNormOneSubgroup_le J))
        (characteristicShellLift hG hi D hK hρ C J T₀ Tp S) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨T₁, hT₁⟩ := exists_strict_lower_cutoff (i := i) (ν := ν) T₀
  obtain ⟨R, hR, hsep⟩ :=
    exists_rational_cell_separation_threshold hG hi hν D hK hρ C hC T₁
  refine ⟨R, hR, fun Tp S hTp J => ?_⟩
  let heights := characteristicShell hG hi D J T₀ Tp S
  have hcut (X : V T) (hX : X ∈ heights) (α : characterLattice T) (hα : α ∈ Δ) :
      0 < eval T α (X - T₁) := hT₁ X α hα (hX.2.2.1 α hα)
  have hrep (x : A₁) (hx : x.val ∈ characteristicHeightProduct hi hK hρ C heights) :
      ∃ x' : A₁, LeftCosetSpace.mk (ΓQ[J]) x' = LeftCosetSpace.mk (ΓQ[J]) x ∧
        x'.val ∈ parabolicCharacteristicSiegelSet hG hi D hK hρ C J T₁ T₀ Tp := by
    obtain ⟨d, hd, hyS, hyA⟩ :=
      exists_siegelRepresentative_of_mem_characteristicHeightProduct hG hi hν hK hρ C hC hcov hcut hx
    have hdQ := parabolicRationalImage_mono hG hi hν (empty_subset J.val) J.2 hd
    obtain ⟨q, hq⟩ := (mem_parabolicRationalImage_iff _ d).mp hdQ
    let d' := mapNormOne F _ G (Standard.parabolicHom i ν J.val) (rationalNormOne F _ q)
    have hd' : d' ∈ ΓQ[J] := ⟨_, ⟨q, rfl⟩, rfl⟩
    have he : (d' * x).val = d * x.val :=
      congrArg (· * x.val) hq
    refine ⟨d' * x, LeftCosetSpace.mk_subgroup_mul (ΓQ[J]) ⟨d', hd'⟩ x, ?_⟩
    rw [he]
    exact ⟨hyS, hyA.2⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  obtain ⟨x', hx', hxS⟩ := hrep x hx
  obtain ⟨y', hy', hyS⟩ := hrep y hy
  rw [← hx', ← hy'] at he ⊢
  have he' : LeftCosetSpace.mk Γ x' = LeftCosetSpace.mk Γ y' := he
  have hd : y' * x'⁻¹ ∈ Γ := (LeftCosetSpace.mk_eq_mk_iff Γ x' y').mp he'
  have hdA : (y' * x'⁻¹).val ∈ rationalSubgroup F G :=
    (rationalNormOneSubgroupInclusion F G ⟨_, hd⟩).2
  have heq : (y' * x'⁻¹).val * x'.val = y'.val :=
    congrArg Subtype.val (inv_mul_cancel_right y' x')
  have hdQ := (hsep hTp hdA hxS (heq.symm ▸ hyS)).2
  exact (LeftCosetSpace.mk_eq_mk_iff (ΓQ[J]) x' y').mpr
    ((mem_standardParabolicRationalNormOneSubgroup J _).mpr hdQ)

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem continuous_linear_height (f : V T →ₗ[ℝ] ℝ) : Continuous (fun x : A => f (H₀ x)) := by
  have hcm (m : RealCharacterParameter F (Standard.parabolicScheme i ν ∅)) :
      Continuous (realParameterPairing F _ m) := by
    induction m using TensorProduct.inductionOn with
    | tmul t χ =>
      exact (continuous_const.mul (continuous_dualEval F _ χ)).congr fun x =>
        (realParameterPairing_tmul F _ t χ x).symm
    | add x y hx hy => exact (hx.add hy).congr fun _ => by simp
  obtain ⟨v, hv⟩ := (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_left.surjective f
  obtain ⟨m, hm⟩ := hρ.surjective v
  rw [← hv, ← hm]
  exact ((hcm m).comp hK.continuous_height).congr fun x =>
    (pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height x) m).symm

/-- The shell lift is Borel, since the minimal Levi slice is locally closed and its product
with the compact unipotent and Iwasawa factors is a countable union of compact sets. -/
theorem measurableSet_characteristicShellLift (J : Idx) (T₀ Tp S : V T) :
    MeasurableSet (characteristicShellLift hG hi D hK hρ C J T₀ Tp S) := by
  classical
  let M₀ := Standard.leviScheme i ν ∅
  let m := map F M₀ G (Standard.leviHom i ν ∅)
  let H (x : AdelicGroupPoints F M₀) := H₀ (m x)
  let p := D.realCorootSpan.subtype.comp (ArthurRelative.toCorootSpan hG hi D)
  have hlin (f : V T →ₗ[ℝ] ℝ) : Continuous (fun x => f (H x)) :=
    (continuous_linear_height hi hK hρ f).comp m.continuous
  have haff (f : V T →ₗ[ℝ] ℝ) (Y : V T) : Continuous (fun x => f (H x - Y)) := by
    simp only [map_sub]
    exact (hlin f).sub continuous_const
  have hspan : IsClosed {x | H x ∈ D.realCorootSpan} := by
    have he : {x | H x ∈ D.realCorootSpan} =
        ⋂ t : Vstar T, {x | pair T t (H x) = pair T t (p (H x))} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hx t
        have hp : p (H x) = H x := congrArg Subtype.val
          (ArthurRelative.toCorootSpan_apply_coe hG hi D (⟨H x, hx⟩ : D.realCorootSpan))
        rw [hp]
      · intro hx
        have hp : H x = p (H x) :=
          (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_right.injective
            (LinearMap.ext fun t => hx t)
        rw [hp]
        exact (ArthurRelative.toCorootSpan hG hi D (H x)).2
    rw [he]
    exact isClosed_iInter fun t => isClosed_eq (hlin (pair T t)) (hlin ((pair T t).comp p))
  let w := ArthurRelative.weight hG hi ν D (Δ₀ : Set (characterLattice T))
  let wQ := ArthurRelative.weight hG hi ν D J.val
  let bounds : Set (AdelicGroupPoints F M₀) := ⋂ α : Δ₀,
    {x | 0 ≤ eval T α.val (H x - T₀) ∧ w α.val (H x - (Tp + S)) ≤ 0}
  have hbounds : IsClosed bounds :=
    isClosed_iInter fun α => (isClosed_le continuous_const (haff (eval T α.val) T₀)).inter
      (isClosed_le (haff (w α.val) (Tp + S)) continuous_const)
  let boundsQ : Set (AdelicGroupPoints F M₀) := ⋂ α : J.val,
    {x | wQ α.val (H x - Tp) ≤ 0}
  have hboundsQ : IsClosed boundsQ :=
    isClosed_iInter fun α => isClosed_le (haff (wQ α.val) Tp) continuous_const
  let closed : Set (AdelicGroupPoints F M₀) :=
    m ⁻¹' (normOneSubgroup F G : Set A) ∩ {x | H x ∈ D.realCorootSpan} ∩ bounds ∩ boundsQ
  have hclosed : IsClosed closed :=
    ((((isClosed_normOneSubgroup F G).preimage m.continuous).inter hspan).inter hbounds).inter hboundsQ
  let O := ⋂ α : (Δ \ J.val : Set (characterLattice T)),
    {x | 0 < eval T α.val (ArthurRelative.levelProjection hG hi ν D J.val (H x - Tp))}
  let : Finite ↥(Δ \ J.val : Set (characterLattice T)) := Set.finite_coe_iff.mpr
    ((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).sdiff (t := J.val))
  have hopen : IsOpen O := isOpen_iInter_of_finite fun α =>
    isOpen_lt continuous_const (haff ((eval T α.val).comp
      (ArthurRelative.levelProjection hG hi ν D J.val)) Tp)
  have he : leviHeightSet hi hK hρ (characteristicShell hG hi D J T₀ Tp S) = m '' (closed ∩ O) := by
    ext x
    constructor
    · rintro ⟨y, rfl, hy, hA, hQ⟩
      exact ⟨y, ⟨⟨⟨⟨hy, hA.1⟩, Set.mem_iInter.mpr (fun α => hA.2 α α.2)⟩,
        Set.mem_iInter.mpr (fun α => hQ.2.2.1 α α.2)⟩,
        Set.mem_iInter.mpr (fun α => hQ.2.2.2 α α.2)⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hc := hy.1
      have hA (α : characterLattice T) (hα : α ∈ Δ₀) :=
        Set.mem_iInter.mp hc.1.2 (⟨α, hα⟩ : Δ₀)
      refine ⟨y, rfl, hc.1.1.1, ⟨hc.1.1.2, hA⟩,
        hc.1.1.2, fun α hα => (hA α ((mem_simpleFinset hG hi).mpr hα)).1, ?_, ?_⟩
      · exact fun α hα => Set.mem_iInter.mp hc.2 (⟨α, hα⟩ : J.val)
      · exact fun α hα => Set.mem_iInter.mp hy.2 (⟨α, hα⟩ : (Δ \ J.val : Set _))
  let hM := Standard.isClosedSubgroup_leviHom i ν ∅
  let : IsAffineHom M₀.X.hom := hM.isAffineHom
  let : IsAffine M₀.X.left := isAffine_of_isAffineHom M₀.X.hom
  let : LocallyOfFiniteType M₀.X.hom := hM.locallyOfFiniteType
  let : LocallyCompactSpace O := hopen.locallyCompactSpace
  let : SecondCountableTopology O := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  obtain ⟨B, hB, hBu⟩ := (isSigmaCompact_iff_sigmaCompactSpace.2 (inferInstance : SigmaCompactSpace O))
  let E (n : ℕ) := (map F _ G (Standard.unipotentHom i ν ∅) '' C.omegaN) *
    (m '' (closed ∩ B n)) * (K : Set A)
  have hE : characteristicHeightProduct hi hK hρ C (characteristicShell hG hi D J T₀ Tp S) =
      ⋃ n, E n := by
    rw [characteristicHeightProduct, he, ← hBu]
    simp only [E, inter_iUnion, Set.image_iUnion, Set.mul_iUnion, Set.iUnion_mul]
  rw [characteristicShellLift, hE, Set.preimage_iUnion, Set.image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  have hEn : IsCompact (E n) :=
    ((C.compact_omegaN.image (map F _ G (Standard.unipotentHom i ν ∅)).continuous).mul
      (((hB n).inter_left hclosed).image m.continuous)).mul hK.isCompact
  let : IsClosed (ΓQ[J] : Set A₁) := (ΓQ[J]).isClosed_of_isDiscrete
    (isDiscrete_parabolicRationalNormOneSubgroup (Standard.parabolicHom i ν J.val))
  exact ((isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal.isCompact_preimage hEn
    |>.image (LeftCosetSpace.continuous_mk (ΓQ[J]))).measurableSet

/-- On every shell at a common sufficiently regular start, the projection preserves
the restricted counting-normalized quotient measures for the same ambient Haar measure. -/
def CharacteristicShellUnfoldingStatement (dh : Measure A₁) [dh.IsMulLeftInvariant]
    (T₀ : V T) : Prop :=
  ∃ R > 0, ∀ (Tp S : V T), (∀ α ∈ Δ, R ≤ eval T α Tp) → ∀ J : Idx,
    MeasurePreserving (LeftCosetSpace.projectionOfLE (standardParabolicRationalNormOneSubgroup_le J))
      ((LeftCosetSpace.discreteQuotientMeasure (ΓQ[J])
        (isDiscrete_parabolicRationalNormOneSubgroup (Standard.parabolicHom i ν J.val)) dh).restrict
          (characteristicShellLift hG hi D hK hρ C J T₀ Tp S))
      ((LeftCosetSpace.discreteQuotientMeasure Γ (isDiscrete_rationalNormOneSubgroup F G) dh).restrict
        (characteristicShellRegion hG hi D hK hρ C J T₀ Tp S))

include hν in
/-- Unfold the characteristic shell using Borel measurability, rational separation and the
exact normalization for injective restrictions of discrete quotients. -/
theorem characteristicShellUnfolding (dh : Measure A₁) [dh.IsMulLeftInvariant]
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ : V T) :
    CharacteristicShellUnfoldingStatement hG hi D hK hρ C dh T₀ := by
  obtain ⟨R, hR, hsep⟩ := exists_injOn_projection_characteristicShellLift hG hi hν D hK hρ C hC hcov T₀
  refine ⟨R, hR, fun Tp S hTp J => ?_⟩
  rw [← projection_image_characteristicShellLift hG hi D hK hρ C J T₀ Tp S]
  exact LeftCosetSpace.measurePreserving_projectionOfLE_restrict
    (standardParabolicRationalNormOneSubgroup_le J) (isDiscrete_rationalNormOneSubgroup F G) dh
    (isDiscrete_parabolicRationalNormOneSubgroup (Standard.parabolicHom i ν J.val)) _
    (measurableSet_characteristicShellLift hG hi D hK hρ C J T₀ Tp S) (hsep Tp S hTp J)

end Langlands.Global.ArthurTruncation
