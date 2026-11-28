import Langlands.Global.AdelicCharacteristicHeightProduct
import Langlands.Global.AdelicTruncationShellPartition
import Langlands.Global.AdelicSplitCenterHaar

/-! # Disjoint characteristic shells on the actual norm-one quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set TensorProduct Topology
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

local notation "Idx" => Langlands.Global.StandardIndex F G i ν
local notation "Γ" => rationalNormOneSubgroup F G
local notation "Δ" => simpleRelativeRoots i ν
local notation "Δ₀" => simpleFinset ν hG hi
local notation "H₀" => height hi hK hρ

/-- The image of the minimal-Levi product with heights in the actual shell `C^Q_{T+S,T}`. -/
def characteristicShellRegion (J : Idx) (T₀ Tp S : V T) :
    Set (NormOneRationalQuotient F G) :=
  LeftCosetSpace.mk Γ '' (Subtype.val ⁻¹' characteristicHeightProduct hi hK hρ C
    (characteristicShell hG hi D J T₀ Tp S))

include hν in
/-- The characteristic region at `T + S` is covered by the actual shell regions. -/
theorem characteristicRegion_eq_iUnion_shellRegions
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ Tp S : V T) :
    characteristicRegion hG hi D hK hρ C T₀ (Tp + S) =
      ⋃ J : Idx, characteristicShellRegion hG hi D hK hρ C J T₀ Tp S := by
  obtain ⟨T₁, hT₁⟩ := exists_strict_lower_cutoff (i := i) (ν := ν) T₀
  let A := characteristicChamber ν hG hi D T₀ (Tp + S)
  have hcut (X : V T) (hX : X ∈ A) (α : characterLattice T) (hα : α ∈ Δ) :
      0 < eval T α (X - T₁) :=
    hT₁ X α hα (hX.2 α ((mem_simpleFinset hG hi).mpr hα)).1
  change LeftCosetSpace.mk Γ '' (Subtype.val ⁻¹' characteristicHeightProduct hi hK hρ C A) = _
  ext y
  constructor
  · rw [normOneCharacteristicHeightImage_eq hG hi hν hK hρ C hC hcov hcut]
    rintro ⟨x, ⟨hxS, hxA⟩, rfl⟩
    have hx : H₀ x.val ∈ A := hxA
    obtain ⟨J, hJ⟩ := exists_mem_parabolicCharacteristicChamber hG hi hν D (Tp := Tp) hx.1
      (fun α hα => (hx.2 α ((mem_simpleFinset hG hi).mpr hα)).1)
    apply Set.mem_iUnion.mpr
    refine ⟨J, x, ?_, rfl⟩
    exact mem_characteristicHeightProduct_of_siegelRepresentative hG hi hν hK hρ C hC hxS x.2
      (A := characteristicShell hG hi D J T₀ Tp S) ⟨hxA, hJ⟩
  · intro hy
    obtain ⟨J, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
    refine ⟨x, ?_, rfl⟩
    obtain ⟨_, ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, rfl, hm, hX⟩, rfl⟩, k, hk, heq⟩ := hx
    exact ⟨_, ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, rfl, hm, hX.1⟩, rfl⟩, k, hk, heq⟩

include hν in
/-- For a sufficiently regular `T`, the actual shell regions are disjoint for distinct indices.
The root threshold is independent of the increment `S`. -/
theorem exists_pairwiseDisjoint_characteristicShellRegion
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ : V T) :
    ∃ R > 0, ∀ (Tp S : V T), (∀ α ∈ Δ, R ≤ eval T α Tp) →
      Set.univ.PairwiseDisjoint
        (fun J : Idx => characteristicShellRegion hG hi D hK hρ C J T₀ Tp S) := by
  obtain ⟨T₁, hT₁⟩ := exists_strict_lower_cutoff (i := i) (ν := ν) T₀
  obtain ⟨R, hR, hd⟩ := exists_pairwiseDisjoint_normOneCharacteristicSiegelRegion hG hi hν D
    hK hρ C hC T₁
  refine ⟨R, hR, fun Tp S hTp => ?_⟩
  have hsub (J : Idx) : characteristicShellRegion hG hi D hK hρ C J T₀ Tp S ⊆
      normOneCharacteristicSiegelRegion hG hi D hK hρ C J T₁ T₀ Tp := by
    have hcut (X : V T) (hX : X ∈ characteristicShell hG hi D J T₀ Tp S)
        (α : characterLattice T) (hα : α ∈ Δ) : 0 < eval T α (X - T₁) :=
      hT₁ X α hα (hX.2.2.1 α hα)
    unfold characteristicShellRegion
    rw [normOneCharacteristicHeightImage_eq hG hi hν hK hρ C hC hcov hcut]
    rintro _ ⟨x, ⟨hxS, hxA⟩, rfl⟩
    exact ⟨x, ⟨hxS, hxA.2⟩, rfl⟩
  intro J hJ J' hJ' hne
  exact (hd hTp hJ hJ' hne).mono (hsub J) (hsub J')

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The full-group parabolic chamber has exactly the characteristic inequalities of `G`. -/
theorem parabolicCharacteristicChamber_top (T₀ Tp : V T) :
    parabolicCharacteristicChamber hG hi D (⟨Δ, Subset.refl _⟩ : Idx) T₀ Tp =
      characteristicChamber ν hG hi D T₀ Tp := by
  ext X
  constructor
  · intro hx
    exact ⟨hx.1, fun α hα => by
      have hm := (mem_simpleFinset hG hi).mp hα
      refine ⟨hx.2.1 α hm, ?_⟩
      rw [coe_simpleFinset hG hi]
      exact hx.2.2.1 α hm⟩
  · intro hx
    refine ⟨hx.1, fun α hα => (hx.2 α ((mem_simpleFinset hG hi).mpr hα)).1,
      fun α hα => ?_, fun α hα => False.elim (hα.2 hα.1)⟩
    have he := (hx.2 α ((mem_simpleFinset hG hi).mpr hα)).2
    rw [coe_simpleFinset hG hi] at he
    exact he

omit [LocallyOfFiniteType G.X.hom] in
/-- Under the weak increase of all upper weight cutoffs, the full-group shell is the
original characteristic region at `T`. -/
theorem characteristicShellRegion_top (T₀ Tp S : V T)
    (hS : ∀ α ∈ Δ₀, 0 ≤ ArthurRelative.weight hG hi ν D (Δ₀ : Set _) α S) :
    characteristicShellRegion hG hi D hK hρ C (⟨Δ, Subset.refl _⟩ : Idx) T₀ Tp S =
      characteristicRegion hG hi D hK hρ C T₀ Tp := by
  have he : characteristicShell hG hi D (⟨Δ, Subset.refl _⟩ : Idx) T₀ Tp S =
      characteristicChamber ν hG hi D T₀ Tp := by
    rw [characteristicShell, parabolicCharacteristicChamber_top hG hi D]
    apply Set.inter_eq_right.mpr
    intro X hX
    refine ⟨hX.1, fun α hα => ⟨(hX.2 α hα).1, ?_⟩⟩
    rw [← sub_sub, map_sub]
    exact sub_nonpos.mpr ((hX.2 α hα).2.trans (hS α hα))
  unfold characteristicShellRegion
  rw [he]
  rfl

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem continuous_linear_positiveHeight (f : V T →ₗ[ℝ] ℝ) :
    Continuous (fun a : PositiveRealTorus.intrinsicSubgroup F T => f (H₀ (positiveTorusMap F i a))) := by
  obtain ⟨v, rfl⟩ := (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_left.surjective f
  induction v using TensorProduct.inductionOn with
  | add u v hu hv =>
    refine (hu.add hv).congr fun a => ?_
    rw [map_add, LinearMap.add_apply]
    rfl
  | tmul r χ =>
    have hr : Continuous (fun _ : PositiveRealTorus.intrinsicSubgroup F T => r) := continuous_const
    refine (hr.mul ((continuous_characterLog_eval F T.toGrp χ).comp
      continuous_subtype_val)).congr fun a => ?_
    rw [show r ⊗ₜ[ℤ] χ = r • ((1 : ℝ) ⊗ₜ[ℤ] χ) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, LinearMap.smul_apply, smul_eq_mul, ← eval_eq_pair, positiveTorusMap_apply,
      eval_height_torus, realParameterPairing_tmul, one_mul]
    rfl

include hν in
/-- The actual shell is Borel on the norm-one rational quotient. In positive torus coordinates
its height set is a closed condition intersected with finitely many open root inequalities. -/
theorem measurableSet_characteristicShellRegion
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (J : Idx) (T₀ Tp S : V T) :
    MeasurableSet (characteristicShellRegion hG hi D hK hρ C J T₀ Tp S) := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨T₁, hT₁⟩ := exists_strict_lower_cutoff (i := i) (ν := ν) T₀
  let A := characteristicShell hG hi D J T₀ Tp S
  have hcut (X : V T) (hX : X ∈ A) (α : characterLattice T) (hα : α ∈ Δ) :
      0 < eval T α (X - T₁) := hT₁ X α hα (hX.2.2.1 α hα)
  let Pos := PositiveRealTorus.intrinsicSubgroup F T
  let H (a : Pos) := H₀ (positiveTorusMap F i a)
  let p : V T →ₗ[ℝ] V T := D.realCorootSpan.subtype.comp (ArthurRelative.toCorootSpan hG hi D)
  have hlin (f : V T →ₗ[ℝ] ℝ) : Continuous (fun a => f (H a)) :=
    continuous_linear_positiveHeight hi hK hρ f
  have haff (f : V T →ₗ[ℝ] ℝ) (Y : V T) : Continuous (fun a => f (H a - Y)) := by
    simp only [map_sub]
    exact (hlin f).sub continuous_const
  have hspan : IsClosed {a : Pos | H a ∈ D.realCorootSpan} := by
    have hEq : {a : Pos | H a ∈ D.realCorootSpan} =
        ⋂ m : Vstar T, {a : Pos | pair T m (H a) = pair T m (p (H a))} := by
      ext a
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro ha m
        have h : p (H a) = H a := by
          exact congrArg Subtype.val
            (ArthurRelative.toCorootSpan_apply_coe hG hi D (⟨H a, ha⟩ : D.realCorootSpan))
        rw [h]
      · intro ha
        have h : H a = p (H a) :=
          (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_right.injective
            (LinearMap.ext fun m => ha m)
        rw [h]
        exact (ArthurRelative.toCorootSpan hG hi D (H a)).2
    rw [hEq]
    exact isClosed_iInter fun m => isClosed_eq (hlin (pair T m)) (hlin ((pair T m).comp p))
  let Ac := {a : Pos | H a ∈ characteristicChamber ν hG hi D T₀ (Tp + S)} ∩
    ⋂ α : J.val, {a : Pos | ArthurRelative.weight hG hi ν D J.val α.val (H a - Tp) ≤ 0}
  have hAc : IsClosed Ac := by
    have hb : {a : Pos | H a ∈ characteristicChamber ν hG hi D T₀ (Tp + S)} =
        {a : Pos | H a ∈ D.realCorootSpan} ∩
        ⋂ α : Δ₀, {a : Pos | 0 ≤ eval T α.val (H a - T₀) ∧
          ArthurRelative.weight hG hi ν D (Δ₀ : Set (characterLattice T)) α.val
            (H a - (Tp + S)) ≤ 0} := by
      ext a
      simp only [characteristicChamber, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        Subtype.forall]
    refine IsClosed.inter ?_ (isClosed_iInter fun α => isClosed_le (haff _ _) continuous_const)
    rw [hb]
    refine hspan.inter (isClosed_iInter fun α => ?_)
    exact (isClosed_le continuous_const (haff (eval T α.val) T₀)).inter
      (isClosed_le (haff _ (Tp + S)) continuous_const)
  let O := ⋂ α : (Δ \ J.val : Set (characterLattice T)),
    {a : Pos | 0 < eval T α.val (ArthurRelative.levelProjection hG hi ν D J.val (H a - Tp))}
  let : Finite ↥(Δ \ J.val : Set (characterLattice T)) := Set.finite_coe_iff.mpr
    ((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).sdiff (t := J.val))
  have hO : IsOpen O := isOpen_iInter_of_finite fun α =>
    isOpen_lt continuous_const (haff ((eval T α.val).comp
      (ArthurRelative.levelProjection hG hi ν D J.val)) Tp)
  have hAO : H ⁻¹' A = Ac ∩ O := by
    ext a
    change (H a ∈ characteristicChamber ν hG hi D T₀ (Tp + S) ∧
      H a ∈ parabolicCharacteristicChamber hG hi D J T₀ Tp) ↔ a ∈ Ac ∩ O
    simp only [Ac, O, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Subtype.forall]
    constructor
    · exact fun h => ⟨⟨h.1, h.2.2.2.1⟩, h.2.2.2.2⟩
    · intro h
      exact ⟨h.1.1, h.1.1.1, fun α hα => (h.1.1.2 α ((mem_simpleFinset hG hi).mpr hα)).1,
        h.1.2, h.2⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.isSplitSubtorus.1
  let : Fintype I := Fintype.ofFinite I
  let : LocallyCompactSpace Pos := PositiveRealTorus.positiveLocallyCompactSpace F T I e
  let : SecondCountableTopology Pos := PositiveRealTorus.positiveSecondCountableTopology F T I e
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let : SecondCountableTopology O := TopologicalSpace.secondCountableTopology_induced _ Pos Subtype.val
  obtain ⟨B, hB, hBu⟩ := (isSigmaCompact_iff_sigmaCompactSpace.2 (inferInstance : SigmaCompactSpace O))
  let Dn (n : ℕ) := Ac ∩ B n
  have hDn (n : ℕ) : IsCompact (Dn n) := (hB n).inter_left hAc
  have hDnu : (⋃ n, Dn n) = H ⁻¹' A := by rw [hAO, ← inter_iUnion, hBu]
  let prod (s : Set Pos) := productSet F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) s
  have hp : siegelSet hi hK hρ C Δ₀ T₁ ∩ H₀ ⁻¹' A = prod (H ⁻¹' A) := by
    ext g
    constructor
    · rintro ⟨hg, hA⟩
      obtain ⟨n, hn, m, hm, a, -, k, hk, rfl⟩ := (mem_siegelSet_iff hi hK hρ C Δ₀ T₁ g).mp hg
      change H₀ _ ∈ A at hA
      rw [height_siegel_product hG hi hν hK hρ n m a (hC ▸ hk)] at hA
      exact (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) _ _).mpr
        ⟨n, hn, m, hm, a, hA, k, hk, rfl⟩
    · intro hg
      obtain ⟨n, hn, m, hm, a, ha, k, hk, rfl⟩ :=
        (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) _ _).mp hg
      refine ⟨(mem_siegelSet_iff hi hK hρ C Δ₀ T₁ _).mpr
        ⟨n, hn, m, hm, a, fun α hα => hcut _ ha α ((mem_simpleFinset hG hi).mp hα), k, hk, rfl⟩, ?_⟩
      change H₀ (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m.val *
        positiveTorusMap F i a * k) ∈ A
      rw [height_siegel_product hG hi hν hK hρ n m a (hC ▸ hk)]
      exact ha
  have hprodUnion : prod (⋃ n, Dn n) = ⋃ n, prod (Dn n) := by
    simp only [prod, productSet, Set.image_iUnion, Set.mul_iUnion, Set.iUnion_mul]
  unfold characteristicShellRegion
  rw [normOneCharacteristicHeightImage_eq hG hi hν hK hρ C hC hcov hcut, hp, ← hDnu, hprodUnion,
    Set.preimage_iUnion, Set.image_iUnion]
  apply MeasurableSet.iUnion
  intro n
  have hn := isCompact_productSet F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T)
    (hDn n)
  exact ((isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal.isCompact_preimage hn
    |>.image (LeftCosetSpace.continuous_mk Γ)).measurableSet

include hν in
/-- Integration on the actual characteristic region at `T + S` is the sum of the actual
shell integrals when `T` satisfies the root threshold. -/
theorem exists_integral_characteristicRegion_eq_sum_shellRegions
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ : V T) :
    ∃ R > 0, ∀ (Tp S : V T), (∀ α ∈ Δ, R ≤ eval T α Tp) →
      ∀ (f : NormOneRationalQuotient F G → ℂ) (measure : Measure (NormOneRationalQuotient F G)),
        IntegrableOn f (characteristicRegion hG hi D hK hρ C T₀ (Tp + S)) measure →
        (∫ x in characteristicRegion hG hi D hK hρ C T₀ (Tp + S), f x ∂measure) =
          ∑ᶠ J : Idx, ∫ x in characteristicShellRegion hG hi D hK hρ C J T₀ Tp S, f x ∂measure := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Finite Idx := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).finite_subsets.to_subtype
  let : Fintype Idx := Fintype.ofFinite _
  obtain ⟨R, hR, hd⟩ := exists_pairwiseDisjoint_characteristicShellRegion hG hi hν D hK hρ C hC hcov T₀
  refine ⟨R, hR, fun Tp S hTp f measure hf => ?_⟩
  let regions (J : Idx) := characteristicShellRegion hG hi D hK hρ C J T₀ Tp S
  have hu := characteristicRegion_eq_iUnion_shellRegions hG hi hν D hK hρ C hC hcov T₀ Tp S
  rw [hu] at hf ⊢
  rw [finsum_eq_sum_of_fintype]
  exact integral_iUnion_fintype (s := regions)
    (fun J => measurableSet_characteristicShellRegion hG hi hν D hK hρ C hC hcov J T₀ Tp S)
    (fun J J' hne => hd Tp S hTp (mem_univ J) (mem_univ J') hne)
    (fun J => hf.mono_set (subset_iUnion regions J))

end Langlands.Global.ArthurTruncation
