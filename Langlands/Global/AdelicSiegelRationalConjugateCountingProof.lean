import Langlands.Global.AdelicSiegelRationalConjugateCountingStatement
import Langlands.Global.AdelicSiegelArchimedeanCell
import Langlands.Analysis.HaarPacking
import Langlands.Analysis.Local.SiegelSetMeasure
import Langlands.Global.AdelicSplitCentreUnitaryCharacter
import Langlands.Global.AdelicGroupPolish

/-! # Proof of the sharp Siegel count of rational points in conjugates of compact sets

`siegelRationalConjugateCounting` proves `SiegelRationalConjugateCountingStatement`: for a point
`x` of a Siegel set with torus coordinate `a` and a compact `E ⊆ G(𝔸)`, the set
`G(F) ∩ x E x⁻¹` is finite with at most `B δ(a)` elements. The count is bounded by packing
(`HaarPacking.finite_inter_and_ncard_mul_le`) by the volume of a chamber conjugate
`a E₁ a⁻¹ W'`, and `exists_measure_conj_mul_le` bounds that volume by `C₀ δ(a)` using the
archimedean open cell (`exists_siegel_archimedeanCell`), the fibre bound
`HaarPacking.measure_mul_mul_le` for the closed subgroup `N(𝔸)` and the Haar modulus of `N(𝔸)`
(`positiveTorusUnipotentModulus_of_coordinates`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

section Volume

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- The Haar modulus of conjugation by a positive torus point on `N(𝔸)` is `δ(a)`. -/
theorem mulEquivHaarChar_normalizerConj_positiveMap (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    letI : LocallyCompactSpace (standardUnipotentImage F G T i ν) :=
      (isClosed_standardUnipotentImage F G T i ν).locallyCompactSpace
    mulEquivHaarChar (HaarModulus.normalizerConj (standardUnipotentImage F G T i ν)
        ⟨positiveMap F G T i T₀ j a, positiveMap_mem_normalizer F G T i ν T₀ j a⟩) =
      siegelModulusNN (i := i) (ν := ν) (j := j) a := by
  rw [← SiegelSetMeasure.coe_closedNormalizerCharacter]
  exact positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates F G hG T
    i ν T₀ j hsetup a

section Generic

variable {Γ : Type*} [Group Γ]

/-- If every point of `W₀` is `n q` with `n ∈ N` and `p q p⁻¹ ∈ Q`, and finitely many left
translates `g⁻¹ W₀` (`g ∈ s`) cover `E`, then `p E p⁻¹ W'` is covered by the translates of
`(p N p⁻¹) Q W'` by `p g⁻¹ p⁻¹`. -/
theorem conj_image_mul_subset_biUnion (p : Γ) {E W' W₀ N Q : Set Γ} {s : Finset Γ}
    (hs : E ⊆ ⋃ g ∈ s, (g * ·) ⁻¹' W₀)
    (hcell : ∀ w ∈ W₀, ∃ n ∈ N, p * (n⁻¹ * w) * p⁻¹ ∈ Q) :
    (fun y => p * y * p⁻¹) '' E * W' ⊆
      ⋃ g ∈ s, (p * g⁻¹ * p⁻¹) • ((fun y => p * y * p⁻¹) '' N * (Q * W')) := by
  rintro _ ⟨_, ⟨e, he, rfl⟩, w', hw', rfl⟩
  obtain ⟨g, hg, hge⟩ := Set.mem_iUnion₂.mp (hs he)
  obtain ⟨n, hn, hq⟩ := hcell (g * e) hge
  refine Set.mem_iUnion₂.mpr ⟨g, hg, ?_⟩
  refine ⟨p * n * p⁻¹ * ((p * (n⁻¹ * (g * e)) * p⁻¹) * w'),
    Set.mul_mem_mul ⟨n, hn, rfl⟩ (Set.mul_mem_mul hq hw'), ?_⟩
  simp only [smul_eq_mul]
  group

/-- The preimage under a multiplicative equivalence of `ψ(A) V` is `A ψ⁻¹(V)`. -/
theorem preimage_image_mul {H : Type*} [Group H] (ψ : H ≃* H) (A V : Set H) :
    ψ ⁻¹' (ψ '' A * V) = A * ψ ⁻¹' V := by
  ext u
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, v, hv, huv⟩
    refine ⟨x, hx, ψ.symm v, ?_, ?_⟩
    · change ψ (ψ.symm v) ∈ V
      rw [ψ.apply_symm_apply]
      exact hv
    · apply ψ.injective
      rw [map_mul, ψ.apply_symm_apply]
      exact huv
  · rintro ⟨x, hx, v, hv, rfl⟩
    exact ⟨ψ x, ⟨x, hx, rfl⟩, ψ v, hv, (map_mul ψ x v).symm⟩

/-- Haar measure of `φ(A) V` for a topological group automorphism `φ`: it is at most
`mulEquivHaarChar φ` times the measure of `A V''` whenever `φ⁻¹(V) ⊆ V''`. -/
theorem measure_image_mul_le {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] (νH : Measure H)
    [νH.IsHaarMeasure] [νH.Regular] (φ : H ≃ₜ* H) (A V V'' : Set H) (hV : φ ⁻¹' V ⊆ V'') :
    νH (φ '' A * V) ≤ (mulEquivHaarChar φ : ℝ≥0∞) * νH (A * V'') := by
  have key := mulEquivHaarChar_smul_preimage νH (X := φ '' A * V) φ
  have hpre := preimage_image_mul (φ : H ≃* H) A V
  change φ ⁻¹' (φ '' A * V) = A * φ ⁻¹' V at hpre
  rw [← key, hpre, ENNReal.smul_def, smul_eq_mul]
  gcongr

end Generic

/-- **Volume of chamber conjugates.** For compact `E₁, W' ⊆ G(𝔸)` there is `C₀ < ∞` with
`vol(a E₁ a⁻¹ W') ≤ C₀ δ(a)` for every point `a` of the weak simple-root chamber. -/
theorem exists_measure_conj_mul_le (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ)
    {E₁ W' : Set (AdelicGroupPoints F G)} (hE₁ : IsCompact E₁) (hW' : IsCompact W') :
    ∃ C₀ : ℝ≥0∞, C₀ ≠ ∞ ∧
      ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t,
        (Measure.haar : Measure (AdelicGroupPoints F G))
            ((fun y => positiveMap F G T i T₀ j a * y * (positiveMap F G T i T₀ j a)⁻¹) '' E₁ *
              W') ≤
          C₀ * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) := by
  classical
  obtain ⟨hTmax, hgen, -⟩ := id hsetup
  obtain ⟨W₀, hW₀, N₁, hN₁, Q, hQ, hcell⟩ := exists_siegel_archimedeanCell hG hsetup t
  set vol : Measure (AdelicGroupPoints F G) := Measure.haar with hvol
  set H := standardUnipotentImage F G T i ν with hHdef
  have hH : IsClosed (H : Set (AdelicGroupPoints F G)) := isClosed_standardUnipotentImage F G T i ν
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set (AdelicGroupPoints F G)))
  set νH : Measure H := Measure.haar with hνH
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have : νH.Regular := Measure.regular_of_isMulLeftInvariant K₀.isCompact
    K₀.interior_nonempty K₀.isCompact.measure_lt_top.ne
  have hclN := Standard.isClosedSubgroup_unipotentHom i ν ∅
  have : IsAffineHom (Standard.unipotentScheme i ν ∅).X.hom := hclN.isAffineHom
  have : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i ν ∅).X.hom
  set mN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) with hmN
  have hmNemb : IsClosedEmbedding mN := isClosedEmbedding_map_of_isClosedSubgroup F _ hclN
  -- the finite cover of `E₁`
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hE₁
    ⟨1, mem_interior_iff_mem_nhds.mpr hW₀⟩
  -- a compact identity neighbourhood of `H` and its chamber conjugates
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : H)
  have hΩV : IsCompact (mN ⁻¹' (Subtype.val '' V)) :=
    hmNemb.isCompact_preimage (hVc.image continuous_subtype_val)
  obtain ⟨Kc, hKc, hcon⟩ := exists_isCompact_conj_unipotent_of_generic i ν j hG hTmax hgen _ hΩV t
  set V'' : Set H := Subtype.val ⁻¹' Kc with hV''
  have hV''c : IsCompact V'' := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  -- the unipotent factors as a compact subset of `H`
  let f : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) → H := fun n => ⟨mN n, n, rfl⟩
  have hf : Continuous f := mN.continuous.subtype_mk _
  set N₁' : Set H := f '' N₁ with hN₁'
  have hN₁'c : IsCompact N₁' := hN₁.image hf
  set B₀ : Set (AdelicGroupPoints F G) := Q * W' with hB₀
  have hB₀c : IsCompact B₀ := hQ.mul hW'
  set D : Set (AdelicGroupPoints F G) := (Subtype.val '' V)⁻¹ * B₀ with hD
  have hDc : IsCompact D := (hVc.image continuous_subtype_val).inv.mul hB₀c
  have hV0 : νH V ≠ 0 := (Measure.measure_pos_of_mem_nhds νH hV1).ne'
  have hVtop : νH V ≠ ∞ := hVc.measure_lt_top.ne
  refine ⟨s.card * (νH (N₁' * V'') * vol D / νH V), ?_, fun a ha => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.div_ne_top ?_ hV0)
    exact ENNReal.mul_ne_top ((hN₁'c.mul hV''c).measure_lt_top.ne) hDc.measure_lt_top.ne
  set pa := positiveMap F G T i T₀ j a with hpa
  have hnorm : pa ∈ Subgroup.normalizer (H : Set (AdelicGroupPoints F G)) :=
    positiveMap_mem_normalizer F G T i ν T₀ j a
  set ψ := HaarModulus.normalizerConj H ⟨pa, hnorm⟩ with hψ
  set X : Set H := ψ '' N₁' with hX
  have hXc : IsCompact X := hN₁'c.image ψ.continuous
  -- step 1: covering
  have himg : (fun y => pa * y * pa⁻¹) '' (mN '' N₁) = Subtype.val '' X := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨ψ (f n), ⟨f n, ⟨n, hn, rfl⟩, rfl⟩, HaarModulus.normalizerConj_apply H ⟨pa, hnorm⟩ (f n)⟩
    · rintro ⟨_, ⟨_, ⟨n, hn, rfl⟩, rfl⟩, rfl⟩
      exact ⟨mN n, ⟨n, hn, rfl⟩, (HaarModulus.normalizerConj_apply H ⟨pa, hnorm⟩ (f n)).symm⟩
  have hcover : (fun y => pa * y * pa⁻¹) '' E₁ * W' ⊆
      ⋃ g ∈ s, (pa * g⁻¹ * pa⁻¹) • ((Subtype.val '' X) * B₀) := by
    rw [← himg]
    refine conj_image_mul_subset_biUnion pa hs fun w hw => ?_
    obtain ⟨n, hn, hq⟩ := hcell w hw
    exact ⟨mN n, ⟨n, hn, rfl⟩, hq a ha⟩
  -- step 2: sum over the cover
  have hstep2 : vol ((fun y => pa * y * pa⁻¹) '' E₁ * W') ≤
      s.card * vol ((Subtype.val '' X) * B₀) := by
    calc vol ((fun y => pa * y * pa⁻¹) '' E₁ * W')
        ≤ vol (⋃ g ∈ s, (pa * g⁻¹ * pa⁻¹) • ((Subtype.val '' X) * B₀)) := measure_mono hcover
      _ ≤ ∑ g ∈ s, vol ((pa * g⁻¹ * pa⁻¹) • ((Subtype.val '' X) * B₀)) :=
          measure_biUnion_finset_le _ _
      _ = s.card * vol ((Subtype.val '' X) * B₀) := by
          simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
  -- step 3: the fibre bound
  have hstep3 := HaarPacking.measure_mul_mul_le H vol νH (X := X) (V := V) (B := B₀)
    ((hXc.mul hVc).isClosed.measurableSet) hDc.isClosed.measurableSet
  -- step 4: the Haar modulus
  have hsub : ψ ⁻¹' V ⊆ V'' := by
    intro u hu
    have hu' : ψ u ∈ V := hu
    obtain ⟨n', hn'⟩ := (ψ u).2
    have hmem : n' ∈ mN ⁻¹' (Subtype.val '' V) := ⟨ψ u, hu', hn'.symm⟩
    have h := hcon n' hmem a ha
    have hval : ((ψ u : H) : AdelicGroupPoints F G) = pa * u * pa⁻¹ :=
      HaarModulus.normalizerConj_apply H ⟨pa, hnorm⟩ u
    change (u : AdelicGroupPoints F G) ∈ Kc
    have : (u : AdelicGroupPoints F G) = pa⁻¹ * mN n' * pa := by
      rw [show mN n' = ((ψ u : H) : AdelicGroupPoints F G) from hn', hval]
      group
    rw [this]
    exact h
  have hmod : νH (X * V) ≤ (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
      νH (N₁' * V'') := by
    have hc : mulEquivHaarChar ψ = siegelModulusNN (i := i) (ν := ν) (j := j) a :=
      mulEquivHaarChar_normalizerConj_positiveMap hG hsetup a
    rw [← hc]
    exact measure_image_mul_le νH ψ N₁' V V'' hsub
  -- combine
  have hfin : vol ((Subtype.val '' X) * B₀) ≤ νH (X * V) * vol D / νH V :=
    (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)).mpr hstep3
  calc vol ((fun y => pa * y * pa⁻¹) '' E₁ * W')
      ≤ s.card * vol ((Subtype.val '' X) * B₀) := hstep2
    _ ≤ s.card * (νH (X * V) * vol D / νH V) := by gcongr
    _ ≤ s.card * ((siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
          νH (N₁' * V'') * vol D / νH V) := by gcongr
    _ = s.card * (νH (N₁' * V'') * vol D / νH V) *
          (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        ring

end Volume

/-- **The sharp Siegel count of rational points in conjugates of compact sets.** The proof is
explained in the Markdown page of this module. -/
theorem siegelRationalConjugateCounting : SiegelRationalConjugateCountingStatement := by
  intro F _ _ G _ _ _ hG T i ν T₀ j hsetup C t Ω hΩ E hE
  classical
  set vol : Measure (AdelicGroupPoints F G) := Measure.haar with hvol
  set Γ := rationalSubgroup F G with hΓ
  -- an identity neighbourhood meeting `Γ` only in `1`
  have hd : DiscreteTopology Γ :=
    SetLike.isDiscrete_iff_discreteTopology.mp (isDiscrete_rationalSubgroup F G)
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have hO1 : (1 : AdelicGroupPoints F G) ∈ O := by
    have h1 : (1 : Γ) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      rfl
    exact h1
  have hsepO : ∀ r ∈ Γ, r ∈ O → r = 1 := by
    intro r hg hgO
    have h1 : (⟨r, hg⟩ : Γ) ∈ Subtype.val ⁻¹' O := hgO
    rw [hOeq] at h1
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp h1)
  -- the packing neighbourhood
  obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_mul_subset (hOopen.mem_nhds hO1)
  have hV₂o : IsOpen (V₁ ∩ V₁⁻¹) := hV₁o.inter hV₁o.inv
  have hV₂1 : (1 : AdelicGroupPoints F G) ∈ V₁ ∩ V₁⁻¹ :=
    ⟨hV₁1, by rw [Set.mem_inv, inv_one]; exact hV₁1⟩
  obtain ⟨Wp, hWpc, hWp1, hWpV⟩ := exists_compact_subset hV₂o hV₂1
  have hsep : ∀ r ∈ Γ, r ∈ Wp * Wp⁻¹ → r = 1 := by
    intro r hg hmem
    apply hsepO r hg
    apply hV₁
    obtain ⟨x, hx, y, hy, rfl⟩ := hmem
    refine Set.mul_mem_mul (hWpV hx).1 ?_
    have hy' : y⁻¹ ∈ V₁⁻¹ := (hWpV (Set.mem_inv.mp hy)).2
    rwa [Set.mem_inv, inv_inv] at hy'
  have hWpm : MeasurableSet Wp := hWpc.isClosed.measurableSet
  have hW0 : vol Wp ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds vol (mem_interior_iff_mem_nhds.mp hWp1)).ne'
  -- the compact sets of the volume bound
  set mN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) with hmN
  set mM := fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
    map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m with hmM
  set D : Set (AdelicGroupPoints F G) := mN '' C.omegaN * mM '' C.omegaM with hD
  have hDc : IsCompact D := (C.compact_omegaN.image mN.continuous).mul
    (C.compact_omegaM.image ((map F _ G _).continuous.comp continuous_subtype_val))
  set W' : Set (AdelicGroupPoints F G) := D⁻¹ * Wp with hW'
  have hW'c : IsCompact W' := hDc.inv.mul hWpc
  set KΩ : Set (AdelicGroupPoints F G) := (C.compactSubgroup : Set _) * Ω with hKΩ
  have hKΩc : IsCompact KΩ := C.compact_compactSubgroup.mul hΩ
  set E₁ : Set (AdelicGroupPoints F G) := KΩ * E * KΩ⁻¹ with hE₁
  have hE₁c : IsCompact E₁ := (hKΩc.mul hE).mul hKΩc.inv
  obtain ⟨C₀, hC₀, hvolb⟩ := exists_measure_conj_mul_le hG hsetup t hE₁c hW'c
  refine ⟨(C₀ / vol Wp).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a x hx
  obtain ⟨z, hz, n, hn, m, hm, ha, k, hk, w, hw, rfl⟩ := hx
  intro P
  set pa := positiveMap F G T i T₀ j a with hpa
  set p := mN n * mM m with hp
  set Z : Set (AdelicGroupPoints F G) :=
    (fun y => p * y * p⁻¹) '' ((fun y => pa * y * pa⁻¹) '' E₁) with hZ
  have hzc : ∀ y : AdelicGroupPoints F G, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp (RestrictionSplitCentre.canonicalSubgroup_le_center F G hz) y).symm
  -- rational points of `x E x⁻¹` lie in `Γ ∩ Z`
  have hPZ : P ⊆ (Γ : Set (AdelicGroupPoints F G)) ∩ Z := by
    rintro r ⟨hg, e, he, rfl⟩
    refine ⟨hg, ?_⟩
    set Y := (mN n * mM m * pa * k) * w with hY
    have hxe : z * (mN n * mM m * pa * k) * w * e * (z * (mN n * mM m * pa * k) * w)⁻¹ =
        z * (Y * e * Y⁻¹) * z⁻¹ := by
      rw [hY]
      group
    have hY' : Y * e * Y⁻¹ = p * (pa * ((k * w) * e * (k * w)⁻¹) * pa⁻¹) * p⁻¹ := by
      rw [hY, hp]
      group
    refine ⟨pa * ((k * w) * e * (k * w)⁻¹) * pa⁻¹, ⟨(k * w) * e * (k * w)⁻¹,
      Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hk hw) he)
        (Set.inv_mem_inv.mpr (Set.mul_mem_mul hk hw)), rfl⟩, ?_⟩
    have key : z * (mN n * mM m * pa * k) * w * e * (z * (mN n * mM m * pa * k) * w)⁻¹ =
        p * (pa * ((k * w) * e * (k * w)⁻¹) * pa⁻¹) * p⁻¹ := by
      rw [hxe, hzc (Y * e * Y⁻¹), mul_inv_cancel_right, hY']
    exact key.symm
  -- the volume of `Z Wp`
  have hpD : p ∈ D := Set.mul_mem_mul ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
  have hZW : Z * Wp ⊆ p • ((fun y => pa * y * pa⁻¹) '' E₁ * W') := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, w₁, hw₁, rfl⟩
    refine ⟨y * (p⁻¹ * w₁), Set.mul_mem_mul hy
      (Set.mul_mem_mul (Set.inv_mem_inv.mpr hpD) hw₁), ?_⟩
    simp only [smul_eq_mul]
    group
  have hvolZ : vol (Z * Wp) ≤ C₀ * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) :=
    calc vol (Z * Wp) ≤ vol (p • ((fun y => pa * y * pa⁻¹) '' E₁ * W')) := measure_mono hZW
      _ = vol ((fun y => pa * y * pa⁻¹) '' E₁ * W') := measure_smul _ _ _
      _ ≤ _ := hvolb a ha
  have hδtop : C₀ * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top hC₀ ENNReal.coe_ne_top
  obtain ⟨hfin, hcard⟩ := HaarPacking.finite_inter_and_ncard_mul_le vol Γ hWpm hW0 hsep Z
    (ne_top_of_le_ne_top hδtop hvolZ)
  refine ⟨hfin.subset hPZ, ?_⟩
  have hle : (((Γ : Set (AdelicGroupPoints F G)) ∩ Z).ncard : ℝ≥0∞) ≤
      C₀ / vol Wp * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) := by
    have h1 : (((Γ : Set (AdelicGroupPoints F G)) ∩ Z).ncard : ℝ≥0∞) ≤
        C₀ * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) / vol Wp :=
      (ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWpc.measure_lt_top.ne)).mpr
        (hcard.trans hvolZ)
    have h2 : C₀ * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) / vol Wp =
        C₀ / vol Wp * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) := by
      simp only [div_eq_mul_inv]
      ring
    rwa [h2] at h1
  have hPle : (P.ncard : ℝ) ≤ (((Γ : Set (AdelicGroupPoints F G)) ∩ Z).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hPZ hfin
  refine hPle.trans ?_
  have hrhs : C₀ / vol Wp * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top hC₀ hW0) ENNReal.coe_ne_top
  have h := ENNReal.toReal_mono hrhs hle
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_siegelModulusNN] at h
  simpa using h

end Langlands.Global
