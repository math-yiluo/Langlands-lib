import Langlands.Global.AdelicLeviRadicalAverageTestFunctionStatement
import Langlands.Global.AdelicCompactEnvelopingIntegral
import Langlands.Global.AdelicIwasawaIntegrationProof
import Langlands.Global.AdelicOpenIwasawaCompact
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Langlands.Analysis.Local.QuotientAutomorphismStatement
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter

/-! # Proof that radical averages of adelic test functions are test functions on the Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField IsDedekindDomain Set Filter Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]

local notation "R∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "Rf" => CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)

/-- A group-scheme point map sends a pair of infinite and finite points to the pair of their
images. -/
private theorem map_pair_eq (j : M ⟶ G) (a : InfiniteAdelicGroupPoints F M)
    (b : FiniteAdelicGroupPoints F M) :
    map F M G j (pair F M a b) =
      pair F G (M.affinePointsTarget j R∞ a) (M.affinePointsTarget j Rf b) := by
  have hi (x : AdelicGroupPoints F M) : infinite F G (map F M G j x) =
      M.affinePointsTarget j R∞ (infinite F M x) :=
    DFunLike.congr_fun (M.affinePointsTarget_naturality j (CommAlgCat.ofHom
      (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) x
  apply (split F G).injective
  simp only [split_apply, hi, finite_map, infinite_pair, finite_pair]

/-- A group-scheme point map commutes with the inclusion of the finite factor. -/
private theorem map_ofFinite_eq (j : M ⟶ G) (b : FiniteAdelicGroupPoints F M) :
    map F M G j (ofFinite F M b) = ofFinite F G (M.affinePointsTarget j Rf b) := by
  simp only [ofFinite_eq_pair, map_pair_eq, map_one]

private theorem continuous_affinePointsTarget_finite (j : M ⟶ G) :
    Continuous (M.affinePointsTarget j Rf) := by
  have h (b : FiniteAdelicGroupPoints F M) :
      M.affinePointsTarget j Rf b = finite F G (map F M G j (ofFinite F M b)) := by
    rw [map_ofFinite_eq, finite_ofFinite]
  simp_rw [funext h]
  exact (finite F G).continuous.comp ((map F M G j).continuous.comp (ofFinite F M).continuous)

/-- Right multiplication of the finite component of a pair is right multiplication by the
included finite point. -/
private theorem pair_mul_ofFinite (a : InfiniteAdelicGroupPoints F G) (b c : FiniteAdelicGroupPoints F G) :
    pair F G a (b * c) = pair F G a b * ofFinite F G c := by
  rw [ofFinite_eq_pair, pair_mul, mul_one]

section Radical

variable [LocallyOfFiniteType G.X.hom] (j : M ⟶ G) (Γ : SubgroupFunctor G)
  [hclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G Γ : Set (AdelicGroupPoints F G))]

local notation "A" => AdelicGroupPoints F G
local notation "N" => AdelicSubgroupPoints.adelicPoints F G Γ

local instance radicalLocallyCompactSpace : LocallyCompactSpace N :=
  hclosed.locallyCompactSpace

/-- The radical average `m ↦ ∫_N β(u j(m)) du` for the Haar measure of `N`. -/
private def radicalAverage (β : A → ℂ) (m : AdelicGroupPoints F M) : ℂ :=
  ∫ u : N, β ((u : A) * map F M G j m) ∂(Measure.haar : Measure N)

/-- The radical points in the translates of `tsupport β` by the inverses of the images of
points in `C`. -/
private def radicalSupport (β : A → ℂ) (C : Set (AdelicGroupPoints F M)) : Set N :=
  Subtype.val ⁻¹' ((fun p : A × AdelicGroupPoints F M => p.1 * (map F M G j p.2)⁻¹) ''
    (tsupport β ×ˢ C))

variable {j Γ}

omit [IsAffine M.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isCompact_radicalSupport {β : A → ℂ} (hβ : HasCompactSupport β)
    {C : Set (AdelicGroupPoints F M)} (hC : IsCompact C) :
    IsCompact (radicalSupport j Γ β C) := by
  apply hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
  exact (hβ.isCompact.prod hC).image (continuous_fst.mul
    ((map F M G j).continuous.comp continuous_snd).inv)

omit [IsAffine G.X.left] [IsAffine M.X.left] [LocallyOfFiniteType G.X.hom] hclosed in
private theorem eq_zero_of_notMem_radicalSupport (β : A → ℂ) {C : Set (AdelicGroupPoints F M)}
    {m : AdelicGroupPoints F M} (hm : m ∈ C) {u : N} (hu : u ∉ radicalSupport j Γ β C) :
    β ((u : A) * map F M G j m) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hu
  exact ⟨((u : A) * map F M G j m, m), ⟨h, hm⟩, by simp⟩

omit [IsAffine M.X.left] in
/-- At each `m ∈ C`, the radical average equals the integral over
`radicalSupport j Γ β C`. -/
private theorem radicalAverage_eq_setIntegral (β : A → ℂ) {C : Set (AdelicGroupPoints F M)}
    {m : AdelicGroupPoints F M} (hm : m ∈ C) :
    radicalAverage j Γ β m =
      ∫ u in radicalSupport j Γ β C, β ((u : A) * map F M G j m) ∂(Measure.haar : Measure N) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hu =>
    eq_zero_of_notMem_radicalSupport β hm hu).symm

variable [LocallyOfFiniteType M.X.hom]

private theorem continuous_radicalAverage {β : A → ℂ} (hβc : Continuous β) (hβ : HasCompactSupport β) :
    Continuous (radicalAverage j Γ β) := by
  rw [continuous_iff_continuousAt]
  intro m₀
  obtain ⟨C, hC, hCm⟩ := exists_compact_mem_nhds m₀
  have hcont : Continuous fun m => ∫ u in radicalSupport j Γ β C,
      β ((u : A) * map F M G j m) ∂(Measure.haar : Measure N) :=
    continuous_parametric_integral_of_continuous
      (f := fun m (u : N) => β ((u : A) * map F M G j m))
      (hβc.comp ((continuous_subtype_val.comp continuous_snd).mul
        ((map F M G j).continuous.comp continuous_fst)))
      (isCompact_radicalSupport hβ hC)
  apply hcont.continuousAt.congr
  filter_upwards [hCm] with m hm
  exact (radicalAverage_eq_setIntegral β hm).symm

omit [LocallyOfFiniteType M.X.hom] in
/-- Right invariance under the preimage of a right-invariance group of `β`. -/
private theorem radicalAverage_mul_ofFinite {β : A → ℂ} {L : Subgroup (FiniteAdelicGroupPoints F G)}
    (hL : ∀ l ∈ L, ∀ g : A, β (g * ofFinite F G l) = β g) {l : FiniteAdelicGroupPoints F M}
    (hl : M.affinePointsTarget j Rf l ∈ L) (m : AdelicGroupPoints F M) :
    radicalAverage j Γ β (m * ofFinite F M l) = radicalAverage j Γ β m := by
  unfold radicalAverage
  congr 1
  funext u
  rw [map_mul, map_ofFinite_eq, ← mul_assoc, hL _ hl]

omit [LocallyOfFiniteType M.X.hom] in
/-- The support of the radical average lies in any compact set containing the Levi parts of the
points `u j(m)` of the support of `β`. -/
private theorem hasCompactSupport_radicalAverage {β : A → ℂ} (hβ : HasCompactSupport β)
    (hproj : ∀ C : Set A, IsCompact C → ∃ K : Set (AdelicGroupPoints F M), IsCompact K ∧
      ∀ m : AdelicGroupPoints F M, ∀ u ∈ N, u * map F M G j m ∈ C → m ∈ K) :
    HasCompactSupport (radicalAverage j Γ β) := by
  obtain ⟨K, hK, hKC⟩ := hproj _ hβ.isCompact
  refine HasCompactSupport.intro hK fun m hm => ?_
  have h0 : ∀ u : N, β ((u : A) * map F M G j m) = 0 := fun u => by
    by_contra h
    exact hm (hKC m u u.2 (subset_tsupport _ h))
  unfold radicalAverage
  simp only [h0, integral_zero]

section Conjugation

/-- Conjugation `u ↦ j(m)⁻¹ u j(m)` of the radical by a point of the Levi. -/
private def radicalConj
    (hnorm : ∀ (m : AdelicGroupPoints F M) (u : A), u ∈ N →
      (map F M G j m)⁻¹ * u * map F M G j m ∈ N)
    (m : AdelicGroupPoints F M) : N ≃ₜ* N :=
  Langlands.QuotientIntegration.subgroupAutomorphism N
    { toFun x := (map F M G j m)⁻¹ * x * map F M G j m
      invFun x := map F M G j m * x * (map F M G j m)⁻¹
      left_inv x := by simp [mul_assoc]
      right_inv x := by simp [mul_assoc]
      map_mul' x y := by simp [mul_assoc]
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }
    fun x => ⟨fun hx => by
      have h := hnorm m⁻¹ ((map F M G j m)⁻¹ * x * map F M G j m) hx
      rw [map_inv, inv_inv] at h
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h, hnorm m x⟩

omit [IsAffine M.X.left] [LocallyOfFiniteType G.X.hom] hclosed [LocallyOfFiniteType M.X.hom] in
private theorem coe_radicalConj
    (hnorm : ∀ (m : AdelicGroupPoints F M) (u : A), u ∈ N →
      (map F M G j m)⁻¹ * u * map F M G j m ∈ N)
    (m : AdelicGroupPoints F M) (u : N) :
    (radicalConj hnorm m u : A) = (map F M G j m)⁻¹ * u * map F M G j m := rfl

omit [LocallyOfFiniteType M.X.hom] in
/-- Conjugation by a point of the finite Levi whose image lies in a compact open subgroup `W`
preserves the Haar measure of the radical by preserving the compact identity neighbourhood
cut out by `W` and a compact identity neighbourhood at infinity. -/
private theorem map_radicalConj_haar
    (hnorm : ∀ (m : AdelicGroupPoints F M) (u : A), u ∈ N →
      (map F M G j m)⁻¹ * u * map F M G j m ∈ N)
    {W : Subgroup (FiniteAdelicGroupPoints F G)}
    (hWc : IsCompact (W : Set (FiniteAdelicGroupPoints F G)))
    (hWo : IsOpen (W : Set (FiniteAdelicGroupPoints F G))) {l : FiniteAdelicGroupPoints F M}
    (hl : M.affinePointsTarget j Rf l ∈ W) :
    (Measure.haar : Measure N).map (radicalConj hnorm (ofFinite F M l)) = Measure.haar := by
  obtain ⟨Kinf, hKinf, hKinf1⟩ := exists_compact_mem_nhds (1 : InfiniteAdelicGroupPoints F G)
  let K : Set N := Subtype.val ⁻¹' (split F G ⁻¹' (Kinf ×ˢ (W : Set (FiniteAdelicGroupPoints F G))))
  have hK : IsCompact K := by
    apply hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    exact (split F G).toHomeomorph.isCompact_preimage.mpr (hKinf.prod hWc)
  have hK1 : K ∈ 𝓝 (1 : N) := by
    apply continuous_subtype_val.continuousAt.preimage_mem_nhds
    apply (split F G).continuous.continuousAt.preimage_mem_nhds
    change Kinf ×ˢ (W : Set (FiniteAdelicGroupPoints F G)) ∈ 𝓝 (split F G 1)
    rw [map_one]
    exact prod_mem_nhds hKinf1 (hWo.mem_nhds W.one_mem)
  have hpos : (Measure.haar : Measure N) K ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds _ hK1).ne'
  have htop : (Measure.haar : Measure N) K ≠ ⊤ := hK.measure_lt_top.ne
  have hpre : radicalConj hnorm (ofFinite F M l) ⁻¹' K = K := by
    ext u
    simp only [K, mem_preimage, coe_radicalConj, split_apply, mem_prod, map_ofFinite_eq,
      map_mul, map_inv, infinite_ofFinite, finite_ofFinite, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_inv, Prod.snd_inv, inv_one, mul_one, one_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := W.mul_mem (W.mul_mem hl h2) (W.inv_mem hl)
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using this
    · rintro ⟨h1, h2⟩
      exact ⟨h1, W.mul_mem (W.mul_mem (W.inv_mem hl) h2) hl⟩
  have hchar : mulEquivHaarChar (radicalConj hnorm (ofFinite F M l)) = 1 := by
    have h := mulEquivHaarChar_smul_preimage (Measure.haar : Measure N) (X := K)
      (radicalConj hnorm (ofFinite F M l))
    rw [hpre, ENNReal.smul_def, smul_eq_mul, ENNReal.mul_eq_right hpos htop] at h
    exact_mod_cast h
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure N)
    (radicalConj hnorm (ofFinite F M l))
  rwa [hchar, one_smul] at h

omit [LocallyOfFiniteType M.X.hom] in
/-- Left invariance under the finite Levi points whose images lie in a left-invariance group of
`β` and in a compact open subgroup. -/
private theorem radicalAverage_ofFinite_mul
    (hnorm : ∀ (m : AdelicGroupPoints F M) (u : A), u ∈ N →
      (map F M G j m)⁻¹ * u * map F M G j m ∈ N)
    {β : A → ℂ} {L W : Subgroup (FiniteAdelicGroupPoints F G)}
    (hL : ∀ l ∈ L, ∀ g : A, β (ofFinite F G l * g) = β g)
    (hWc : IsCompact (W : Set (FiniteAdelicGroupPoints F G)))
    (hWo : IsOpen (W : Set (FiniteAdelicGroupPoints F G))) {l : FiniteAdelicGroupPoints F M}
    (hlL : M.affinePointsTarget j Rf l ∈ L) (hlW : M.affinePointsTarget j Rf l ∈ W)
    (m : AdelicGroupPoints F M) :
    radicalAverage j Γ β (ofFinite F M l * m) = radicalAverage j Γ β m := by
  let α := radicalConj hnorm (ofFinite F M l)
  have hpres : MeasurePreserving α.toHomeomorph.toMeasurableEquiv (Measure.haar : Measure N)
      Measure.haar :=
    ⟨α.toHomeomorph.toMeasurableEquiv.measurable, map_radicalConj_haar hnorm hWc hWo hlW⟩
  unfold radicalAverage
  rw [← hpres.integral_comp' (fun u : N => β ((u : A) * map F M G j m))]
  congr 1
  funext u
  change β ((u : A) * map F M G j (ofFinite F M l * m)) =
    β ((map F M G j (ofFinite F M l))⁻¹ * u * map F M G j (ofFinite F M l) * map F M G j m)
  rw [map_mul, map_ofFinite_eq, mul_assoc, mul_assoc]
  rw [← hL _ hlL ((ofFinite F G (M.affinePointsTarget j Rf l))⁻¹ * _)]
  simp only [mul_inv_cancel_left]

end Conjugation

section Slices

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "M∞" => InfiniteAdelicGroupPoints F M
local notation "Af" => FiniteAdelicGroupPoints F G

set_option backward.isDefEq.respectTransparency true in
/-- The infinite slices of a radical average are smooth. Over the compact part of the radical
used for integration near `a₀`, the finite parts of `u j(a, b)` meet finitely many cosets of the
right-invariance group `L` of `β`. The integrand is a finite sum of smooth slices of `β` at
coset representatives, weighted by the indicators of those cosets. -/
private theorem radicalAverage_slice_mem {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom)
    (hsM : SmoothOfRelativeDimension e M.X.hom) {β : A → ℂ}
    (hβs : ∀ b, functionInfiniteSlice F G β b ∈ InfinitePlotSmoothFunctions F G)
    (hβ : HasCompactSupport β) {L : Subgroup Af} (hLo : IsOpen (L : Set Af))
    (hL : ∀ l ∈ L, ∀ g : A, β (g * ofFinite F G l) = β g) (b : FiniteAdelicGroupPoints F M) :
    functionInfiniteSlice F M (radicalAverage j Γ β) b ∈ InfinitePlotSmoothFunctions F M := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsG
  let := smoothChartedSpace F M hsM
  let := smoothLieGroup F G hsG
  let : IsManifold 𝓘(ℝ, smoothModel F d) ∞ G∞ := smoothIsManifold F G hsG
  let : IsManifold 𝓘(ℝ, smoothModel F e) ∞ M∞ := smoothIsManifold F M hsM
  apply (isPlotSmooth_iff_contMDiff F M hsM _).mpr
  intro a₀
  let jinf : M∞ → G∞ := M.affinePointsTarget j R∞
  let jf := M.affinePointsTarget j Rf
  have hincl : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d) ∞ jinf := by
    apply (contMDiff_iff_coordinateSmooth F G 𝓘(ℝ, smoothModel F e) hsG _).mpr
    exact ((contMDiff_iff_coordinateSmooth F M 𝓘(ℝ, smoothModel F e) hsM id).mp
      contMDiff_id).postcomp j.hom.hom
  obtain ⟨Cinf, hCinf, hCa₀⟩ := exists_compact_mem_nhds a₀
  let C : Set (AdelicGroupPoints F M) := split F M ⁻¹' (Cinf ×ˢ {b})
  have hC : IsCompact C :=
    (split F M).toHomeomorph.isCompact_preimage.mpr (hCinf.prod isCompact_singleton)
  let S := radicalSupport j Γ β C
  have hS : IsCompact S := isCompact_radicalSupport hβ hC
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let ν := (Measure.haar : Measure N).comap (Subtype.val : S → N)
  let : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [(MeasurableEmbedding.subtype_coe hSm).comap_apply, Set.image_univ, Subtype.range_coe]
    exact hS.measure_lt_top⟩
  let : DiscreteTopology (Af ⧸ L) := QuotientGroup.discreteTopology hLo
  let κ : S → Af ⧸ L := fun x => QuotientGroup.mk (finite F G ((x : N) : A) * jf b)
  have hκ : Continuous κ := QuotientGroup.continuous_mk.comp
    (((finite F G).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const)
  let R := ((isCompact_range hκ).finite_of_discrete).toFinset
  let w (q : Af ⧸ L) : C(S, ℂ) := ⟨fun x => if κ x = q then 1 else 0,
    (continuous_of_discreteTopology (f := fun y : Af ⧸ L => if y = q then (1 : ℂ) else 0)).comp
      hκ⟩
  let jS : C(S, G∞) := ⟨fun x => infinite F G ((x : N) : A),
    (infinite F G).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩
  let h (q : Af ⧸ L) (p : M∞ × G∞) : ℂ := β (pair F G (p.2 * jinf p.1) q.out)
  have hh (q : Af ⧸ L) :
      ContMDiff (𝓘(ℝ, smoothModel F e).prod 𝓘(ℝ, smoothModel F d)) 𝓘(ℝ, ℂ) ∞ (h q) :=
    ((isPlotSmooth_iff_contMDiff F G hsG (functionInfiniteSlice F G β q.out)).mp
      (hβs q.out)).comp (contMDiff_snd.mul (hincl.comp contMDiff_fst))
  let Φ (a : M∞) : ℂ := ∑ q ∈ R, ∫ x, w q x * h q (a, jS x) ∂ν
  have hΦ : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ) ∞ Φ := by
    apply contMDiff_finsetSum
    intro q _
    simpa only [smul_eq_mul] using
      Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral ν (w q) jS
        (hh q)
  apply (hΦ a₀).congr_of_eventuallyEq
  filter_upwards [hCa₀] with a ha
  have hm : pair F M a b ∈ C := by
    simpa only [C, mem_preimage, split_apply, infinite_pair, finite_pair, mem_prod,
      mem_singleton_iff, and_true] using ha
  have hint (q : Af ⧸ L) : Integrable (fun x => w q x * h q (a, jS x)) ν :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, (w q).continuous.mul
      ((hh q).continuous.comp (continuous_const.prodMk jS.continuous))⟩).integrable ν
  have hpt (x : S) : β (((x : N) : A) * map F M G j (pair F M a b)) =
      ∑ q ∈ R, w q x * h q (a, jS x) := by
    have hxR : κ x ∈ R := by
      simp only [R, Set.Finite.mem_toFinset, Set.mem_range_self]
    simp only [w, ContinuousMap.coe_mk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      ite_eq_left hxR]
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L (finite F G ((x : N) : A) * jf b)
    change _ = β (pair F G (infinite F G ((x : N) : A) * jinf a)
      (Quotient.out (QuotientGroup.mk (finite F G ((x : N) : A) * jf b) : Af ⧸ L)))
    rw [hl, pair_mul_ofFinite, hL _ l.2, map_pair_eq, ← pair_mul, pair_projections]
  change radicalAverage j Γ β (pair F M a b) = Φ a
  calc radicalAverage j Γ β (pair F M a b)
      = ∫ x : S, β (((x : N) : A) * map F M G j (pair F M a b)) ∂ν := by
        rw [radicalAverage_eq_setIntegral β hm]
        exact (integral_subtype_comap hSm _).symm
    _ = ∫ x : S, ∑ q ∈ R, w q x * h q (a, jS x) ∂ν := by
        congr 1
        funext x
        exact hpt x
    _ = Φ a := integral_finsetSum R fun q _ => hint q

end Slices

/-- The radical average inherits the test function properties from the ambient function. -/
private theorem isAdelicTestFunction_radicalAverage {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom)
    (hsM : SmoothOfRelativeDimension e M.X.hom)
    (hnorm : ∀ (m : AdelicGroupPoints F M) (u : A), u ∈ N →
      (map F M G j m)⁻¹ * u * map F M G j m ∈ N)
    (hproj : ∀ C : Set A, IsCompact C → ∃ K : Set (AdelicGroupPoints F M), IsCompact K ∧
      ∀ m : AdelicGroupPoints F M, ∀ u ∈ N, u * map F M G j m ∈ C → m ∈ K)
    {β : A → ℂ} (hβ : IsAdelicTestFunction F G β) :
    IsAdelicTestFunction F M (radicalAverage j Γ β) := by
  obtain ⟨⟨hβc, hβs, L, hLo, hL⟩, hβk, L', hL'o, hL'⟩ := hβ
  let jf := M.affinePointsTarget j Rf
  have hjf : Continuous jf := continuous_affinePointsTarget_finite j
  let W := FiniteAdelicGroupPoints.compactOpenSubgroup F G
  have hWo : IsOpen (W : Set (FiniteAdelicGroupPoints F G)) := W.isOpen
  have hWc : IsCompact (W : Set (FiniteAdelicGroupPoints F G)) :=
    FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G
  refine ⟨⟨continuous_radicalAverage hβc hβk,
      radicalAverage_slice_mem hsG hsM hβs hβk hLo hL,
      L.comap jf, hLo.preimage hjf, ?_⟩,
    hasCompactSupport_radicalAverage hβk hproj,
    (L' ⊓ W.toSubgroup).comap jf, (hL'o.inter hWo).preimage hjf, ?_⟩
  · intro l hl m
    exact radicalAverage_mul_ofFinite hL hl m
  · intro l hl m
    exact radicalAverage_ofFinite_mul hnorm hL' hWc hWo hl.1 hl.2 m

end Radical

/-- Constant multiples of adelic test functions are adelic test functions. -/
private theorem IsAdelicTestFunction.const_mul {β : AdelicGroupPoints F G → ℂ}
    (hβ : IsAdelicTestFunction F G β) (c : ℂ) :
    IsAdelicTestFunction F G (fun g => c * β g) := by
  obtain ⟨⟨hβc, hβs, L, hLo, hL⟩, hβk, L', hL'o, hL'⟩ := hβ
  refine ⟨⟨continuous_const.mul hβc, ?_, L, hLo, ?_⟩,
    HasCompactSupport.mul_left (f := fun _ => c) hβk, L', hL'o, ?_⟩
  · intro b
    exact (InfinitePlotSmoothFunctions F G).smul_mem c (hβs b)
  · exact fun l hl g => congrArg (c * ·) (hL l hl g)
  · exact fun l hl g => congrArg (c * ·) (hL' l hl g)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The normalized radical average of an adelic test function restricts to a test function
on the Levi of a standard parabolic. -/
theorem leviRadicalAverageTestFunction : LeviRadicalAverageTestFunctionStatement.{u} := by
  intro F _ _ G _ _ _ fam J β hβ
  have : Smooth G.X.hom := fam.connectedReductive.smooth
  let j := fam.l J ≫ fam.p J
  let iU := fam.iU J ≫ fam.p J
  let Γ := SubgroupFunctor.range iU
  let N := AdelicSubgroupPoints.adelicPoints F G Γ
  let hNclosed : IsClosed (N : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G iU
  let : LocallyCompactSpace N := hNclosed.locallyCompactSpace
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ fam.a J ≫ fam.l J ≫ fam.p J
  have hP : (Dynamic.parabolic χ).IsRepresentedBy (fam.p J) :=
    ⟨IsClosedSubgroup.mono_overHom r.isCompatible.parabolic.isClosedSubgroup,
      r.parabolic_eq_splitComponentCocharacter⟩
  have hM : (Dynamic.centralizer χ).IsRepresentedBy j :=
    ⟨IsClosedSubgroup.mono_overHom (r.isCompatible.levi.isClosedSubgroup.comp
      r.isCompatible.parabolic.isClosedSubgroup), r.levi_eq_splitComponentCocharacter⟩
  have hU : (Dynamic.unipotent χ).IsRepresentedBy iU :=
    ⟨IsClosedSubgroup.mono_overHom ((fam.isUnipotentRadical J).1.isClosedSubgroup.comp
      r.isCompatible.parabolic.isClosedSubgroup), r.range_comp_radical_eq (fam.isUnipotentRadical J)⟩
  let T := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (AdeleRing (𝓞 F) F)))
  have hnorm (m : AdelicGroupPoints F (fam.M J)) (x : AdelicGroupPoints F G) (hx : x ∈ N) :
      (map F (fam.M J) G j m)⁻¹ * x * map F (fam.M J) G j m ∈ N := by
    change x ∈ Γ.carrier T at hx
    change _ ∈ Γ.carrier T
    rw [show Γ = Dynamic.unipotent χ from hU.2] at hx ⊢
    have hm : map F (fam.M J) G j m ∈ (Dynamic.centralizer χ).carrier T :=
      (mem_range_map_iff_of_isRepresentedBy F hM _).mp ⟨m, rfl⟩
    exact (Subgroup.mem_normalizer_iff''.mp
      (Dynamic.centralizer_le_normalizer_unipotent χ T hm) x).mp hx
  have hproj (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
      ∃ K : Set (AdelicGroupPoints F (fam.M J)), IsCompact K ∧
        ∀ m, ∀ x ∈ N, x * map F (fam.M J) G j m ∈ C → m ∈ K := by
    let P := (map F (fam.P J) G (fam.p J)).toMonoidHom.range
    let D : Set P := Subtype.val ⁻¹' C
    have hPclosed : IsClosed (P : Set (AdelicGroupPoints F G)) :=
      (isClosedEmbedding_map_parabolic F hP).isClosed_range
    have hD : IsCompact D := hPclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine ⟨leviProjection F hP hM '' D, hD.image (continuous_leviProjection F hP hM), ?_⟩
    intro m x hx hxC
    change x ∈ Γ.carrier T at hx
    rw [show Γ = Dynamic.unipotent χ from hU.2] at hx
    obtain ⟨v, hv⟩ := (mem_range_map_iff_of_isRepresentedBy F hU x).mpr hx
    change map F (fam.U J) G iU v = x at hv
    let q : P := leviMul F hP hM hU (1, v) * leviMul F hP hM hU (m, 1)
    refine ⟨q, ?_, ?_⟩
    · change (q : AdelicGroupPoints F G) ∈ C
      simpa only [q, Subgroup.coe_mul, coe_leviMul, map_one, one_mul, mul_one, hv] using hxC
    · simp only [q, map_mul, leviProjection_leviMul, one_mul]
  have hAvg := isAdelicTestFunction_radicalAverage fam.connectedReductive.smoothDimension_spec
    (fam.leviSmooth J) hnorm hproj hβ
  let c := AdelicSubgroupPoints.quotientMassNormalizer F G Γ
  have hscale (m : AdelicGroupPoints F (fam.M J)) :
      (∫ x : N, β ((x : AdelicGroupPoints F G) * map F (fam.M J) G j m)
        ∂AdelicSubgroupPoints.normalizedHaarMeasure F G Γ) =
      (c.toReal : ℂ) * radicalAverage j Γ β m :=
    (integral_smul_measure («μ» := (Measure.haar : Measure N))
      (fun x : N => β ((x : AdelicGroupPoints F G) * map F (fam.M J) G j m)) c).trans
      Complex.real_smul
  change IsAdelicTestFunction F (fam.M J) fun m =>
    ∫ x : N, β ((x : AdelicGroupPoints F G) * map F (fam.M J) G j m)
      ∂AdelicSubgroupPoints.normalizedHaarMeasure F G Γ
  rw [funext hscale]
  exact IsAdelicTestFunction.const_mul hAvg c.toReal

end Langlands.Global
