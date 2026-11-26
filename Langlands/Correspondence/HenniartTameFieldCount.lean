import Langlands.Correspondence.HenniartTameOrbitCount
import Langlands.LocalFactor.Ramification.Herbrand.SlopeProof
import Langlands.Galois.Local.UnramifiedCriterionProof

/-!
# Wild inertia of a tame totally ramified extension and the fixed-point formula

For a subextension `E` of degree `m` and residue degree one whose Weil group contains wild
inertia of `K`, the Weil map identifies wild inertia of `E` with that of `K`, rescaling upper
indices by `m`. With the orbit formula over `E` this gives the fixed-point formula
`WeilTameFieldFixedPointStatement` from the Frobenius parametrization of tame fields.
-/

noncomputable section

namespace Langlands.Henniart.TameField

open Weil.Local FiniteRepresentation Clifford WildInertia TameOrbit LocalClassField
open VirtualRepresentation.LocalWeil.Ramification

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (E : FiniteIntermediateExtension K.Carrier)

/-- If wild inertia of `K` lies in the Weil group of a subextension `E` of residue degree one and
degree `m`, the relative inverse Herbrand function is multiplication by `m` on `[0, ∞)`. -/
theorem relativeHerbrandPsi_eq {m : ℕ}
    (hdeg : extensionDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = m)
    (hres : extensionResidueDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = 1)
    (hker : ∀ x : localWeilGroup K, x ∈ weilWildInertia K →
      x ∈ (intermediateWeilMap K E).toMonoidHom.range)
    {v : ℝ} (hv : 0 ≤ v) :
    Ramification.HerbrandBridge.relativeHerbrandPsi E v = (m : ℝ) * v := by
  have hW : ∀ v₀ : ℝ, 0 < v₀ → upperGroup K v₀ ≤ LocalFactor.CommonClosure.weilSubgroup K E := by
    intro v₀ hv₀ x hx
    have h1 := hker x (upperGroup_le_weilWildInertia K hv₀ hx)
    rw [intermediateWeilMap_range] at h1
    exact h1
  have he := PadicField.ramificationIndex_mul_extensionResidueDegree K (E.asPadicField (p := p))
    (intermediateEmbedding K E)
  rw [hres, mul_one, hdeg] at he
  have heK : (0 : ℝ) < K.canonicalTopologicalData.ramificationIndex := by
    exact_mod_cast K.canonicalTopologicalData.ramificationIndex_pos
  have hslope : ((LocalFactor.CommonClosure.fieldData K E).ramificationIndex /
      K.canonicalTopologicalData.ramificationIndex : ℝ) = m := by
    change (((E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex : ℕ) : ℝ) /
      _ = _
    rw [he, Nat.cast_mul, mul_div_assoc, div_self heK.ne', mul_one]
  rcases hv.eq_or_lt with h0 | hpos
  · rw [← h0, Ramification.HerbrandBridge.relativeHerbrandPsi_zero, mul_zero]
  · -- the affine formula on `[ε, v]` for every `0 < ε ≤ v`, and continuity at `0`
    have key : ∀ ε : ℝ, 0 < ε → ε ≤ v →
        Ramification.HerbrandBridge.relativeHerbrandPsi E ε =
          Ramification.HerbrandBridge.relativeHerbrandPsi E v - m * (v - ε) := by
      intro ε hε hεv
      have h := Ramification.HerbrandBridge.relativeHerbrandPsi_sub_eq_of_upperGroup_le E
        hε.le (hW ε hε) le_rfl hεv
      rw [hslope] at h
      linarith
    have hcont := (Ramification.HerbrandBridge.relativeHerbrandPsi_continuous E).tendsto 0
    rw [Ramification.HerbrandBridge.relativeHerbrandPsi_zero] at hcont
    have hlim : Filter.Tendsto (fun ε => Ramification.HerbrandBridge.relativeHerbrandPsi E ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Ramification.HerbrandBridge.relativeHerbrandPsi E v - m * (v - 0))) := by
      have h2 : Filter.Tendsto (fun ε : ℝ => Ramification.HerbrandBridge.relativeHerbrandPsi E v -
          m * (v - ε)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Ramification.HerbrandBridge.relativeHerbrandPsi E v - m * (v - 0))) := by
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        exact ((continuous_const.sub (continuous_const.mul
          (continuous_const.sub continuous_id))).tendsto 0)
      apply h2.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      exact (key ε hε.1 hε.2.le).symm
    have huniq := tendsto_nhds_unique (hcont.mono_left nhdsWithin_le_nhds) hlim
    linarith

/-- Wild inertia is closed in the Weil group. -/
theorem isClosed_weilWildInertia (F : PadicField.{uK} p) :
    IsClosed ((weilWildInertia F : Subgroup (localWeilGroup F)) : Set (localWeilGroup F)) :=
  (Subgroup.isClosed_topologicalClosure
    (⨆ (v : ℝ) (_ : 0 < v), Ramification.Padic.absoluteUpperRamificationGroup F v)).preimage
    (localProjection F).continuous

/-- Wild inertia of a finite subextension is normal in its Weil group. -/
instance weilWildInertia_normal_field : (weilWildInertia (E.asPadicField (p := p))).Normal :=
  weilWildInertia_normal _

section Tame

variable {m : ℕ}
  (hdeg : extensionDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = m)
  (hres : extensionResidueDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = 1)
  (hker : ∀ x : localWeilGroup K, x ∈ weilWildInertia K →
    x ∈ (intermediateWeilMap K E).toMonoidHom.range)

include hdeg in
/-- The degree is positive. -/
theorem degree_pos : 0 < m := hdeg ▸ extensionDegree_pos _ _ _

include hdeg hres hker in
/-- If `E` has degree `m`, residue degree one, and its Weil group contains wild inertia of `K`, then
for `v > 0` the Weil map sends `w` into the upper group of `K` of index `v` exactly when `w` lies in
the upper group of `E` of index `m v`. -/
theorem map_mem_upperGroup_iff {v : ℝ} (hv : 0 < v) (w : localWeilGroup (E.asPadicField (p := p))) :
    intermediateWeilMap K E w ∈ upperGroup K v ↔
      w ∈ upperGroup (E.asPadicField (p := p)) ((m : ℝ) * v) := by
  have h := Ramification.HerbrandBridge.intermediateWeilEquiv_mem_upperGroup_iff E (v := v)
    (by linarith) w
  rw [intermediateWeilEquiv_apply] at h
  rw [h, relativeHerbrandPsi_eq K E hdeg hres hker hv.le]

include hdeg hres hker in
/-- Under the same hypotheses, wild inertia of `E` maps into wild inertia of `K`. -/
theorem map_mem_weilWildInertia (w : localWeilGroup (E.asPadicField (p := p)))
    (hw : w ∈ weilWildInertia (E.asPadicField (p := p))) :
    intermediateWeilMap K E w ∈ weilWildInertia K := by
  have hm : (0 : ℝ) < m := by exact_mod_cast degree_pos K E hdeg
  let H : Subgroup (localInertia (E.asPadicField (p := p))) :=
    ((weilWildInertia K).comap (intermediateWeilMap K E).toMonoidHom).subgroupOf
      (localInertia (E.asPadicField (p := p)))
  have hH : IsClosed (H : Set (localInertia (E.asPadicField (p := p)))) :=
    ((isClosed_weilWildInertia K).preimage (intermediateWeilMap K E).continuous).preimage
      continuous_subtype_val
  have hle := wildIn_le_of_isClosed (E.asPadicField (p := p)) hH fun v hv y hy => by
    have h1 : (intermediateWeilMap K E) (y : localWeilGroup (E.asPadicField (p := p))) ∈
        upperGroup K (v / m) := by
      rw [map_mem_upperGroup_iff K E hdeg hres hker (div_pos hv hm), mul_div_cancel₀ _ hm.ne']
      exact hy
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_comap.mpr
      (upperGroup_le_weilWildInertia K (div_pos hv hm) h1))
  have hmem : (⟨w, weilWildInertia_le_localInertia _ hw⟩ :
      localInertia (E.asPadicField (p := p))) ∈ wildIn (E.asPadicField (p := p)) :=
    Subgroup.mem_subgroupOf.mpr hw
  exact Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp (hle hmem))

include hdeg hres hker in
/-- Under the same hypotheses, every element of wild inertia of `K` comes from wild inertia of
`E`. -/
theorem exists_weilWildInertia_preimage (x : localWeilGroup K) (hx : x ∈ weilWildInertia K) :
    ∃ w ∈ weilWildInertia (E.asPadicField (p := p)), intermediateWeilMap K E w = x := by
  have hm : (0 : ℝ) < m := by exact_mod_cast degree_pos K E hdeg
  have : T2Space (localWeilGroup K) := localWeilGroup_t2Space K
  let S := (weilWildInertia (E.asPadicField (p := p))).map (intermediateWeilMap K E).toMonoidHom
  have hS : IsClosed (S : Set (localWeilGroup K)) := by
    have hc : IsCompact ((weilWildInertia (E.asPadicField (p := p)) :
        Subgroup (localWeilGroup (E.asPadicField (p := p)))) :
        Set (localWeilGroup (E.asPadicField (p := p)))) :=
      isCompact_iff_compactSpace.mpr (compactSpace_weilWildInertia (E.asPadicField (p := p)))
    rw [Subgroup.coe_map]
    exact (hc.image (intermediateWeilMap K E).continuous).isClosed
  let H : Subgroup (localInertia K) := S.subgroupOf (localInertia K)
  have hH : IsClosed (H : Set (localInertia K)) := hS.preimage continuous_subtype_val
  have hle := wildIn_le_of_isClosed K hH fun v hv y hy => by
    obtain ⟨w, hw⟩ := hker _ (upperGroup_le_weilWildInertia K hv hy)
    have hw' : w ∈ upperGroup (E.asPadicField (p := p)) ((m : ℝ) * v) := by
      rw [← map_mem_upperGroup_iff K E hdeg hres hker hv]
      change (intermediateWeilMap K E).toMonoidHom w ∈ _
      rw [hw]
      exact hy
    exact Subgroup.mem_subgroupOf.mpr
      ⟨w, upperGroup_le_weilWildInertia (E.asPadicField (p := p)) (mul_pos hm hv) hw', hw⟩
  have hmem : (⟨x, weilWildInertia_le_localInertia K hx⟩ : localInertia K) ∈ wildIn K :=
    Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_subgroupOf.mp (hle hmem)
  exact ⟨w, hw, hwx⟩

include hdeg hres hker in
/-- Under the same hypotheses, the restriction of the Weil map to wild inertia. -/
def wildHom : weilWildInertia (E.asPadicField (p := p)) →* weilWildInertia K where
  toFun w := ⟨intermediateWeilMap K E w, map_mem_weilWildInertia K E hdeg hres hker w w.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (intermediateWeilMap K E)
    (x : localWeilGroup (E.asPadicField (p := p))) (y : localWeilGroup (E.asPadicField (p := p))))

include hdeg hres hker in
/-- The restricted Weil map is bijective on wild inertia. -/
theorem wildHom_bijective : Function.Bijective (wildHom K E hdeg hres hker) := by
  constructor
  · intro x y h
    exact Subtype.ext (intermediateWeilMap_injective K E (congrArg Subtype.val h))
  · intro x
    obtain ⟨w, hw, hwx⟩ := exists_weilWildInertia_preimage K E hdeg hres hker x x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩

include hdeg hres hker in
/-- Under the same hypotheses, wild inertia of `E` and of `K` are isomorphic topological groups
through the Weil map. -/
def wildIso : weilWildInertia (E.asPadicField (p := p)) ≃ₜ* weilWildInertia K :=
  let e := MulEquiv.ofBijective (wildHom K E hdeg hres hker) (wildHom_bijective K E hdeg hres hker)
  have hind : Topology.IsInducing e := by
    have h1 : Topology.IsInducing ((Subtype.val : weilWildInertia K → localWeilGroup K) ∘ e) := by
      have h2 : (Subtype.val : weilWildInertia K → localWeilGroup K) ∘ e =
          ⇑(intermediateWeilMap K E) ∘ (Subtype.val : weilWildInertia (E.asPadicField (p := p)) →
            localWeilGroup (E.asPadicField (p := p))) := rfl
      rw [h2]
      exact (intermediateWeilMap_isEmbedding K E).isInducing.comp Topology.IsInducing.subtypeVal
    exact (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp h1
  { e with
    continuous_toFun := hind.continuous
    continuous_invFun := (e.toEquiv.toHomeomorphOfIsInducing hind).symm.continuous }

include hdeg hres hker in
/-- The isomorphism is the Weil map. -/
@[simp] theorem wildIso_apply (w : weilWildInertia (E.asPadicField (p := p))) :
    ((wildIso K E hdeg hres hker w : weilWildInertia K) : localWeilGroup K) =
      intermediateWeilMap K E w := rfl

/-- Under the same hypotheses, wild classes of `E` regarded as wild classes of `K`. -/
abbrev fieldW : WildClasses.{uK, uW} (E.asPadicField (p := p)) → WildClasses.{uK, uW} K :=
  classMap (wildIso K E hdeg hres hker).symm

include hdeg hres hker in
/-- The transport of classes is injective. -/
theorem fieldW_injective : Function.Injective (fieldW.{uK, uW} K E hdeg hres hker) :=
  fun c c' h => by
    rw [← classMap_classMap_symm (wildIso K E hdeg hres hker) c,
      ← classMap_classMap_symm (wildIso K E hdeg hres hker) c']
    exact congrArg (classMap (wildIso K E hdeg hres hker)) h

include hdeg hres hker in
/-- The transport of classes is surjective. -/
theorem fieldW_surjective : Function.Surjective (fieldW.{uK, uW} K E hdeg hres hker) :=
  fun c => ⟨classMap (wildIso K E hdeg hres hker) c, classMap_symm_classMap _ c⟩

include hdeg hres hker in
/-- The transport of classes is equivariant along the Weil map. -/
theorem fieldW_smul (w : localWeilGroup (E.asPadicField (p := p)))
    (c : WildClasses.{uK, uW} (E.asPadicField (p := p))) :
    fieldW K E hdeg hres hker (w • c) = intermediateWeilMap K E w • fieldW K E hdeg hres hker c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change A.1.representation (MulAut.conjNormal w⁻¹ ((wildIso K E hdeg hres hker).symm n)) =
      A.1.representation ((wildIso K E hdeg hres hker).symm
        (MulAut.conjNormal (intermediateWeilMap K E w)⁻¹ n))
    congr 1
    apply (wildIso K E hdeg hres hker).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Subtype.ext
    have h := congrArg Subtype.val ((wildIso K E hdeg hres hker).apply_symm_apply n)
    rw [wildIso_apply] at h
    rw [wildIso_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply, map_mul, map_mul, h,
      map_inv, inv_inv, inv_inv]

include hdeg hres hker in
/-- Under the same hypotheses and for `v > 0`, triviality at index `m v` over `E` is triviality at
index `v` over `K`. -/
theorem wildClassTrivialAt_fieldW {v : ℝ} (hv : 0 < v)
    (c : WildClasses.{uK, uW} (E.asPadicField (p := p))) :
    wildClassTrivialAt (E.asPadicField (p := p)) ((m : ℝ) * v) c ↔
      wildClassTrivialAt K v (fieldW K E hdeg hres hker c) := by
  induction c using Quotient.inductionOn with
  | h A =>
    change WildTrivialAt (E.asPadicField (p := p)) ((m : ℝ) * v) A.1 ↔
      WildTrivialAt K v (objMap (wildIso K E hdeg hres hker).symm A).1
    constructor
    · intro h n hn
      change A.1.representation ((wildIso K E hdeg hres hker).symm n) = 1
      apply h
      rw [← map_mem_upperGroup_iff K E hdeg hres hker hv, ← wildIso_apply K E hdeg hres hker,
        ContinuousMulEquiv.apply_symm_apply]
      exact hn
    · intro h w hw
      have h1 := h (wildIso K E hdeg hres hker w) (by
        rw [wildIso_apply, map_mem_upperGroup_iff K E hdeg hres hker hv]
        exact hw)
      change A.1.representation ((wildIso K E hdeg hres hker).symm
        (wildIso K E hdeg hres hker w)) = 1 at h1
      rwa [ContinuousMulEquiv.symm_apply_apply] at h1

include hdeg hres hker in
/-- Under the same hypotheses, suppose the Weil group of `E` meets inertia of `K` in `J` and the
Weil map sends `φL` to `ψ`. A class of `E` lies in `tameOrbitClasses` for inertia of `E` with
exponents `r, 1, j` and is fixed by `φL` exactly when its transport lies in
`tameOrbitClasses K J r m j` and is fixed by `ψ`. -/
theorem mem_iff (J : OpenNormalSubgroup (localWeilGroup K))
    (hJE : (intermediateWeilMap K E).toMonoidHom.range ⊓ localInertia K = J.toSubgroup)
    (φL : localWeilGroup (E.asPadicField (p := p))) {ψ : localWeilGroup K}
    (hφL : intermediateWeilMap K E φL = ψ) (r j : ℕ)
    (c : WildClasses.{uK, uW} (E.asPadicField (p := p))) :
    (c ∈ tameOrbitClasses.{uK, uW} (E.asPadicField (p := p))
        (localInertia (E.asPadicField (p := p))) r 1 j ∧ φL • c = c) ↔
      (fieldW K E hdeg hres hker c ∈ tameOrbitClasses.{uK, uW} K J.toSubgroup r m j ∧
        ψ • fieldW K E hdeg hres hker c = fieldW K E hdeg hres hker c) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast degree_pos K E hdeg
  have hp : p.Prime := Fact.out
  have hfix : (∀ g ∈ localInertia (E.asPadicField (p := p)), g • c = c) ↔
      (∀ x ∈ J.toSubgroup, x • fieldW K E hdeg hres hker c = fieldW K E hdeg hres hker c) := by
    constructor
    · intro h x hx
      rw [← hJE] at hx
      obtain ⟨⟨w, hw⟩, hxI⟩ := hx
      have hw' : intermediateWeilMap K E w = x := hw
      have hwI : w ∈ localInertia (E.asPadicField (p := p)) :=
        (intermediateWeilMap_mem_localInertia K E w).mp (hw' ▸ hxI)
      rw [← hw', ← fieldW_smul, h w hwI]
    · intro h g hg
      apply fieldW_injective K E hdeg hres hker
      rw [fieldW_smul]
      apply h
      rw [← hJE]
      exact ⟨⟨g, rfl⟩, (intermediateWeilMap_mem_localInertia K E g).mpr hg⟩
  have hpr : (0 : ℝ) < ((p ^ r : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos r
  have hkey : ∀ v : ℝ, (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < v ↔
      (j : ℝ) / ((p ^ r * 1 : ℕ) : ℝ) < m * v := by
    intro v
    have h1 : ((p ^ r * m : ℕ) : ℝ) = ((p ^ r : ℕ) : ℝ) * m := by push_cast; ring
    have h2 : ((p ^ r * 1 : ℕ) : ℝ) = ((p ^ r : ℕ) : ℝ) := by push_cast; ring
    rw [h1, h2, div_lt_iff₀ (mul_pos hpr hm), div_lt_iff₀ hpr]
    constructor <;> intro h <;> nlinarith
  have htriv : (∀ v : ℝ, (j : ℝ) / ((p ^ r * 1 : ℕ) : ℝ) < v →
        wildClassTrivialAt (E.asPadicField (p := p)) v c) ↔
      (∀ v : ℝ, (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < v →
        wildClassTrivialAt K v (fieldW K E hdeg hres hker c)) := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) := by positivity
    constructor
    · intro h v hv
      have hv0 : 0 < v := lt_of_le_of_lt hj0 hv
      exact (wildClassTrivialAt_fieldW K E hdeg hres hker hv0 c).mp (h _ ((hkey v).mp hv))
    · intro h vL hvL
      have hv : (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < vL / m := by
        rw [hkey, mul_div_cancel₀ _ hm.ne']
        exact hvL
      have hv0 : 0 < vL / m := lt_of_le_of_lt hj0 hv
      have h1 := (wildClassTrivialAt_fieldW K E hdeg hres hker hv0 c).mpr (h _ hv)
      rwa [mul_div_cancel₀ _ hm.ne'] at h1
  have hφ : φL • c = c ↔ ψ • fieldW K E hdeg hres hker c = fieldW K E hdeg hres hker c := by
    rw [← hφL, ← fieldW_smul]
    exact (fieldW_injective K E hdeg hres hker).eq_iff.symm
  have hrank : openKernelIrreducibleRank _ (fieldW K E hdeg hres hker c) =
      openKernelIrreducibleRank _ c := rank_classMap _ c
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨hfix.mp h1, hrank ▸ h2, htriv.mp h3⟩, hφ.mp h4⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨hfix.mpr h1, hrank ▸ h2, htriv.mpr h3⟩, hφ.mpr h4⟩

end Tame

/-- Inertia as an open normal subgroup of the Weil group. -/
def inertiaOpenNormal (F : PadicField.{uK} p) : OpenNormalSubgroup (localWeilGroup F) where
  toSubgroup := localInertia F
  isOpen' := localInertia_isOpen F
  isNormal' := localInertia_normal F

/-- **Fixed-point formula** for one subextension `E` of degree `m` prime to `p` and residue
degree one, whose Weil group meets inertia of `K` in `J` (of index `m` in inertia), and an element
`ψ` of degree one of the Weil group of `K` in the image of the Weil group of `E`. The Frobenius
parametrization is used over `E`. -/
theorem fixed_count (hpar : TameWeilFrobeniusParametrizationStatement.{uK}) {m : ℕ}
    (hm : ¬ p ∣ m)
    (hdeg : extensionDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = m)
    (hres : extensionResidueDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = 1)
    (J : OpenNormalSubgroup (localWeilGroup K))
    (hJm : (J.toSubgroup.subgroupOf (localInertia K)).index = m)
    (hJE : (intermediateWeilMap K E).toMonoidHom.range ⊓ localInertia K = J.toSubgroup)
    (ψ : localWeilGroup K) (hψ : ψ ∈ (intermediateWeilMap K E).toMonoidHom.range)
    (hψdeg : localDegreeInt K ψ = 1) (r j : ℕ) :
    Numerical.weilConductorCount.{uK, uW} (E.asPadicField (p := p)) (p ^ r - 1) j =
      ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) *
        {c ∈ tameOrbitClasses.{uK, uW} K J.toSubgroup r m j | ψ • c = c}.encard := by
  have hp : p.Prime := Fact.out
  have hker : ∀ x : localWeilGroup K, x ∈ weilWildInertia K →
      x ∈ (intermediateWeilMap K E).toMonoidHom.range := by
    intro x hx
    let J' := J.toSubgroup.subgroupOf (localInertia K)
    have : J'.Normal := Subgroup.Normal.subgroupOf J.isNormal' _
    have hJo : IsOpen (J' : Set (localInertia K)) := J.isOpen'.preimage continuous_subtype_val
    have hcop : Nat.Coprime J'.index p := by
      rw [hJm]
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    have hNJ := wildIn_le_of_coprime K J' hJo hcop
    have hxJ : x ∈ J.toSubgroup := Subgroup.mem_subgroupOf.mp
      (hNJ (Subgroup.mem_subgroupOf.mpr hx :
        (⟨x, weilWildInertia_le_localInertia K hx⟩ : localInertia K) ∈ wildIn K))
    rw [← hJE] at hxJ
    exact hxJ.1
  obtain ⟨φL, hφL⟩ := hψ
  have hφL' : intermediateWeilMap K E φL = ψ := hφL
  have hφLdeg : localDegreeInt (E.asPadicField (p := p)) φL = 1 := by
    have h := intermediateWeilEquiv_degree K E φL
    rw [intermediateWeilEquiv_apply, hres, Nat.cast_one, one_mul, hφL'] at h
    rw [← h, hψdeg]
  have hJL : ((inertiaOpenNormal (E.asPadicField (p := p))).toSubgroup.subgroupOf
      (localInertia (E.asPadicField (p := p)))).index = 1 := by
    change ((localInertia (E.asPadicField (p := p))).subgroupOf
      (localInertia (E.asPadicField (p := p)))).index = 1
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
  have horbit := TameOrbit.orbitFormula.{uK, uW} (E.asPadicField (p := p)) φL hφLdeg
    (fun d hd => exists_index_of_parametrization (E.asPadicField (p := p)) hpar φL hφLdeg d hd)
    (inertiaOpenNormal (E.asPadicField (p := p))) le_rfl (r := r) (j := j) hp.not_dvd_one hJL
  rw [mul_one] at horbit
  rw [horbit]
  have hq : (E.asPadicField (p := p)).canonicalTopologicalData.residueCardinality =
      K.canonicalTopologicalData.residueCardinality := by
    rw [extensionResidueCardinality K (E.asPadicField (p := p)) (intermediateEmbedding K E), hres,
      pow_one]
  rw [hq]
  congr 1
  -- orbits of `E` are singletons
  let SL := {c ∈ tameOrbitClasses.{uK, uW} (E.asPadicField (p := p))
    (localInertia (E.asPadicField (p := p))) r 1 j | φL • c = c}
  have hfixL : ∀ c ∈ tameOrbitClasses.{uK, uW} (E.asPadicField (p := p))
      (localInertia (E.asPadicField (p := p))) r 1 j,
      ∀ h : localInertia (E.asPadicField (p := p)), h • c = c :=
    fun c hc h => hc.1 h h.2
  have hA : frobeniusStableTameOrbits.{uK, uW} (E.asPadicField (p := p))
      (inertiaOpenNormal (E.asPadicField (p := p))).toSubgroup r 1 j φL =
      (fun c => (Quotient.mk'' c : MulAction.orbitRel.Quotient
        (localInertia (E.asPadicField (p := p))) (WildClasses.{uK, uW} (E.asPadicField (p := p)))))
        '' SL := by
    ext o
    constructor
    · rintro ⟨c, hc, rfl, hst⟩
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      obtain ⟨h, hh⟩ := Quotient.exact hst
      rw [← hh]
      exact hfixL c hc h
    · rintro ⟨c, ⟨hc, hφc⟩, rfl⟩
      exact ⟨c, hc, rfl, by rw [hφc]⟩
  have hinjA : Set.InjOn (fun c => (Quotient.mk'' c : MulAction.orbitRel.Quotient
      (localInertia (E.asPadicField (p := p))) (WildClasses.{uK, uW} (E.asPadicField (p := p)))))
      SL := by
    intro c hc c' hc' h
    obtain ⟨u, hu⟩ := Quotient.exact h
    rw [← hu]
    exact hfixL c' hc'.1 u
  have hB : {c ∈ tameOrbitClasses.{uK, uW} K J.toSubgroup r m j | ψ • c = c} =
      fieldW K E hdeg hres hker '' SL := by
    ext c'
    constructor
    · intro hc'
      obtain ⟨c, rfl⟩ := fieldW_surjective K E hdeg hres hker c'
      exact ⟨c, (mem_iff K E hdeg hres hker J hJE φL hφL' r j c).mpr hc', rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact (mem_iff K E hdeg hres hker J hJE φL hφL' r j c).mp hc
  rw [hA, hinjA.encard_image, hB, (fieldW_injective K E hdeg hres hker).injOn.encard_image]

end Langlands.Henniart.TameField

namespace Langlands.Henniart

/-- The fixed-point formula follows from the Frobenius parametrization of tame fields. -/
theorem weilTameFieldFixedPoint_of_parametrization
    (hpar : TameWeilFrobeniusParametrizationStatement.{uK}) :
    WeilTameFieldFixedPointStatement.{uK, uW} := by
  intro p _ K r m j hm φ hφ D g
  have h2 := D.inertiaIntersection (QuotientGroup.mk g)
  have h3 := D.frobenius_mem g
  have h1 := (D.fieldEquiv (QuotientGroup.mk g)).2
  have hJm : (D.kernel.toSubgroup.subgroupOf (Weil.Local.localInertia K)).index = m := by
    change Nat.card (Weil.Local.localInertia K ⧸ _) = m
    rw [← Nat.card_congr D.cosetEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hψdeg : Weil.Local.localDegreeInt K ((g : Weil.Local.localWeilGroup K) * φ) = 1 := by
    have hg : Weil.Local.localDegree K (g : Weil.Local.localWeilGroup K) = 1 := g.2
    unfold Weil.Local.localDegreeInt at hφ ⊢
    rw [map_mul, hg, one_mul]
    exact hφ
  generalize D.fieldEquiv (QuotientGroup.mk g) = Eb at h1 h2 h3 ⊢
  obtain ⟨E, hE⟩ := Eb
  exact TameField.fixed_count K E hpar hm hE.1 hE.2.1 D.kernel hJm h2 _ h3 hψdeg r j

end Langlands.Henniart
