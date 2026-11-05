import Langlands.Representation.Jacquet.StandardCanonicalSectionStatement
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement

/-! # The uniform standard canonical Jacquet section -/

noncomputable section

universe uG uV uQ uF

namespace Langlands.Jacquet

open Langlands.BruhatTits.SpecialCompact

section UniformKernel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

private theorem average_apply_of_mem {k : G} (hk : k ∈ K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k v) = Compact.averageMap ρ hρ K hK v := by
  let τ := ρ.comp K.toSubgroup.subtype
  let k' : K.toSubgroup := ⟨k, hk⟩
  have ho : Compact.orbit τ (τ k' v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a * k', by simp [τ]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a * k'⁻¹, ?_⟩
      simp [τ, map_mul, Module.End.mul_apply]
  change Compact.orbitMean τ (τ k' v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

private theorem uniform_relations_average_zero
    (N : Subgroup G) (Ω : ℝ → Set G) (hΩ : Monotone Ω)
    (hcontain : ∀ Γ : Set N, IsCompact Γ → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ω ε, N.subtype '' Γ ⊆
        ambientConjugate t⁻¹ ((K.toSubgroup ⊓ N : Subgroup G) : Set G))
    (v : V) (hv : v ∈ relations ρ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ω ε,
      Compact.averageMap ρ hρ K hK (ρ t v) = 0 := by
  rw [relations_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨n, w⟩, rfl⟩ := hw
    obtain ⟨ε, hε, hεn⟩ := hcontain {n} isCompact_singleton
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hn : (n : G) ∈ ambientConjugate t⁻¹
        ((K.toSubgroup ⊓ N : Subgroup G) : Set G) :=
      hεn t ht ⟨n, Set.mem_singleton n, rfl⟩
    obtain ⟨a, ha, hna⟩ := hn
    have hconj : t * (n : G) * t⁻¹ = a := by
      rw [← hna]
      group
    rw [map_sub, map_sub, sub_eq_zero]
    calc
      _ = Compact.averageMap ρ hρ K hK
          (ρ (t * (n : G) * t⁻¹) (ρ t w)) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := average_apply_of_mem ρ hρ K hK (hconj ▸ ha.1) _
  | zero => exact ⟨1, zero_lt_one, fun t _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨εx, hxpos, hx⟩ := hx
    obtain ⟨εy, hypos, hy⟩ := hy
    refine ⟨min εx εy, lt_min hxpos hypos, fun t ht => ?_⟩
    rw [map_add, map_add, hx t (hΩ (min_le_left _ _) ht),
      hy t (hΩ (min_le_right _ _) ht), add_zero]
  | smul c x _ hx =>
    obtain ⟨ε, hε, hx⟩ := hx
    exact ⟨ε, hε, fun t ht => by rw [map_smul, map_smul, hx t ht, smul_zero]⟩

private theorem uniform_fixedKernel_compression_zero
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (Ω : ℝ → Set G) (hΩ : Monotone Ω)
    (hcontain : ∀ Γ : Set N, IsCompact Γ → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ω ε, N.subtype '' Γ ⊆
        ambientConjugate t⁻¹ ((K.toSubgroup ⊓ N : Subgroup G) : Set G)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ω ε,
      LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) ≤
        LinearMap.ker (compressedAction ρ hρ K hK t) := by
  classical
  let j := fixedJacquetMap ρ N M hMN K.toSubgroup
  let := hfin
  obtain ⟨B, hB⟩ := IsNoetherian.noetherian (LinearMap.ker j)
  have hpoint : ∀ v ∈ B, ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ω ε,
      compressedAction ρ hρ K hK t v = 0 := by
    intro v hv
    have hvker : v ∈ LinearMap.ker j := hB ▸ Submodule.subset_span hv
    have hvq : mk ρ N v.val = 0 := congrArg Subtype.val hvker
    obtain ⟨ε, hε, hvε⟩ := uniform_relations_average_zero ρ hρ K hK N Ω hΩ hcontain
      v.val ((mk_eq_zero ρ N v.val).mp hvq)
    exact ⟨ε, hε, fun t ht => Subtype.ext (hvε t ht)⟩
  have hfinite : ∀ S : Finset (fixedVectors ρ K.toSubgroup),
      (∀ v ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ω ε,
        compressedAction ρ hρ K hK t v = 0) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ω ε, ∀ v ∈ S,
        compressedAction ρ hρ K hK t v = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨1, zero_lt_one, by simp⟩
    | @insert v S hv ih =>
      intro hS
      obtain ⟨εv, hvpos, hvε⟩ := hS v (Finset.mem_insert_self _ _)
      obtain ⟨εS, hSpos, hSε⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
      refine ⟨min εv εS, lt_min hvpos hSpos, fun t ht w hw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hvε t (hΩ (min_le_left _ _) ht)
      · exact hSε t (hΩ (min_le_right _ _) ht) w hw
  obtain ⟨ε, hε, hεB⟩ := hfinite B hpoint
  refine ⟨ε, hε, fun t ht => ?_⟩
  rw [← hB]
  exact Submodule.span_le.mpr (fun v hv => hεB t ht v hv)

end UniformKernel

section LinearAlgebra

variable {W : Type uV} [AddCommGroup W] [Module ℂ W]
variable {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q]

private theorem submodule_eq_of_quotient_bijective
    (j : W →ₗ[ℂ] Q) {P R : Submodule ℂ W} (hPR : P ≤ R)
    (hP : Function.Surjective (j.comp P.subtype))
    (hR : Function.Injective (j.comp R.subtype)) : P = R := by
  apply le_antisymm hPR
  intro v hv
  obtain ⟨w, hw⟩ := hP (j v)
  have heq : (⟨w.val, hPR w.property⟩ : R) = ⟨v, hv⟩ := hR hw
  have heqval : w.val = v := congrArg Subtype.val heq
  rw [← heqval]
  exact w.property

end LinearAlgebra

section SingleImage

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

private theorem singleCompression_consequences
    {N M Nbar : Subgroup G} {t : G}
    (h : IsIwahoriContraction K N M Nbar t) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (hkill : LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) ≤
      LinearMap.ker (compressedAction ρ hρ K hK t)) :
    LinearMap.ker (compressedAction ρ hρ K hK t) =
        LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) ∧
      IsCompl (LinearMap.ker (compressedAction ρ hρ K hK t))
        (LinearMap.range (compressedAction ρ hρ K hK t)) ∧
      Function.Bijective (compressedImageJacquetMap ρ hρ K hK t N M hMN) ∧
      LinearMap.range (compressedAction ρ hρ K hK t) = stableImage ρ hρ K hK t ∧
      powerKernelSup ρ hρ K hK t =
        LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
  let C := compressedAction ρ hρ K hK t
  have hpower := powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN
  have hker : LinearMap.ker C = powerKernelSup ρ hρ K hK t := by
    apply le_antisymm
    · intro v hv
      exact Submodule.mem_iSup_of_mem 1 (by simpa using hv)
    · rw [hpower]
      exact hkill
  have hcompl := powerKernelSup_isCompl_stableImage ρ hρ K hK t hfin
  have hrange : LinearMap.range C = stableImage ρ hρ K hK t := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      have hw : w ∈ powerKernelSup ρ hρ K hK t ⊔ stableImage ρ hρ K hK t := by
        rw [hcompl.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      rw [← hker, LinearMap.mem_ker] at ha
      rw [map_add, ha, zero_add]
      exact compressedAction_mem_stableImage ρ hρ K hK t b hb
    · exact iInf_le_of_le 1 (by simp only [pow_one]; exact le_rfl)
  dsimp only [C] at hrange hker
  have hb := stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin
  refine ⟨hker.trans hpower, ?_, ?_, hrange, hpower⟩
  · rwa [hker, hrange]
  · unfold compressedImageJacquetMap
    rw [hrange]
    exact hb

end SingleImage

section CommonImage

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

private theorem common_compression_range
    {N M Nbar : Subgroup G} (hMN : M ≤ Subgroup.normalizer N)
    (Ω : Set G)
    (hmul : ∀ t ∈ Ω, ∀ t' ∈ Ω, t * t' ∈ Ω)
    (hcomm : ∀ t ∈ Ω, ∀ t' ∈ Ω, Commute t t')
    (hiw : ∀ t ∈ Ω, IsIwahoriContraction K N M Nbar t)
    (hbij : ∀ t ∈ Ω,
      Function.Bijective (compressedImageJacquetMap ρ hρ K hK t N M hMN))
    {t t' : G} (ht : t ∈ Ω) (ht' : t' ∈ Ω) :
    LinearMap.range (compressedAction ρ hρ K hK t) =
      LinearMap.range (compressedAction ρ hρ K hK t') := by
  have hprod (a : G) (ha : a ∈ Ω) (b : G) (hb : b ∈ Ω) :
      compressedAction ρ hρ K hK (a * b) =
        compressedAction ρ hρ K hK a * compressedAction ρ hρ K hK b :=
    compressedAction_mul_of_factor ρ hρ K hK N M Nbar (hiw a ha).factor a b
      (fun u hu => ((hiw a ha).upper u hu).1)
      (fun l hl => ((hiw b hb).lower l hl).1)
      (fun m hm => ((hiw b hb).levi m hm).1)
  have hleft : LinearMap.range (compressedAction ρ hρ K hK (t * t')) ≤
      LinearMap.range (compressedAction ρ hρ K hK t) := by
    rintro v ⟨w, rfl⟩
    exact ⟨compressedAction ρ hρ K hK t' w, by rw [hprod t ht t' ht']; rfl⟩
  have hright : LinearMap.range (compressedAction ρ hρ K hK (t * t')) ≤
      LinearMap.range (compressedAction ρ hρ K hK t') := by
    rw [(hcomm t ht t' ht').eq]
    rintro v ⟨w, rfl⟩
    exact ⟨compressedAction ρ hρ K hK t w, by rw [hprod t' ht' t ht]; rfl⟩
  have hleft_eq := submodule_eq_of_quotient_bijective
    (fixedJacquetMap ρ N M hMN K.toSubgroup) hleft
      (hbij (t * t') (hmul t ht t' ht')).2 (hbij t ht).1
  have hright_eq := submodule_eq_of_quotient_bijective
    (fixedJacquetMap ρ N M hMN K.toSubgroup) hright
      (hbij (t * t') (hmul t ht t' ht')).2 (hbij t' ht').1
  exact hleft_eq.symm.trans hright_eq

end CommonImage

section ActualChambers

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
variable {S A : CommGroupScheme (Spec (CommRingCat.of F))}
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
variable {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

private theorem actual_epsilon_monotone :
    Monotone (standardComponentCAepsilon i ν J q) := by
  intro ε δ hεδ t ht
  obtain ⟨a, ha, rfl⟩ := ht
  exact ⟨a, ⟨ha.1, fun α hα => (ha.2 α hα).trans_le hεδ⟩, rfl⟩

private theorem characterNorm_nonnegative (α : characterLattice A)
    (a : rationalPoints A.toGrp) : 0 ≤ CocharacterUniformizer.characterNorm F A α a :=
  NNReal.coe_nonneg _

private theorem characterNorm_mul (α : characterLattice A)
    (a b : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A α (a * b) =
      CocharacterUniformizer.characterNorm F A α a *
        CocharacterUniformizer.characterNorm F A α b := by
  simp [CocharacterUniformizer.characterNorm]

private theorem characterNorm_pow (α : characterLattice A)
    (a : rationalPoints A.toGrp) (n : ℕ) :
    CocharacterUniformizer.characterNorm F A α (a ^ n) =
      CocharacterUniformizer.characterNorm F A α a ^ n := by
  simp [CocharacterUniformizer.characterNorm]

private theorem actual_epsilon_mul {ε : ℝ} (hε : ε ≤ 1)
    {t t' : rationalPoints G}
    (ht : t ∈ standardComponentCAepsilon i ν J q ε)
    (ht' : t' ∈ standardComponentCAepsilon i ν J q ε) :
    t * t' ∈ standardComponentCAepsilon i ν J q ε := by
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨b, hb, rfl⟩ := ht'
  refine ⟨a * b, ⟨(CocharacterUniformizer.CA F A).mul_mem ha.1 hb.1, ?_⟩, map_mul _ _ _⟩
  intro α hα
  rw [characterNorm_mul]
  exact (mul_le_of_le_one_right (characterNorm_nonnegative α a)
    ((hb.2 α hα).le.trans hε)).trans_lt (ha.2 α hα)

private theorem actual_epsilon_commute {ε : ℝ} {t t' : rationalPoints G}
    (ht : t ∈ standardComponentCAepsilon i ν J q ε)
    (ht' : t' ∈ standardComponentCAepsilon i ν J q ε) : Commute t t' := by
  obtain ⟨a, _, rfl⟩ := ht
  obtain ⟨b, _, rfl⟩ := ht'
  exact (Commute.all a b).map (rationalPoints.map (q ≫ i))

private theorem actual_epsilon_nonempty
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : rationalPoints G, t ∈ standardComponentCAepsilon i ν J q ε := by
  obtain ⟨c, hc⟩ := hA.exists_cocharacter_lift i ν hi hzeta
  have hpair : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      (1 : ℤ) ≤ latticePairing A α c := by
    rintro α ⟨β, hβ, rfl⟩
    have heq : latticePairing A (componentCharacterRestriction q β) c =
        latticePairing S β zeta := by
      change gmEndEquiv F (c ≫ (Additive.ofMul q ≫ β)) = _
      rw [← Category.assoc]
      have hc' : c ≫ Additive.ofMul q = zeta := congrArg Additive.ofMul hc
      rw [hc']
      rfl
    rw [heq]
    exact hzeta.2.2 β hβ.1 hβ.2
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    ((zpow_lt_one_iff_right₀ hq).mpr (show (-1 : ℤ) < 0 by decide))
  let x := CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)
  have hx : x ∈ CocharacterUniformizer.CA F A := ⟨Multiplicative.ofAdd c, rfl⟩
  refine ⟨rationalPoints.map (q ≫ i) (x ^ n), x ^ n,
    ⟨(CocharacterUniformizer.CA F A).pow_mem hx n, ?_⟩, rfl⟩
  intro α hα
  rw [characterNorm_pow]
  apply lt_of_le_of_lt _ hn
  apply pow_le_pow_left₀ (characterNorm_nonnegative α x)
  rw [CocharacterUniformizer.characterNorm_latticeSection]
  exact zpow_le_zpow_right₀ hq.le (neg_le_neg (hpair α hα))

private theorem actual_epsilon_isIwahoriContraction
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (K : OpenSubgroup (rationalPoints G))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    {ε : ℝ} (hε : ε ≤ 1) {t : rationalPoints G}
    (ht : t ∈ standardComponentCAepsilon i ν J q ε) :
    IsIwahoriContraction K (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J) t := by
  obtain ⟨a, ha, rfl⟩ := ht
  apply isIwahoriContraction_of_contractionAndCofinality K.isOpen hBasis.1 hBasis.2
  · exact hA.map_mem_standardLeviPoints i ν a
  · exact ⟨a, ha.1, rfl⟩
  · exact ⟨a, ⟨ha.1, fun α hα => (ha.2 α hα).le.trans hε⟩, rfl⟩
  · exact ⟨a, ⟨ha.1, fun α hα => (ha.2 α hα).trans_le hε⟩, rfl⟩

end ActualChambers

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The uniform single-image section and independence assertion of Renard VI.6.1,
under the explicit actual-standard Chapter V hypotheses. -/
theorem standardCanonicalSection : StandardCanonicalSectionStatement := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  dsimp only
  intro S A i hi ν _ J _ hstandard q hA hMN K hK hBasis V _ _ ρ hρ
  obtain ⟨ε₀, hε₀, hkill₀⟩ := uniform_fixedKernel_compression_zero ρ hρ.1 K hK
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hMN (hρ.2 K)
    (standardComponentCAepsilon i ν J q) (actual_epsilon_monotone i ν)
    hBasis.2.2.2.2.1.1
  let ε := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ zero_lt_one
  have hεone : ε ≤ 1 := min_le_right _ _
  have hkill (t : rationalPoints G) (ht : t ∈ standardComponentCAepsilon i ν J q ε) :=
    hkill₀ t (actual_epsilon_monotone i ν (min_le_left _ _) ht)
  have hiw (t : rationalPoints G) (ht : t ∈ standardComponentCAepsilon i ν J q ε) :=
    actual_epsilon_isIwahoriContraction i ν hA K hBasis hεone ht
  have hsingle (t : rationalPoints G) (ht : t ∈ standardComponentCAepsilon i ν J q ε) :=
    singleCompression_consequences ρ hρ.1 K hK (hiw t ht) hMN (hρ.2 K) (hkill t ht)
  have hbij (t : rationalPoints G) (ht : t ∈ standardComponentCAepsilon i ν J q ε) :=
    (hsingle t ht).2.2.1
  obtain ⟨zeta, hzeta⟩ := hstandard
  obtain ⟨t₀, ht₀⟩ := actual_epsilon_nonempty i ν hA hi hzeta hε
  have hrange (t : rationalPoints G) (ht : t ∈ standardComponentCAepsilon i ν J q ε) :=
    common_compression_range ρ hρ.1 K hK hMN (standardComponentCAepsilon i ν J q ε)
      (fun a ha b hb => actual_epsilon_mul i ν hεone ha hb)
      (fun a ha b hb => actual_epsilon_commute i ν ha hb) hiw hbij ht₀ ht
  let s := compressedImageLift ρ hρ.1 K hK t₀
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hMN (hbij t₀ ht₀)
  refine ⟨ε, hε, hεone, ⟨t₀, ht₀⟩, s, ?_, ?_⟩
  · apply LinearMap.ext
    intro y
    exact fixedJacquetMap_compressedImageLift ρ hρ.1 K hK t₀ _ _ hMN (hbij t₀ ht₀) y
  · intro t ht
    obtain ⟨hker, hcompl, hb, hstable, hpower⟩ := hsingle t ht
    refine ⟨hkill t ht, hker, hcompl, hb, hstable, hpower, ?_, ?_⟩
    · exact (range_compressedImageLift ρ hρ.1 K hK t₀ _ _ hMN (hbij t₀ ht₀)).trans
        (hrange t ht)
    · intro hb'
      exact compressedImageLift_eq_of_range_eq ρ hρ.1 K hK t t₀ _ _ hMN hb'
        (hbij t₀ ht₀) (hrange t ht).symm

end Langlands.Jacquet
