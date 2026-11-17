import Langlands.Representation.Exponents.RepresentedChamberIwahoriContractionProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly

/-! # The canonical Jacquet section for a represented parabolic -/

noncomputable section

universe u v uG uV uQ

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Jacquet Langlands.BruhatTits.SpecialCompact

-- These generic arguments are adapted from the private helpers in
-- `Langlands.Representation.Jacquet.StandardCanonicalSectionProof`.

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


/-- Renard VI.6.1: a single image and a canonical section uniform on a sufficiently
small chamber, for every admissible representation and every stated Iwahori decomposition. -/
theorem representedCanonicalSection : RepresentedCanonicalSectionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar
    hP hPP K hK hfactor A a pres Δ incG Nf Mf hMN V _ _ ρ hρ j
  have := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  let Ω : ℝ → Set (rationalPoints G) := fun ε =>
    incG '' {t | ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε}
  have hΩ : Monotone Ω := by
    intro ε δ hεδ g
    rintro ⟨t, ht, rfl⟩
    exact ⟨t, fun α hα => (ht α hα).trans_le hεδ, rfl⟩
  have hGeo := splitComponentOppositeContraction k G hG P Pbar M N Nbar p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP A a pres
  have hcontain : ∀ Γ : Set Nf, IsCompact Γ → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ω ε, Nf.subtype '' Γ ⊆
        ambientConjugate t⁻¹ ((K.toSubgroup ⊓ Nf : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
    intro Γ hΓ
    have hC : IsCompact (Nf.subtype '' Γ) := hΓ.image continuous_subtype_val
    have hCN : Nf.subtype '' Γ ⊆ pointImage (n ≫ p) := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    obtain ⟨ε, hε, hεC⟩ := hGeo (Nf.subtype '' Γ) hC hCN ∅ isCompact_empty
      (Set.empty_subset _) (K : Set (rationalPoints G)) (K.isOpen.mem_nhds K.one_mem)
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨t, ht, rfl⟩ x hx
    have hincG : incG t = rationalPoints.map (m ≫ p) (rationalPoints.map a t) := by
      simp only [incG, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
    have hg : incG t ∈ Mf := ⟨rationalPoints.map a t, hincG.symm⟩
    refine ⟨incG t * x * (incG t)⁻¹,
      ⟨(hεC t ht).1 x hx,
        (Subgroup.mem_normalizer_iff.mp (hMN hg) x).mp (hCN hx)⟩, ?_⟩
    dsimp
    group
  obtain ⟨ε₀, hε₀, hε₀one, _, hiw₀⟩ :=
    representedChamberIwahoriContraction k G hG P Pbar M N Nbar p m n hp hm hn hmul
      pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP K hK hfactor A a pres
  obtain ⟨ε₁, hε₁, hkill₁⟩ := uniform_fixedKernel_compression_zero ρ hρ.1 K hK Nf Mf hMN
    (hρ.2 K) Ω hΩ hcontain
  let ε : ℝ := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hεone : ε ≤ 1 := (min_le_left _ _).trans hε₀one
  have hkill (g : rationalPoints G) (hg : g ∈ Ω ε) :=
    hkill₁ g (hΩ (min_le_right _ _) hg)
  have hiw : ∀ g ∈ Ω ε,
      IsIwahoriContraction K Nf Mf (pointImage (nbar ≫ pbar)) g := by
    rintro _ ⟨t, ht, rfl⟩
    exact hiw₀ t (fun α hα => (ht α hα).trans_le (min_le_left _ _))
  have hsingle (g : rationalPoints G) (hg : g ∈ Ω ε) :=
    singleCompression_consequences ρ hρ.1 K hK (hiw g hg) hMN (hρ.2 K) (hkill g hg)
  have hbij (g : rationalPoints G) (hg : g ∈ Ω ε) := (hsingle g hg).2.2.1
  have hmulΩ : ∀ g ∈ Ω ε, ∀ g' ∈ Ω ε, g * g' ∈ Ω ε := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    refine ⟨t * t', ?_, map_mul _ _ _⟩
    intro α hα
    have hnorm : CocharacterUniformizer.characterNorm k A α (t * t') =
        CocharacterUniformizer.characterNorm k A α t *
          CocharacterUniformizer.characterNorm k A α t' := by
      simp [CocharacterUniformizer.characterNorm]
    rw [hnorm]
    exact (mul_le_of_le_one_right (NNReal.coe_nonneg _)
      ((ht' α hα).le.trans hεone)).trans_lt (ht α hα)
  have hcommΩ : ∀ g ∈ Ω ε, ∀ g' ∈ Ω ε, Commute g g' := by
    rintro _ ⟨t, _, rfl⟩ _ ⟨t', _, rfl⟩
    exact (Commute.all t t').map incG
  obtain ⟨t₀, ht₀⟩ := represented_chamber_nonempty pres hε
  have hg₀ : incG t₀ ∈ Ω ε := ⟨t₀, ht₀, rfl⟩
  have hrange (g : rationalPoints G) (hg : g ∈ Ω ε) :=
    common_compression_range ρ hρ.1 K hK hMN (Ω ε) hmulΩ hcommΩ hiw hbij hg₀ hg
  let s := compressedImageLift ρ hρ.1 K hK (incG t₀) Nf Mf hMN (hbij _ hg₀)
  refine ⟨ε, hε, hεone, ⟨t₀, ht₀⟩, s, ?_, ?_⟩
  · apply LinearMap.ext
    intro y
    exact fixedJacquetMap_compressedImageLift ρ hρ.1 K hK (incG t₀) Nf Mf hMN
      (hbij _ hg₀) y
  · intro t ht
    have hg : incG t ∈ Ω ε := ⟨t, ht, rfl⟩
    obtain ⟨hker, hcompl, hb, hstable, hpower⟩ := hsingle _ hg
    refine ⟨hkill _ hg, hker, hcompl, hb, hstable, hpower, ?_, ?_⟩
    · exact (range_compressedImageLift ρ hρ.1 K hK (incG t₀) Nf Mf hMN
        (hbij _ hg₀)).trans (hrange _ hg)
    · intro hb'
      exact compressedImageLift_eq_of_range_eq ρ hρ.1 K hK (incG t) (incG t₀) Nf Mf hMN
        hb' (hbij _ hg₀) (hrange _ hg).symm

end Langlands.Aubert.General.RepresentedParabolic
