import Langlands.Representation.Intertwining.PQIntegralIdentificationAbstract
import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Induction.CompactQuotientDuality
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Aubert.General.RestrictedLeviTopology

/-! # The integral over `V = N̄ ∩ U` on an abstract parabolic

Group-level ingredients of Renard VII.3.4 (first paragraph of the proof). For a semidirect
decomposition `P = M ⋉ N` of a closed subgroup of a locally compact nonarchimedean group `G`,
a smooth representation `σ` of `M`, and a closed subgroup `V` with a Haar measure, the
integral `f ↦ ∫_V f(v) dv` of an induced function whose restriction to `V` has compact
support is defined by testing against linear forms. This module proves its linearity,
its invariance under right translation by a unipotent subgroup `U = (N ∩ U) V`, its
covariance under `M`, a descent lemma through the Jacquet relations of `U`, and the existence
of induced functions with prescribed integral.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Aubert.General.IntegralIdentification

open DualIntegral

universe uG uV

section Unimodular

/-- A locally compact group in which every element lies in a compact open subgroup is
unimodular: every regular Haar measure is right invariant. -/
theorem isMulRightInvariant_of_forall_mem_compactOpen {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ]
    [BorelSpace Γ]
    (h : ∀ g : Γ, ∃ C : Subgroup Γ, IsOpen (C : Set Γ) ∧ IsCompact (C : Set Γ) ∧ g ∈ C)
    (μ : Measure Γ) [μ.IsHaarMeasure] [μ.Regular] : μ.IsMulRightInvariant :=
  Haar.isMulRightInvariant_of_modularCharacter_eq_one (fun g => by
    obtain ⟨C, hCo, hCc, hg⟩ := h g
    exact Induction.modularCharacter_eq_one_of_isCompact C hCo hCc hg) μ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- In a closed limit of compact subgroups every element lies in a compact open subgroup. -/
theorem exists_compactOpen_of_isLimit (V : Subgroup G) (hV : IsClosed (V : Set G))
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups V) (v : V) :
    ∃ C : Subgroup V, IsOpen (C : Set V) ∧ IsCompact (C : Set V) ∧ v ∈ C := by
  have : LocallyCompactSpace V := hV.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨C, hC, hv⟩ :=
    CorrectedFiltration.exists_compactOpen_mem_of_isLimitOfCompactSubgroups V hVc v
  exact ⟨C, C.isOpen, hC, hv⟩

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A closed subgroup of a limit of compact subgroups is a limit of compact subgroups. -/
theorem isLimitOfCompactSubgroups_of_le [IsTopologicalGroup G] {U V : Subgroup G} (hVU : V ≤ U)
    (hV : IsClosed (V : Set G)) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Jacquet.Localization.IsLimitOfCompactSubgroups V := by
  intro C hC
  let i : V → U := fun v => ⟨v, hVU v.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  obtain ⟨K, hK, hCK⟩ := hU (i '' C) (hC.image hi)
  refine ⟨(K.map U.subtype).comap V.subtype, ?_, ?_⟩
  · have hKG : IsCompact ((K.map U.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.image continuous_subtype_val
    rw [Subgroup.coe_comap, Subgroup.coe_subtype]
    exact hV.isClosedEmbedding_subtypeVal.isCompact_preimage hKG
  · intro c hc
    exact ⟨i c, hCK ⟨c, hc, rfl⟩, rfl⟩

end Unimodular

section Descent

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type*} [AddCommGroup X] [Module ℂ X] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A linear map on a subspace, invariant under a limit of compact subgroups `U`, vanishes on
the subspace's intersection with the `U`-relations of a smooth representation. This is the
exactness of the Jacquet functor (BZ77), applied to the inclusion of the subspace. -/
theorem eq_zero_of_mem_relations {ρ : Representation ℂ G X} (hρ : IsSmooth ρ)
    (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (S : Submodule ℂ X) (hS : ∀ u ∈ U, ∀ s ∈ S, ρ u s ∈ S) (T : S →ₗ[ℂ] W)
    (hT : ∀ (u : U) (s : S), T ⟨ρ u s, hS u u.2 s s.2⟩ = T s)
    (s : S) (hs : (s : X) ∈ Jacquet.Localization.relations ρ U 1) : T s = 0 := by
  obtain ⟨K, hK, hsK⟩ :=
    (Jacquet.Localization.mem_relations_iff_compact U hU 1 ρ (s : X)).mp hs
  rw [MonoidHom.one_comp] at hsK
  -- The restriction of `ρ` to `U`, and the subspace as a representation of `U`.
  let ρU : Representation ℂ U X := ρ.comp U.subtype
  let ρS : Representation ℂ U S :=
    { toFun := fun u =>
        { toFun := fun t => ⟨ρ u t, hS u u.2 t t.2⟩
          map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
          map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
      map_one' := by
        ext t
        simp
      map_mul' := by
        intro u u'
        ext t
        simp [Module.End.mul_apply] }
  let i : ρS.IntertwiningMap ρU :=
    { toLinearMap := S.subtype
      isIntertwining' := fun _ => rfl }
  have hi : Function.Injective i := Subtype.val_injective
  have hρU : IsSmooth ρU := isSmooth_comp U.subtype continuous_subtype_val hρ
  have hKlim : Jacquet.Localization.IsLimitOfCompactSubgroups K := by
    intro C _
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact ⟨⊤, by rw [Subgroup.coe_top]; exact isCompact_univ, fun x _ => trivial⟩
  have hinj := Jacquet.Localization.map_injective_of_smooth K hKlim 1
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact IsLocallyConstant.const _) ⊥ bot_le
    (Jacquet.Localization.isInvariant_one K ⊥ bot_le) i hi hρU
  have hsS : s ∈ Jacquet.Localization.relations ρS K 1 := by
    apply (Jacquet.Localization.mk_eq_zero ρS K 1 s).mp
    apply hinj
    rw [map_zero]
    exact (Jacquet.Localization.mk_eq_zero ρU K 1 (i s)).mpr hsK
  have hle : Jacquet.Localization.relations ρS K 1 ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, t⟩, rfl⟩
    change T (ρS k t - ((1 : K →* ℂˣ) k : ℂ) • t) = 0
    rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
    exact hT (k : U) t
  exact hle hsS

end Descent

section Conjugation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M V : Subgroup G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A subgroup normalized by `x ↦ m⁻¹ x m` for all `m ∈ M` is also normalized by
`x ↦ m x m⁻¹`. -/
theorem conj_inv_mem (hMV : ∀ m ∈ M, ∀ v ∈ V, (m : G)⁻¹ * v * m ∈ V) (m : M) (x : V) :
    (m : G) * (x : G) * (m : G)⁻¹ ∈ V := by
  have h := hMV (m : G)⁻¹ (M.inv_mem m.2) (x : G) x.2
  rwa [inv_inv] at h

/-- Conjugation `x ↦ m⁻¹ x m` of `V` by an element `m` of the Levi normalizing `V`. -/
noncomputable def leviConj (hMV : ∀ m ∈ M, ∀ v ∈ V, (m : G)⁻¹ * v * m ∈ V) (m : M) :
    V ≃ₜ* V where
  toFun x := ⟨(m : G)⁻¹ * (x : G) * (m : G), hMV (m : G) m.2 (x : G) x.2⟩
  invFun x := ⟨(m : G) * (x : G) * (m : G)⁻¹, conj_inv_mem hMV m x⟩
  left_inv x := Subtype.ext (show (m : G) * ((m : G)⁻¹ * (x : G) * m) * (m : G)⁻¹ = x by group)
  right_inv x := Subtype.ext (show (m : G)⁻¹ * ((m : G) * (x : G) * (m : G)⁻¹) * m = x by group)
  map_mul' x y := Subtype.ext (show (m : G)⁻¹ * ((x : G) * y) * m =
    ((m : G)⁻¹ * x * m) * ((m : G)⁻¹ * y * m) by group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end Conjugation

section Induced

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M N : Subgroup G} (hP : IsSemidirectDecomposition P M N) (hN : IsClosed (N : Set G))
  (σ : SmoothRep.{0, uG, uV} ℂ M)

/-- The induced functions. -/
local notation "Ind" => Induction.SmoothFunctions P (inducingRepresentation hP hN σ)

/-- Right translation on induced functions. -/
local notation "ρI" => Induction.smoothInduced P (inducingRepresentation hP hN σ)

/-- Evaluation of induced functions. -/
local notation "ev" => Induction.eval P (inducingRepresentation hP hN σ)

theorem eval_smoothInduced (g : G) (f : Ind) (x : G) :
    ev (ρI g f) x = ev f (x * g) := rfl

theorem eval_add (f f' : Ind) (x : G) : ev (f + f') x = ev f x + ev f' x := rfl

theorem eval_smul (c : ℂ) (f : Ind) (x : G) : ev (c • f) x = c • ev f x := rfl

theorem eval_zero (x : G) : ev 0 x = 0 := rfl

theorem eval_mul_left (p : P) (f : Ind) (x : G) :
    ev f ((p : G) * x) = inducingRepresentation hP hN σ p (ev f x) :=
  f.1.2 p x

/-- On a unimodular radical, induced functions are left invariant under the radical. -/
theorem eval_unipotent_mul (hδ : IsUnimodularModulus N hN) (n : N) (f : Ind) (x : G) :
    ev f ((n : G) * x) = ev f x := by
  refine (eval_mul_left hP hN σ ⟨n, hP.unipotent_le n.2⟩ f x).trans ?_
  change ((HaarModulus.closedHalfCharacter N hN P hP.le_normalizer ⟨n, hP.unipotent_le n.2⟩ :
      ℂˣ) : ℂ) • σ.representation (hP.projection ⟨n, hP.unipotent_le n.2⟩) (ev f x) = ev f x
  rw [closedHalfCharacter_unipotent hP hN hδ n, hP.projection_unipotent n]
  simp

/-- At a point of the Levi, induced functions transform by `δ^{1/2} σ`. -/
theorem eval_levi_mul (m : M) (f : Ind) (x : G) :
    ev f ((m : G) * x) =
      ((HaarModulus.closedHalfCharacter N hN M hP.levi_le_normalizer m : ℂˣ) : ℂ) •
        σ.representation m (ev f x) := by
  refine (eval_mul_left hP hN σ ⟨m, hP.levi_le m.2⟩ f x).trans ?_
  change ((HaarModulus.closedHalfCharacter N hN P hP.le_normalizer ⟨m, hP.levi_le m.2⟩ :
      ℂˣ) : ℂ) • σ.representation (hP.projection ⟨m, hP.levi_le m.2⟩) (ev f x) = _
  rw [closedHalfCharacter_levi hP hN m, hP.projection_levi m]

/-- Induced functions are invariant under right translation by an open subgroup. -/
theorem exists_openSubgroup_eval_mul (f : Ind) :
    ∃ K₀ : OpenSubgroup G, ∀ (x : G) (k : K₀), ev f (x * k) = ev f x := by
  obtain ⟨K₀, hK₀⟩ := f.property
  exact ⟨K₀, fun x k => congrArg (fun F => F.1 x) (hK₀ k)⟩

/-- The restriction of an induced function to any subgroup is locally constant. -/
theorem isLocallyConstant_restrict (V : Subgroup G) (f : Ind) :
    IsLocallyConstant (fun x : V => ev f x) := by
  obtain ⟨K₀, hK₀⟩ := exists_openSubgroup_eval_mul hP hN σ f
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let O : Set V := (fun y : V => (x : G)⁻¹ * y) ⁻¹' (K₀ : Set G)
  refine ⟨O, K₀.isOpen.preimage (continuous_const.mul continuous_subtype_val), by simp [O], ?_⟩
  intro y hy
  have h := hK₀ x ⟨(x : G)⁻¹ * y, hy⟩
  simp only [mul_inv_cancel_left] at h
  exact h

section Conj

variable {V : Subgroup G}

variable [MeasurableSpace V] [BorelSpace V] (haar : Measure V) [haar.IsHaarMeasure]

/-- The modulus of the conjugation `leviConj m` with respect to the Haar measure of `V`. -/
def leviConjFactor (hMV : ∀ m ∈ M, ∀ v ∈ V, (m : G)⁻¹ * v * m ∈ V) (m : M) : ℝ≥0 :=
  haarScalarFactor (haar.map (leviConj hMV m)) haar

/-- The scalar of the Levi covariance of the integral over `V`: `δ_P^{1/2}(m)` times the modulus
of conjugation by `m` on `V`. It does not depend on the representation `σ`. -/
def leviFactor (hMV : ∀ m ∈ M, ∀ v ∈ V, (m : G)⁻¹ * v * m ∈ V) (m : M) : ℂ :=
  ((HaarModulus.closedHalfCharacter N hN M hP.levi_le_normalizer m : ℂˣ) : ℂ) *
    (leviConjFactor haar hMV m : ℂ)

end Conj

section Integral

variable (V : Subgroup G) [MeasurableSpace V] [BorelSpace V] (haar : Measure V)

/-- Renard's `∫_V f(v) dv`, read against linear forms. -/
def integralOn (f : Ind) : σ :=
  dualIntegral haar (fun x : V => ev f x)

/-- Compact support of the restriction to `V`. -/
def HasCompactSupportOn (f : Ind) : Prop :=
  ∃ C : Set V, IsCompact C ∧ ∀ x : V, x ∉ C → ev f x = 0

variable [IsFiniteMeasureOnCompacts haar]

/-- A compactly supported restriction has a dual integral. -/
theorem hasDualIntegral_integralOn {f : Ind} (hf : HasCompactSupportOn hP hN σ V f) :
    HasDualIntegral haar (fun x : V => ev f x) (integralOn hP hN σ V haar f) := by
  obtain ⟨C, hC, hzero⟩ := hf
  exact hasDualIntegral_dualIntegral
    (exists_hasDualIntegral_of_isLocallyConstant (isLocallyConstant_restrict hP hN σ V f) hC hzero)

theorem integralOn_add {f f' : Ind} (hf : HasCompactSupportOn hP hN σ V f)
    (hf' : HasCompactSupportOn hP hN σ V f') :
    integralOn hP hN σ V haar (f + f') =
      integralOn hP hN σ V haar f + integralOn hP hN σ V haar f' :=
  ((hasDualIntegral_integralOn hP hN σ V haar hf).add
    (hasDualIntegral_integralOn hP hN σ V haar hf')).dualIntegral_eq

theorem integralOn_smul (c : ℂ) {f : Ind} (hf : HasCompactSupportOn hP hN σ V f) :
    integralOn hP hN σ V haar (c • f) = c • integralOn hP hN σ V haar f :=
  ((hasDualIntegral_integralOn hP hN σ V haar hf).smul c).dualIntegral_eq

/-- The integral as a linear map on a submodule of compactly supported functions. -/
def integralLinear (S : Submodule ℂ Ind) (hS : ∀ f ∈ S, HasCompactSupportOn hP hN σ V f) :
    S →ₗ[ℂ] σ where
  toFun f := integralOn hP hN σ V haar f
  map_add' f f' := integralOn_add hP hN σ V haar (hS f f.2) (hS f' f'.2)
  map_smul' c f := integralOn_smul hP hN σ V haar c (hS f f.2)

section RightInvariance

variable [T2Space G] [SecondCountableTopology G]

/-- **Right invariance of the integral over `V`** (Renard VII.3.4, proof). Let `U` be a closed
limit of compact subgroups of `G` which is the literal product `U = (N ∩ U) V` of its closed
subgroups `N ∩ U` and `V`, through a homeomorphism `m`, where the radical `N` is a limit of
compact subgroups. For every induced function `f`, every linear form `ℓ` and every `u ∈ U`,
`v ↦ ℓ(f(vu))` is integrable on `V` exactly when `v ↦ ℓ(f(v))` is, with the same integral.
The proof applies `QuotientIntegration.integral_mul_right_of_leftInvariant` in the group `U`
to the left `N ∩ U`-invariant function `ℓ ∘ f` (invariant because `N` is unimodular), with an
invariant measure on `(N ∩ U) \ U` from `compatibleMeasureExists`; all groups involved are
unimodular since they are limits of compact subgroups. -/
theorem integral_eval_mul_right (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups N)
    {U V : Subgroup G} (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set G)) (hVU : V ≤ U)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (m : (N.subgroupOf U) × (V.subgroupOf U) ≃ₜ U) (hm : ∀ p, m p = p.1.val * p.2.val)
    [MeasurableSpace V] [BorelSpace V] (haar : Measure V) [haar.IsHaarMeasure]
    (f : Ind) (ℓ : Module.Dual ℂ σ) (u : U) :
    (Integrable (fun x : V => ℓ (ev f ((x : G) * u))) haar ↔
        Integrable (fun x : V => ℓ (ev f x)) haar) ∧
      ∫ x : V, ℓ (ev f ((x : G) * u)) ∂haar = ∫ x : V, ℓ (ev f x) ∂haar := by
  have hδ : IsUnimodularModulus N hN := isUnimodularModulus_of_isLimitOfCompactSubgroups N hN hNc
  have : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace V := hV.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  let H : Subgroup U := N.subgroupOf U
  let K : Subgroup U := V.subgroupOf U
  have hHc : IsClosed (H : Set U) := hN.preimage continuous_subtype_val
  have hKc : IsClosed (K : Set U) := hV.preimage continuous_subtype_val
  have : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace K := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient H) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient H) := ⟨rfl⟩
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set U)
  have : SigmaCompactSpace K := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- Haar measures on `U` and `N ∩ U`, both right invariant.
  let μG : Measure U := Measure.haar
  let μH : Measure H := Measure.haar
  have : μG.IsMulRightInvariant :=
    isMulRightInvariant_of_forall_mem_compactOpen (exists_compactOpen_of_isLimit U hU hUc) μG
  have hHlim : Jacquet.Localization.IsLimitOfCompactSubgroups H :=
    isLimitOfCompactSubgroups_subgroupOf N U hU hNc
  have : μH.IsMulRightInvariant :=
    isMulRightInvariant_of_forall_mem_compactOpen (exists_compactOpen_of_isLimit H hHc hHlim) μH
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists H hHc μG μH
  have := hν.regular
  -- The Haar measure of `V`, transported to `K = V ∩ U` inside `U`.
  let ι : V ≃ₜ* K :=
    { toMulEquiv := (Subgroup.subgroupOfEquivOfLe hVU).symm
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let μK : Measure K := haar.map ι
  have : μK.Regular := inferInstance
  have hKlim : Jacquet.Localization.IsLimitOfCompactSubgroups K :=
    isLimitOfCompactSubgroups_subgroupOf V U hU (isLimitOfCompactSubgroups_of_le hVU hV hUc)
  have : μK.IsMulRightInvariant :=
    isMulRightInvariant_of_forall_mem_compactOpen (exists_compactOpen_of_isLimit K hKc hKlim) μK
  -- The left `N ∩ U`-invariant function.
  let φ : U → ℂ := fun y => ℓ (ev f y)
  have hφ : ∀ h : H, ∀ y, φ (h.val * y) = φ y := fun h y =>
    congrArg ℓ (eval_unipotent_mul hP hN σ hδ ⟨(h : U), h.2⟩ f y)
  obtain ⟨h1, h2⟩ := QuotientIntegration.integral_mul_right_of_leftInvariant H K m hm μK ν
    hν.nonzero hν.right_invariant φ hφ u
  have hemb : MeasurableEmbedding ι := ι.toHomeomorph.measurableEmbedding
  rw [hemb.integrable_map_iff, hemb.integrable_map_iff] at h1
  rw [hemb.integral_map, hemb.integral_map] at h2
  exact ⟨h1, h2⟩

/-- Right translation by `U` preserves the integral over `V` of an induced function whose
restriction to `V` has compact support. -/
theorem integralOn_smoothInduced (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups N)
    {U V : Subgroup G} (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set G)) (hVU : V ≤ U)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (m : (N.subgroupOf U) × (V.subgroupOf U) ≃ₜ U) (hm : ∀ p, m p = p.1.val * p.2.val)
    [MeasurableSpace V] [BorelSpace V] (haar : Measure V) [haar.IsHaarMeasure]
    {f : Ind} (hf : HasCompactSupportOn hP hN σ V f) (u : U) :
    integralOn hP hN σ V haar (ρI u f) = integralOn hP hN σ V haar f := by
  apply HasDualIntegral.dualIntegral_eq
  intro ℓ
  obtain ⟨h1, h2⟩ := integral_eval_mul_right hP hN σ hNc hU hV hVU hUc m hm haar f ℓ u
  have hI := hasDualIntegral_integralOn hP hN σ V haar hf ℓ
  exact ⟨h1.mpr hI.1, by rw [hI.2, ← h2]; rfl⟩

end RightInvariance

section LeviCovariance

omit [IsFiniteMeasureOnCompacts haar] in
/-- **Levi covariance of the integral over `V`.** For `m` in the Levi normalizing `V` and an
induced function `f` with compactly supported restriction to `V`,
`∫_V f(vm) dv = c(m) σ(m) ∫_V f(v) dv` with `c = leviFactor`: indeed
`f(vm) = δ_P^{1/2}(m) σ(m) f(m⁻¹vm)`, and the change of variables `v ↦ m⁻¹vm` multiplies the
Haar measure of `V` by its modulus. -/
theorem integralOn_smoothInduced_levi [T2Space G] [SecondCountableTopology G]
    (hV : IsClosed (V : Set G)) [haar.IsHaarMeasure]
    (hMV : ∀ m ∈ M, ∀ v ∈ V, (m : G)⁻¹ * v * m ∈ V) {f : Ind}
    (hf : HasCompactSupportOn hP hN σ V f) (m : M) :
    integralOn hP hN σ V haar (ρI (m : G) f) =
      leviFactor hP hN haar hMV m • σ.representation m (integralOn hP hN σ V haar f) := by
  have : LocallyCompactSpace V := hV.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology V := TopologicalSpace.Subtype.secondCountableTopology (V : Set G)
  let c := leviConj hMV m
  have hmap : haar.map c = leviConjFactor haar hMV m • haar := isMulLeftInvariant_eq_smul _ _
  have hI := ((hasDualIntegral_integralOn hP hN σ V haar hf).map
    (σ.representation m)).comp_measurableEmbedding c.toHomeomorph.measurableEmbedding hmap
  have hI' := hI.smul ((HaarModulus.closedHalfCharacter N hN M hP.levi_le_normalizer m : ℂˣ) : ℂ)
  apply HasDualIntegral.dualIntegral_eq
  rw [leviFactor, mul_smul]
  refine hI'.congr fun x => ?_
  change _ = ev f ((x : G) * m)
  have hx : (x : G) * m = (m : G) * ((c x : V) : G) := by
    change _ = (m : G) * ((m : G)⁻¹ * x * m)
    group
  rw [hx, eval_levi_mul hP hN σ m f]
  rfl

end LeviCovariance

end Integral

section TestFunction

/-- **Coordinates on `V` near `1`.** If the orbit `P \ P V` is locally closed and `V` meets `P`
trivially, then for every neighbourhood `O` of `1` in `V` there is an open neighbourhood `O'` of
`1` in `G` such that `p x ∈ O'` with `p ∈ P`, `x ∈ V` forces `x ∈ O`. This is the openness of
the orbit map `V → P \ P V` (`Geometric.isOpenMap_cosetOrbitMap`, a Baire category argument). -/
theorem exists_open_coordinate [SigmaCompactSpace G] (hPc : IsClosed (P : Set G))
    {V : Subgroup G} (hV : IsClosed (V : Set G))
    (hlocV : IsLocallyClosed (Geometric.cosetOrbit P V 1)) (hPV : ∀ v ∈ V, v ∈ P → v = 1)
    {O : Set V} (hO : O ∈ 𝓝 (1 : V)) :
    ∃ O' : Set G, IsOpen O' ∧ (1 : G) ∈ O' ∧ ∀ p ∈ P, ∀ x : V, p * (x : G) ∈ O' → x ∈ O := by
  obtain ⟨O₀, hO₀O, hO₀o, h1O₀⟩ := mem_nhds_iff.mp hO
  have hopen := Geometric.isOpenMap_cosetOrbitMap P V 1 hPc hV hlocV O₀ hO₀o
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.mp hopen
  refine ⟨Induction.quotientMap P ⁻¹' W, hWo.preimage continuous_quotient_mk', ?_, ?_⟩
  · have h1 : Geometric.cosetOrbitMap P V 1 1 ∈ Subtype.val ⁻¹' W := by
      rw [hW]
      exact ⟨1, h1O₀, rfl⟩
    simpa [Geometric.cosetOrbitMap] using h1
  · intro p hp x hx
    have hx' : Geometric.cosetOrbitMap P V 1 x ∈ Subtype.val ⁻¹' W := by
      change Induction.quotientMap P (1⁻¹ * (x : G)) ∈ W
      have heq : Induction.quotientMap P (1⁻¹ * (x : G)) = Induction.quotientMap P (p * x) := by
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        simpa using hp
      rw [heq]
      exact hx
    rw [hW] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hba : x * y⁻¹ ∈ Geometric.orbitStabilizer P V 1 :=
      QuotientGroup.rightRel_apply.mp ((Geometric.cosetOrbitMap_eq_iff P V 1 y x).mp hyx)
    have hba' : (x : G) * (y : G)⁻¹ ∈ P := by
      simpa [Geometric.orbitStabilizer] using hba
    have h1 := hPV _ (V.mul_mem x.2 (V.inv_mem y.2)) hba'
    have hxy : x = y := Subtype.ext (mul_inv_eq_one.mp h1)
    exact hO₀O (hxy ▸ hy)

/-- **Induced functions with prescribed integral** (Renard VII.3.4, proof: surjectivity).
Let `D ∋ 1` be a locally closed left `P`-invariant subset of `G` (in the application the double
coset `P Q`), such that induced functions vanishing on `closure D \ D` have compactly supported
restriction to `V`. Then every `v ∈ σ` is the integral over `V` of an induced function vanishing
on `closure D \ D`. The function is a multiple of the section of `ind_P^G` supported on `P K`
with value `v` at `1`, for a small compact open subgroup `K`: its restriction to `V` is `v`
times the indicator of the open set `V ∩ P K`, whose measure is positive and finite. -/
theorem exists_integralOn_eq [SigmaCompactSpace G] (hPc : IsClosed (P : Set G))
    (hproj : Continuous hP.projection) {V : Subgroup G} (hV : IsClosed (V : Set G))
    (hlocV : IsLocallyClosed (Geometric.cosetOrbit P V 1)) (hPV : ∀ v ∈ V, v ∈ P → v = 1)
    [MeasurableSpace V] [BorelSpace V] (haar : Measure V) [haar.IsHaarMeasure]
    (D : Set G) (hDP : ∀ p ∈ P, ∀ x ∈ D, p * x ∈ D) (h1D : (1 : G) ∈ D)
    (hlocD : IsLocallyClosed D)
    (hcs : ∀ f : Ind, (∀ x ∈ closure D \ D, ev f x = 0) → HasCompactSupportOn hP hN σ V f)
    (v : σ) :
    ∃ f : Ind, (∀ x ∈ closure D \ D, ev f x = 0) ∧ integralOn hP hN σ V haar f = v := by
  classical
  by_cases hv0 : v = 0
  · refine ⟨0, fun x _ => eval_zero hP hN σ x, ?_⟩
    rw [hv0]
    apply HasDualIntegral.dualIntegral_eq
    exact hasDualIntegral_zero.congr fun x => (eval_zero hP hN σ x).symm
  -- An open subgroup of `P` fixing `v`, and an open subgroup `K₁` of `G` inside it.
  have hsm : IsSmooth (inducingRepresentation hP hN σ) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter N hN P hP.le_normalizer)).mpr
      (isSmooth_comp hP.projection hproj σ.isSmooth)
  obtain ⟨H, hH⟩ := hsm v
  obtain ⟨Ov, hOv, hOvH⟩ := IsInducing.subtypeVal.isOpen_iff.mp H.isOpen
  have h1Ov : (1 : G) ∈ Ov := by
    have h : (1 : P) ∈ (H : Set P) := H.one_mem
    rw [← hOvH] at h
    exact h
  have hfixOv : ∀ p : P, (p : G) ∈ Ov → inducingRepresentation hP hN σ p v = v := by
    intro p hp
    have hpH : p ∈ (H : Set P) := by
      rw [← hOvH]
      exact hp
    exact hH ⟨p, hpH⟩
  obtain ⟨K₁, hK₁⟩ := NonarchimedeanGroup.is_nonarchimedean Ov (hOv.mem_nhds h1Ov)
  obtain ⟨O', hO'o, h1O', hO'⟩ := exists_open_coordinate hPc hV hlocV hPV
    (O := Subtype.val ⁻¹' (K₁ : Set G))
    ((K₁.isOpen.preimage continuous_subtype_val).mem_nhds K₁.one_mem)
  have hcob : IsOpen (coborder D) := hlocD.isOpen_coborder
  have h1cob : (1 : G) ∈ coborder D := subset_coborder h1D
  obtain ⟨K, hK, hKN⟩ := compactOpenSubgroupBasis G ((K₁ : Set G) ∩ O' ∩ coborder D)
    (((K₁.isOpen.inter hO'o).inter hcob).mem_nhds ⟨⟨K₁.one_mem, h1O'⟩, h1cob⟩)
  have hvfix : v ∈ fixedVectors (inducingRepresentation hP hN σ)
      (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    intro p
    have hp : (1 : G)⁻¹ * ((p : P) : G) * 1 ∈ K := Induction.mem_conjOpenSubgroup.mp p.property
    have hpK : ((p : P) : G) ∈ K := by simpa using hp
    exact hfixOv p (hK₁ (hKN hpK).1.1)
  -- The section supported on `P K` with value `v` at `1`.
  let s := Induction.compactDoubleCosetSection P (inducingRepresentation hP hN σ) K hK 1 v hvfix
  have happ : ∀ (p : P) (k : K), ev s.val ((p : G) * 1 * (k : G)) =
      inducingRepresentation hP hN σ p v :=
    Induction.compactDoubleCosetSection_apply P _ K hK 1 v hvfix
  have hsupp : ∀ x : G, ev s.val x ≠ 0 → x ∈ (P : Set G) * (K : Set G) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := Induction.compactDoubleCosetSection_support_subset P _ K hK 1 v hvfix
      ⟨x, hx, rfl⟩
    have hxk : x * (1 * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkx)
    exact ⟨x * (1 * k)⁻¹, hxk, k, hk, by simp⟩
  -- Its restriction to `V` is `v` times an indicator.
  let S : Set V := Subtype.val ⁻¹' ((P : Set G) * (K : Set G))
  have hval : ∀ x : V, ev s.val x = S.indicator (fun _ => v) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have hxK₁ : (x : G) ∈ K₁ := by
        have h := hO' a⁻¹ (P.inv_mem ha) x (by
          rw [← hab, ← mul_assoc, inv_mul_cancel, one_mul]
          exact (hKN hb).1.2)
        exact h
      have haK₁ : a ∈ K₁ := by
        have h : a = (x : G) * b⁻¹ := by rw [← hab, mul_inv_cancel_right]
        rw [h]
        exact K₁.mul_mem hxK₁ (K₁.inv_mem (hKN hb).1.1)
      have hx' : (x : G) = ((⟨a, ha⟩ : P) : G) * 1 * ((⟨b, hb⟩ : K) : G) := by
        rw [mul_one]
        exact hab.symm
      rw [hx', happ]
      exact hfixOv ⟨a, ha⟩ (hK₁ haK₁)
    · rw [Set.indicator_of_notMem hx]
      by_contra hne
      exact hx (hsupp x hne)
  -- It vanishes on `closure D \ D`.
  have hclP : ∀ p ∈ P, ∀ x ∈ closure D, p * x ∈ closure D := by
    intro p hp x hx
    exact map_mem_closure (continuous_const.mul continuous_id) hx (fun y hy => hDP p hp y hy)
  have hbv : ∀ x ∈ closure D \ D, ev s.val x = 0 := by
    rintro x ⟨hxcl, hxD⟩
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ := hsupp x hne
    have hbcl : b ∈ closure D := by
      have h := hclP a⁻¹ (P.inv_mem ha) x hxcl
      rwa [← hab, ← mul_assoc, inv_mul_cancel, one_mul] at h
    have hbD : b ∈ D := by
      by_contra hbD
      exact (hKN hb).2 ⟨hbcl, hbD⟩
    exact hxD (hab ▸ hDP a ha b hbD)
  -- The measure of `V ∩ P K` is positive and finite.
  obtain ⟨C, hC, hCz⟩ := hcs s.val hbv
  have hSC : S ⊆ C := by
    intro x hx
    by_contra hxC
    have h := hCz x hxC
    rw [hval, Set.indicator_of_mem hx] at h
    exact hv0 h
  have hSopen : IsOpen S :=
    (IsOpen.mul_left (s := (P : Set G)) K.isOpen).preimage continuous_subtype_val
  have h1S : (1 : V) ∈ S := ⟨1, P.one_mem, 1, K.one_mem, mul_one 1⟩
  have hμS : haar S ≠ ∞ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hSC)
  have hμpos : 0 < haar S := hSopen.measure_pos haar ⟨1, h1S⟩
  have hreal : haar.real S ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hμpos.ne', hμS⟩
  have hI : integralOn hP hN σ V haar s.val = (haar.real S : ℂ) • v :=
    ((hasDualIntegral_indicator hSopen.measurableSet hμS v).congr
      fun x => (hval x).symm).dualIntegral_eq
  refine ⟨(haar.real S : ℂ)⁻¹ • s.val, ?_, ?_⟩
  · intro x hx
    rw [eval_smul, hbv x hx, smul_zero]
  · rw [integralOn_smul hP hN σ V haar _ (hcs s.val hbv), hI, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hreal), one_smul]

end TestFunction

end Induced


end Langlands.Aubert.General.IntegralIdentification
