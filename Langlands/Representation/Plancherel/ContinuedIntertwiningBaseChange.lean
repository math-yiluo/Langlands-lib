import Langlands.Representation.Plancherel.ContinuedIntertwiningNaturality
import Langlands.Representation.Plancherel.CompactIntertwiningBaseChange
import Langlands.Representation.Plancherel.UnramifiedOperatorTranslation

/-! # Independent intertwiner continuations after a change of base representation -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uH uI uV uW uV' uW'

section RationalTranslation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → V' →ₗ[ℂ] W'}

include hp hL

/-- A square at corresponding translated parameters persists for two
independently supplied continuations and their independent denominators. -/
theorem rationalOperatorContinuationData_translation_natural
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B)
    (S : V →ₗ[ℂ] V') (T : W →ₗ[ℂ] W')
    (hD : IsOpen D) (hne : D.Nonempty)
    (hDΩ : D ⊆ (unramifiedParameterTranslation _ τ) ⁻¹' Ω) (hDΛ : D ⊆ Λ)
    (hnat : ∀ χ (hχ : χ ∈ D),
      (B ⟨χ, hDΛ hχ⟩).comp S = T.comp (A ⟨τ * χ, hDΩ hχ⟩))
    (χ : ↥(((unramifiedParameterTranslation _ τ) ⁻¹' p.regularRegion) ∩
      q.regularRegion)) :
    (q.continuedOperator ⟨χ.val, χ.property.2⟩).comp S =
      T.comp (p.continuedOperator ⟨τ * χ.val, χ.property.1⟩) := by
  exact rationalOperatorContinuationData_natural L hp hL (p.translation τ) q
    S T hD hne hDΩ hDΛ hnat χ

end RationalTranslation

section CharacterTransport

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI}
  (e : H ≃ₜ* M) (ν : I → (H →* ℝ≥0ˣ))
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

local notation "νM" => (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν

/-- The actual twisting equivalence in the original character chart.
The identity comparison accounts for left translation and Levi transport. -/
def transportedBaseTwistEquiv (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation) :
    (A.twist (χM (τ * χ)).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM (τ * χ)))).representation.Equiv
      (B.twist (χM χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (χM χ))).representation :=
  (equivOfRepresentationEq (by
    change twist (χM (τ * χ)).val.toMonoidHom A.representation =
      twist (χM χ * χM τ).val.toMonoidHom A.representation
    rw [map_mul, mul_comm (χM τ) (χM χ)])).trans
      (productBaseTwistEquiv νM (χM τ) (χM χ) a)

@[simp]
theorem transportedBaseTwistEquiv_apply (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (v : A) :
    transportedBaseTwistEquiv e ν τ χ a v = a v := rfl

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- Restriction of the chart-compatible actual map is the fixed compact
base comparison. The parameter dependence remains only in restriction. -/
theorem unramifiedLeviInductionCompactEquiv_transportedBaseChange
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (f : UnramifiedLeviInduction h hU νM (χM (τ * χ)) A) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        νM (fun i => (hν i).comp e.symm.continuous) hr (χM χ) B
        (inducedMap h hU (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap f) =
      compactInductionBaseChangeEquiv h K hP hK
        νM (fun i => (hν i).comp e.symm.continuous) hr (χM τ) a
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
          νM (fun i => (hν i).comp e.symm.continuous) hr (χM (τ * χ)) A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

/-- The inverse restriction comparison uses the same fixed compact map. -/
theorem unramifiedLeviInductionCompactEquiv_symm_transportedBaseChange
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (f : CompactInductionPicture h K A) :
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        νM (fun i => (hν i).comp e.symm.continuous) hr (χM χ) B).symm
        (compactInductionBaseChangeEquiv h K hP hK
          νM (fun i => (hν i).comp e.symm.continuous) hr (χM τ) a f) =
      inducedMap h hU (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
          νM (fun i => (hν i).comp e.symm.continuous) hr (χM (τ * χ)) A).symm f) := by
  apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
    νM (fun i => (hν i).comp e.symm.continuous) hr (χM χ) B).injective
  rw [LinearEquiv.apply_symm_apply,
    unramifiedLeviInductionCompactEquiv_transportedBaseChange e ν h hU hδ
      K hP hK hPK hν hr,
    LinearEquiv.apply_symm_apply]

variable {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- Compact restriction preserves and reflects the actual base-change square
in the original character chart, at left-translated parameters. -/
theorem compactIntertwiningOperator_transportedBaseChange_iff
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (JA : (UnramifiedLeviInduction h hU νM (χM (τ * χ)) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' νM (χM (τ * χ)) A).representation)
    (JB : (UnramifiedLeviInduction h hU νM (χM χ) B).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' νM (χM χ) B).representation) :
    (∀ f, JB (inducedMap h hU
        (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap f) =
      inducedMap h' hU' (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap (JA f)) ↔
    (∀ f, compactIntertwiningOperator h hU hδ K hP hK hPK
        νM (fun i => (hν i).comp e.symm.continuous) hr
        h' hU' hδ' hP' hP'K hr' (χM χ) B JB
        (compactInductionBaseChangeEquiv h K hP hK
          νM (fun i => (hν i).comp e.symm.continuous) hr (χM τ) a f) =
      compactInductionBaseChangeEquiv h' K hP' hK
        νM (fun i => (hν i).comp e.symm.continuous) hr' (χM τ) a
        (compactIntertwiningOperator h hU hδ K hP hK hPK
          νM (fun i => (hν i).comp e.symm.continuous) hr
          h' hU' hδ' hP' hP'K hr' (χM (τ * χ)) A JA f)) := by
  constructor
  · intro hJ f
    change unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K
      νM (fun i => (hν i).comp e.symm.continuous) hr' (χM χ) B
      (JB ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        νM (fun i => (hν i).comp e.symm.continuous) hr (χM χ) B).symm
        (compactInductionBaseChangeEquiv h K hP hK
          νM (fun i => (hν i).comp e.symm.continuous) hr (χM τ) a f))) = _
    rw [unramifiedLeviInductionCompactEquiv_symm_transportedBaseChange
      e ν h hU hδ K hP hK hPK hν hr, hJ,
      unramifiedLeviInductionCompactEquiv_transportedBaseChange
        e ν h' hU' hδ' K hP' hK hP'K hν hr']
    rfl
  · intro hJ f
    have hc := hJ
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        νM (fun i => (hν i).comp e.symm.continuous) hr (χM (τ * χ)) A f)
    simp only [compactIntertwiningOperator, LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
    rw [unramifiedLeviInductionCompactEquiv_symm_transportedBaseChange
      e ν h hU hδ K hP hK hPK hν hr, LinearEquiv.symm_apply_apply] at hc
    apply (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K
      νM (fun i => (hν i).comp e.symm.continuous) hr' (χM χ) B).injective
    rw [unramifiedLeviInductionCompactEquiv_transportedBaseChange
      e ν h' hU' hδ' K hP' hK hP'K hν hr']
    exact hc

end CharacterTransport

section ActualInduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : SmoothRep.{0, uG, uV} ℂ M)
  (B : SmoothRep.{0, uG, uW} ℂ M)
  {Ω Λ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)
variable
  (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
  (JA : ∀ χ : Ω,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (JB : ∀ χ : Λ,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation)
  (p : RationalOperatorContinuationData Ω (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (JA χ)))
  (q : RationalOperatorContinuationData Λ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (JB χ)))
  (hD : IsOpen D) (hne : D.Nonempty)
  (hDΩ : D ⊆ (unramifiedParameterTranslation
    (fun ψ => (rationalNormCharacters L ψ).toMul) τ) ⁻¹' Ω)
  (hDΛ : D ⊆ Λ)
  (a : (A.twist
    (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
      τ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        τ))).representation.Equiv B.representation)
  (hnat : ∀ χ (hχ : χ ∈ D)
    (f : UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        (τ * χ)) A),
    JB ⟨χ, hDΛ hχ⟩
        (inducedMap h₀ hU₀
          (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
            τ χ a).toIntertwiningMap f) =
      inducedMap h₁ hU₁
        (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
          τ χ a).toIntertwiningMap
        (JA ⟨τ * χ, hDΩ hχ⟩ f))

local notation "C₀" => compactInductionBaseChangeEquiv h₀ K hP₀ hK νM hνM hr₀ (χM τ) a
local notation "C₁" => compactInductionBaseChangeEquiv h₁ K hP₁ hK νM hνM hr₁ (χM τ) a

include hp hL hD hne hDΩ hDΛ hnat

/-- Independently chosen compact continuations respect an actual change of
base representation on the intersection of their translated regular loci. -/
theorem continuedCompactIntertwiner_baseChange
    (χ : ↥(((unramifiedParameterTranslation νL τ) ⁻¹' p.regularRegion) ∩ q.regularRegion))
    (f : CompactInductionPicture h₀ K A) :
    q.continuedOperator ⟨χ.val, χ.property.2⟩ (C₀ f) =
      C₁ (p.continuedOperator ⟨τ * χ.val, χ.property.1⟩ f) := by
  have he := rationalOperatorContinuationData_translation_natural L hp hL τ p q
    (C₀).toLinearMap (C₁).toLinearMap hD hne hDΩ hDΛ
    (fun ψ hψ => by
      apply LinearMap.ext
      intro v
      exact ((compactIntertwiningOperator_transportedBaseChange_iff
        e νL h₀ hU₀ hδ₀ K hP₀ hK hP₀K hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ τ ψ a
        (JA ⟨τ * ψ, hDΩ hψ⟩) (JB ⟨ψ, hDΛ hψ⟩)).mp (hnat ψ hψ)) v)
    χ
  exact congrArg (fun Z => Z f) he

set_option quotPrecheck false in
local notation "hDA" => (unramifiedParameterTranslation νL τ).isOpenMap D hD
set_option quotPrecheck false in
local notation "hneA" => hne.image (unramifiedParameterTranslation νL τ)
set_option quotPrecheck false in
local notation "hDAΩ" => Set.image_subset_iff.mpr hDΩ
local notation "JextA" => continuedInductionIntertwiner L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  JA p hDA hneA hDAΩ
local notation "JextB" => continuedInductionIntertwiner L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν B
  JB q hD hne hDΛ

set_option maxRecDepth 2048 in
/-- The independent continuations on the actual normalized induction spaces
respect the same chosen base equivalence at corresponding translated parameters. -/
theorem continuedInductionIntertwiner_baseChange
    (χ : ↥(((unramifiedParameterTranslation νL τ) ⁻¹' p.regularRegion) ∩ q.regularRegion))
    (f : UnramifiedLeviInduction h₀ hU₀ νM (χM (τ * χ.val)) A) :
    JextB ⟨χ.val, χ.property.2⟩
        (inducedMap h₀ hU₀
          (transportedBaseTwistEquiv e νL τ χ.val a).toIntertwiningMap f) =
      inducedMap h₁ hU₁ (transportedBaseTwistEquiv e νL τ χ.val a).toIntertwiningMap
        (JextA ⟨τ * χ.val, χ.property.1⟩ f) := by
  refine ((compactIntertwiningOperator_transportedBaseChange_iff
    e νL h₀ hU₀ hδ₀ K hP₀ hK hP₀K hν hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
    τ χ.val a (JextA ⟨τ * χ.val, χ.property.1⟩)
    (JextB ⟨χ.val, χ.property.2⟩)).mpr ?_) f
  intro v
  have hc := continuedCompactIntertwiner_baseChange L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
    e hν A B τ JA JB p q hD hne hDΩ hDΛ a hnat χ v
  have hA := congrArg (fun Z => Z v)
    (continuedInductionIntertwiner_compact L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
      e hν A JA p hDA hneA hDAΩ ⟨τ * χ.val, χ.property.1⟩)
  have hB := congrArg (fun Z => Z (C₀ v))
    (continuedInductionIntertwiner_compact L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
      e hν B JB q hD hne hDΛ ⟨χ.val, χ.property.2⟩)
  exact hB.trans (hc.trans (congrArg C₁ hA).symm)

end ActualInduction

end Langlands.Plancherel
