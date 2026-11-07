import Langlands.Representation.Plancherel.CompactInductionPolynomialAction
import Langlands.Representation.Plancherel.RationalUnramifiedIntertwiningContinuation
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport

/-! # Rational continuation on the actual normalized induction spaces -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe u uG uI uV uL

section CompactTransport

variable {G : Type uG} [Group G] [TopologicalSpace G]
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
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Compact conjugation is a linear equivalence between the full ambient
intertwiner spaces, with the inverse constructed from actual extension. -/
def compactInductionIntertwinerEquiv (χ : unramifiedCharacters ν) :
    ((UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation) ≃ₗ[ℂ]
    ((unramifiedCompactRepresentation h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).IntertwiningMap
      (unramifiedCompactRepresentation h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ A χ)) where
  toFun J :=
    (unramifiedCompactRepresentationEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ A χ).toIntertwiningMap.comp (J.comp
        (unramifiedCompactRepresentationEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).symm.toIntertwiningMap)
  invFun J :=
    (unramifiedCompactRepresentationEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ A χ).symm.toIntertwiningMap.comp (J.comp
        (unramifiedCompactRepresentationEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).toIntertwiningMap)
  left_inv J := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    simp only [Representation.IntertwiningMap.toLinearMap_apply,
      Representation.IntertwiningMap.comp_apply,
      Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply]
  right_inv J := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    simp only [Representation.IntertwiningMap.toLinearMap_apply,
      Representation.IntertwiningMap.comp_apply,
      Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply]
  map_add' J L := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change (unramifiedCompactRepresentationEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ A χ)
      (J ((unramifiedCompactRepresentationEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).symm f) +
       L ((unramifiedCompactRepresentationEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).symm f)) = _
    exact map_add _ _ _
  map_smul' c J := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change (unramifiedCompactRepresentationEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ A χ)
      (c • J ((unramifiedCompactRepresentationEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ A χ).symm f)) = _
    exact map_smul _ _ _

/-- The bundled forward transport is exactly the original compact operator. -/
@[simp]
theorem compactInductionIntertwinerEquiv_toLinearMap (χ : unramifiedCharacters ν)
    (J : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation) :
    (compactInductionIntertwinerEquiv h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
        hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A χ J).toLinearMap =
      compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J := rfl

end CompactTransport

section PolynomialTransport

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {L : Type uL} [Group L] [TopologicalSpace L] (e : L ≃ₜ* M)
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Polynomiality of the actual induction action survives identification of
the Levi with its literal ambient subgroup. -/
theorem unramifiedCompactRepresentation_transport_polynomial (g : G) :
    IsPolynomialOperatorOn Set.univ (fun χ =>
      unramifiedCompactRepresentation h hU hδ K hP hK hPK
        (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
        (fun i => (hν i).comp e.symm.continuous) hr A
        (unramifiedCharactersHomeomorph e ν χ.val) g) := by
  intro f
  obtain ⟨n, b, w, hf⟩ := unramifiedCompactRepresentation_polynomial h hU hδ
    K hP hK hPK (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
    (fun i => (hν i).comp e.symm.continuous) hr A g Set.univ f
  refine ⟨n, fun i => (unramifiedRegularFunctionsEquiv e ν).symm (b i), w, ?_⟩
  intro χ
  simpa only [unramifiedRegularFunctionsEquiv_symm_apply] using
    hf ⟨unramifiedCharactersHomeomorph e ν χ.val, Set.mem_univ _⟩

end PolynomialTransport

section ActualContinuation

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
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {Ω D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)
local notation "E" => compactInductionIntertwinerEquiv h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
  hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ νM hνM A
local notation "ρ₀" => (fun χ => unramifiedCompactRepresentation h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM hνM hr₀ A (χM χ))
local notation "ρ₁" => (fun χ => unramifiedCompactRepresentation h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM hνM hr₁ A (χM χ))
local notation "T" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM hνM hr₀
  h₁ hU₁ hδ₁ hP₁ hP₁K hr₁

variable (J : ∀ χ : Ω,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)

/-- The original actual intertwiners, bundled on their fixed compact carriers. -/
def compactInductionIntertwinerFamily (χ : Ω) :
    (ρ₀ χ.val).IntertwiningMap (ρ₁ χ.val) :=
  E (χM χ.val) (J χ)

@[simp]
theorem compactInductionIntertwinerFamily_toLinearMap (χ : Ω) :
    (compactInductionIntertwinerFamily L h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J χ).toLinearMap =
      T (χM χ.val) A (J χ) := rfl

local notation "Jc" => compactInductionIntertwinerFamily L h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
  hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J

/-- A supplied rationality proof constructs continuation data for the actual
compact-picture family, using one common denominator for the whole operator. -/
def compactInductionContinuationData
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hJ : IsRationalOperatorOn Ω (fun χ => T (χM χ.val) A (J χ))) :
    RationalOperatorContinuationData Ω (fun χ => (Jc χ).toLinearMap) :=
  rationalOperatorContinuation L hp hL hD hne hDΩ _ hJ

variable (p : RationalOperatorContinuationData Ω (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J χ)))
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)

/-- Continue the actual ambient intertwiners to the full nonzero locus of the
chosen denominator. Polynomiality of both actual actions is proved, not assumed. -/
def continuedInductionIntertwiner (χ : p.regularRegion) :
    (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ νM (χM χ.val) A).representation :=
  (E (χM χ.val)).symm
    (continuedIntertwiner L hp hL ρ₀ ρ₁
      (unramifiedCompactRepresentation_transport_polynomial h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        e νL hν hr₀ A)
      (unramifiedCompactRepresentation_transport_polynomial h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        e νL hν hr₁ A)
      Jc p hD hne hDΩ χ)

local notation "Jext" => continuedInductionIntertwiner L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
  hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J p hD hne hDΩ

include hp hL hD hne hDΩ

/-- Compact restriction of the continued actual map is precisely the constructed
rational operator continuation, with the original normalizations. -/
theorem continuedInductionIntertwiner_compact (χ : p.regularRegion) :
    T (χM χ.val) A (Jext χ) = p.continuedOperator χ := by
  have he := congrArg Representation.IntertwiningMap.toLinearMap
    ((E (χM χ.val)).apply_symm_apply
      (continuedIntertwiner L hp hL ρ₀ ρ₁
        (unramifiedCompactRepresentation_transport_polynomial h₀ hU₀ hδ₀ K hP₀ hK hP₀K
          e νL hν hr₀ A)
        (unramifiedCompactRepresentation_transport_polynomial h₁ hU₁ hδ₁ K hP₁ hK hP₁K
          e νL hν hr₁ A)
        Jc p hD hne hDΩ χ))
  exact he

/-- The continued actual ambient family is rational in the source's fixed
compact-picture sense. -/
theorem continuedInductionIntertwiner_rational :
    IsRationalOperatorOn p.regularRegion (fun χ => T (χM χ.val) A (Jext χ)) := by
  have he : (fun χ : p.regularRegion => T (χM χ.val) A (Jext χ)) = p.continuedOperator := by
    funext χ
    exact continuedInductionIntertwiner_compact L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J p hD hne hDΩ χ
  rw [he]
  exact p.continuedOperator_rational

/-- Restriction recovers the original actual ambient intertwiners. -/
theorem continuedInductionIntertwiner_agrees (χ : Ω) :
    Jext ⟨χ.val, p.subset_regularRegion χ.property⟩ = J χ := by
  have he := congrArg (E (χM χ.val)).symm
    (continuedIntertwiner_agrees L hp hL ρ₀ ρ₁
      (unramifiedCompactRepresentation_transport_polynomial h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        e νL hν hr₀ A)
      (unramifiedCompactRepresentation_transport_polynomial h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        e νL hν hr₁ A)
      Jc p hD hne hDΩ χ)
  exact he.trans ((E (χM χ.val)).symm_apply_apply (J χ))

/-- Different denominator/numerator choices yield the same actual ambient
intertwiners at every common regular parameter. -/
theorem continuedInductionIntertwiner_unique
    (q : RationalOperatorContinuationData Ω (fun χ => (Jc χ).toLinearMap))
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    Jext ⟨χ.val, χ.property.1⟩ =
      continuedInductionIntertwiner L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
        hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J q hD hne hDΩ
        ⟨χ.val, χ.property.2⟩ := by
  apply congrArg (E (χM χ.val)).symm
  exact continuedIntertwiner_unique L hp hL ρ₀ ρ₁
    (unramifiedCompactRepresentation_transport_polynomial h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      e νL hν hr₀ A)
    (unramifiedCompactRepresentation_transport_polynomial h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      e νL hν hr₁ A)
    Jc p hD hne hDΩ q χ

end ActualContinuation

end Langlands.Plancherel
