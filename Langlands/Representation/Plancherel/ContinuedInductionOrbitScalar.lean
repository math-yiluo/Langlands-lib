import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarOrbit
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Orbit scalars for continued operators on actual normalized induction -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uH uG uI uV uW

section Pullback

variable {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI}
  (e : H ≃ₜ* M) (ν : I → (H →* ℝ≥0ˣ))
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

local notation "νM" =>
  (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν

/-- Reflect a twisting equivalence from the canonical smooth pullback to
the original Levi subgroup, keeping its linear map. -/
def baseTwistEquivOfPullback (τ : unramifiedCharacters ν)
    (a : ((SmoothRep.pullback e A).twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv
        (SmoothRep.pullback e B).representation) :
    (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation :=
  Representation.Equiv.mk a.toLinearEquiv (fun m => by
    have ha := a.isIntertwining' (e.symm m)
    change a.toLinearMap.comp
      ((τ.val (e.symm m) : ℂ) • A.representation (e (e.symm m))) =
        (B.representation (e (e.symm m))).comp a.toLinearMap at ha
    change a.toLinearMap.comp
      ((τ.val (e.symm m) : ℂ) • A.representation m) =
        (B.representation m).comp a.toLinearMap
    simpa only [e.apply_symm_apply] using ha)

@[simp]
theorem baseTwistEquivOfPullback_apply (τ : unramifiedCharacters ν)
    (a : ((SmoothRep.pullback e A).twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv
        (SmoothRep.pullback e B).representation) (v : A) :
    baseTwistEquivOfPullback e ν τ a v = a v := rfl

/-- Pull a Levi twisting equivalence back to the original character chart,
again keeping its linear map. -/
def pullbackBaseTwistEquiv (τ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation) :
    ((SmoothRep.pullback e A).twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv
        (SmoothRep.pullback e B).representation :=
  Representation.Equiv.mk a.toLinearEquiv (fun h => by
    have ha := a.isIntertwining' (e h)
    change a.toLinearMap.comp
      ((τ.val (e.symm (e h)) : ℂ) • A.representation (e h)) =
        (B.representation (e h)).comp a.toLinearMap at ha
    change a.toLinearMap.comp
      ((τ.val h : ℂ) • A.representation (e h)) =
        (B.representation (e h)).comp a.toLinearMap
    simpa only [e.symm_apply_apply] using ha)

@[simp]
theorem pullbackBaseTwistEquiv_apply (τ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (v : A) :
    pullbackBaseTwistEquiv e ν τ a v = a v := rfl

/-- The full twist stabilizers of the original object and its canonical
pullback agree under the actual character homeomorphism. -/
theorem mem_smoothRepUnramifiedTwistStabilizer_pullback_iff
    (τ : unramifiedCharacters ν) :
    τ ∈ smoothRepUnramifiedTwistStabilizer ν (SmoothRep.pullback e A) ↔
      χM τ ∈ smoothRepUnramifiedTwistStabilizer νM A := by
  change SmoothRep.isoClass ((SmoothRep.pullback e A).twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)) = SmoothRep.isoClass (SmoothRep.pullback e A) ↔
    SmoothRep.isoClass (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))) = SmoothRep.isoClass A
  rw [SmoothRep.isoClass_eq_iff, SmoothRep.isoClass_eq_iff]
  exact ⟨fun ⟨a⟩ => ⟨SmoothRep.mkIso
      (baseTwistEquivOfPullback e ν τ (SmoothRep.equivOfIso a))⟩,
    fun ⟨a⟩ => ⟨SmoothRep.mkIso
      (pullbackBaseTwistEquiv e ν τ (SmoothRep.equivOfIso a))⟩⟩

/-- An element of the actual pullback stabilizer supplies a genuine
twisting equivalence of the inducing representation on the Levi subgroup. -/
def stabilizerBaseTwistEquiv
    (τ : smoothRepUnramifiedTwistStabilizer ν (SmoothRep.pullback e A)) :
    (A.twist (χM τ.val).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ.val))).representation.Equiv A.representation :=
  SmoothRep.equivOfIso (Classical.choice
    ((SmoothRep.isoClass_eq_iff _ _).mp
      ((mem_smoothRepUnramifiedTwistStabilizer_pullback_iff e ν τ.val).mp τ.property)))

end Pullback

section InductionComparison

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (e : H ≃ₜ* M) {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (A : SmoothRep.{0, uG, uV} ℂ M)
  {Ω₁₀ Ω₀₁ : Set (unramifiedCharacters ν)}

local notation "νM" =>
  (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν

variable
  (J₁₀ : ∀ χ : Ω₁₀,
    (UnramifiedLeviInduction h₀ hU₀ (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom) (unramifiedCharactersHomeomorph e ν χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom) (unramifiedCharactersHomeomorph e ν χ.val) A).representation)
  (J₀₁ : ∀ χ : Ω₀₁,
    (UnramifiedLeviInduction h₁ hU₁ (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom) (unramifiedCharactersHomeomorph e ν χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom) (unramifiedCharactersHomeomorph e ν χ.val) A).representation)

/-- Original self-comparisons implemented by actual induced maps from a
single equivalence of the inducing representation with a twist of itself. -/
structure InductionSelfBaseChangeData (τ : unramifiedCharacters ν) where
  twistEquiv : (A.twist (χM τ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv A.representation
  forwardRegion : Set (unramifiedCharacters ν)
  reverseRegion : Set (unramifiedCharacters ν)
  forward_isOpen : IsOpen forwardRegion
  forward_nonempty : forwardRegion.Nonempty
  forward_in_translation : forwardRegion ⊆ (unramifiedParameterTranslation ν τ) ⁻¹' Ω₁₀
  forward_in_original : forwardRegion ⊆ Ω₁₀
  reverse_isOpen : IsOpen reverseRegion
  reverse_nonempty : reverseRegion.Nonempty
  reverse_in_translation : reverseRegion ⊆ (unramifiedParameterTranslation ν τ) ⁻¹' Ω₀₁
  reverse_in_original : reverseRegion ⊆ Ω₀₁
  forward_natural : ∀ χ (hχ : χ ∈ forwardRegion)
    (f : UnramifiedLeviInduction h₀ hU₀ νM (χM (τ * χ)) A),
    J₁₀ ⟨χ, forward_in_original hχ⟩
        (inducedMap h₀ hU₀
          (transportedBaseTwistEquiv e ν τ χ twistEquiv).toIntertwiningMap f) =
      inducedMap h₁ hU₁
        (transportedBaseTwistEquiv e ν τ χ twistEquiv).toIntertwiningMap
        (J₁₀ ⟨τ * χ, forward_in_translation hχ⟩ f)
  reverse_natural : ∀ χ (hχ : χ ∈ reverseRegion)
    (f : UnramifiedLeviInduction h₁ hU₁ νM (χM (τ * χ)) A),
    J₀₁ ⟨χ, reverse_in_original hχ⟩
        (inducedMap h₁ hU₁
          (transportedBaseTwistEquiv e ν τ χ twistEquiv).toIntertwiningMap f) =
      inducedMap h₀ hU₀
        (transportedBaseTwistEquiv e ν τ χ twistEquiv).toIntertwiningMap
        (J₀₁ ⟨τ * χ, reverse_in_translation hχ⟩ f)

variable
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)

set_option quotPrecheck false in
local notation "hνM" => (fun i => (hν i).comp e.symm.continuous)
local notation "T₁₀" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
local notation "T₀₁" => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM hνM hr₁ h₀ hU₀ hδ₀ hP₀ hP₀K hr₀

/-- Compact restriction turns the actual original induction squares into
the fixed-carrier self-comparisons used for rational scalar descent. -/
def InductionSelfBaseChangeData.toSelfBaseChangeData
    {τ : unramifiedCharacters ν}
    (d : InductionSelfBaseChangeData h₀ hU₀ h₁ hU₁ e ν A J₁₀ J₀₁ τ) :
    SelfBaseChangeData Ω₁₀ Ω₀₁
      (fun χ => T₁₀ (χM χ.val) A (J₁₀ χ))
      (fun χ => T₀₁ (χM χ.val) A (J₀₁ χ)) τ where
  source := (compactInductionBaseChangeEquiv h₀ K hP₀ hK
    νM hνM hr₀ (χM τ) d.twistEquiv).toLinearEquiv
  target := (compactInductionBaseChangeEquiv h₁ K hP₁ hK
    νM hνM hr₁ (χM τ) d.twistEquiv).toLinearEquiv
  forwardRegion := d.forwardRegion
  reverseRegion := d.reverseRegion
  forward_isOpen := d.forward_isOpen
  forward_nonempty := d.forward_nonempty
  forward_in_translation := d.forward_in_translation
  forward_in_original := d.forward_in_original
  reverse_isOpen := d.reverse_isOpen
  reverse_nonempty := d.reverse_nonempty
  reverse_in_translation := d.reverse_in_translation
  reverse_in_original := d.reverse_in_original
  forward_natural χ hχ := by
    apply LinearMap.ext
    intro f
    exact ((compactIntertwiningOperator_transportedBaseChange_iff
      e ν h₀ hU₀ hδ₀ K hP₀ hK hP₀K hν hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ τ χ d.twistEquiv
      (J₁₀ ⟨τ * χ, d.forward_in_translation hχ⟩)
      (J₁₀ ⟨χ, d.forward_in_original hχ⟩)).mp (d.forward_natural χ hχ)) f
  reverse_natural χ hχ := by
    apply LinearMap.ext
    intro f
    exact ((compactIntertwiningOperator_transportedBaseChange_iff
      e ν h₁ hU₁ hδ₁ K hP₁ hK hP₁K hν hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ τ χ d.twistEquiv
      (J₀₁ ⟨τ * χ, d.reverse_in_translation hχ⟩)
      (J₀₁ ⟨χ, d.reverse_in_original hχ⟩)).mp (d.reverse_natural χ hχ)) f

end InductionComparison

section ActualOrbitScalar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints L)]
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
  {Ω₁₀ Ω₀₁ D₁₀ D₀₁ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)
local notation "T₁₀" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
local notation "T₀₁" => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM hνM hr₁ h₀ hU₀ hδ₀ hP₀ hP₀K hr₀

variable
  (J₁₀ : ∀ χ : Ω₁₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (J₀₁ : ∀ χ : Ω₀₁,
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (p : RationalOperatorContinuationData Ω₁₀ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₁₀ χ)))
  (q : RationalOperatorContinuationData Ω₀₁ (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₀₁ χ)))
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty) (hD₁₀Ω : D₁₀ ⊆ Ω₁₀)
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty) (hD₀₁Ω : D₀₁ ⊆ Ω₀₁)

local notation "R" => p.regularRegion ∩ q.regularRegion

local notation "π" => SmoothRep.pullback e A
local notation "fC" => continuedCompositeRationalScalar L hp hL p q
  (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)

/-- Any invariant presentation of the actual compact-composite fraction
recovers its extracted coefficient at every common regular parameter. -/
theorem continuedInductionCompositeOrbitScalar_value
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ)
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ))
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
      (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ =
        p.continuedCompositeScalar q v ℓ χ :=
  r.orbitValue_eq_scalarPresentation L hp hL π
    (scalarCoefficientPresentation (p.continuedComposite q)
      (p.continuedComposite_rational q) v ℓ)
    (continuedCompositeRegion_nonempty L hp hL p q
      (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)) rfl χ hχ

section GenericIrreducibility

variable [TopologicalSpace.SeparableSpace G]
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => MonoidHom.comp (rationalNormCharacters L ψ).toMul
        e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

local notation "SC" => continuedInductionComposite_generic_scalar L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hi

include hD₁₀ hD₀₁ hD hne hi

/-- Actual induced self-comparisons and generic induced irreducibility
prove full stabilizer fixedness of the extracted rational scalar. -/
theorem continuedInductionCompositeRationalScalar_stabilizer_fixed
    (hd : ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      Nonempty (InductionSelfBaseChangeData h₀ hU₀ h₁ hU₁ e νL A J₁₀ J₀₁ τ.val))
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val (fC v ℓ) = fC v ℓ := by
  apply continuedCompositeRationalScalar_subgroup_fixed L hp hL p q
    (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) _ _ hD hne
    (fun χ hχ => SC ⟨χ.val, hχ, χ.property⟩) v ℓ hℓ
  intro τ
  obtain ⟨d⟩ := hd τ
  exact ⟨InductionSelfBaseChangeData.toSelfBaseChangeData
    h₀ hU₀ h₁ hU₁ e νL A J₁₀ J₀₁
    hδ₀ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hν hr₀ hr₁ d⟩

/-- Construct an orbit presentation from genuine induced comparisons.
The representation defining the orbit is the inducing object's canonical
pullback, and generic scalarity is derived from induced irreducibility. -/
def continuedInductionCompositeOrbitScalarPresentation
    [Finite (smoothRepUnramifiedTwistStabilizer νL π)]
    (hd : ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      Nonempty (InductionSelfBaseChangeData h₀ hU₀ h₁ hU₁ e νL A J₁₀ J₀₁ τ.val))
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ) :=
  Classical.choice (unramifiedTwistOrbitScalarPresentation_exists L hp hL π _
    (continuedInductionCompositeRationalScalar_stabilizer_fixed L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi hd v ℓ hℓ))

/-- The full actual induced composite is the orbit scalar times identity
where both operators and the chosen invariant presentation are regular. -/
theorem continuedInductionComposite_eq_orbitScalar
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ))
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    continuedInductionComposite L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω χ =
        r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
          (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ •
            Representation.IntertwiningMap.id
              (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation := by
  have hv := continuedInductionCompositeOrbitScalar_value L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω v ℓ r χ hχ
  exact (continuedInductionComposite_eq_scalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi v ℓ hℓ χ).trans
      (congrArg (fun c : ℂ => c • Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation) hv.symm)

end GenericIrreducibility

end ActualOrbitScalar

end Langlands.Plancherel
