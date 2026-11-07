import Langlands.Representation.Plancherel.CompactIntertwiningContinuation

/-! # Representative transport for rational intertwiner continuations -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uI uV uW uV' uW'

namespace UnramifiedOperatorFamily.RationalOperatorContinuationData

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} {ν : I → (H →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω : Set (unramifiedCharacters ν)}
  {A : Ω → V →ₗ[ℂ] W}

/-- Transport the numerator by fixed linear maps, preserving the original
whole-operator denominator. No injectivity or finite dimensionality is needed. -/
def map (p : RationalOperatorContinuationData Ω A)
    (S : V' →ₗ[ℂ] V) (T : W →ₗ[ℂ] W') :
    RationalOperatorContinuationData Ω (fun χ => T.comp ((A χ).comp S)) where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator χ := T.comp ((p.numerator χ).comp S)
  polynomial := (p.polynomial.precomp S).postcomp T
  clears χ := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, p.clears χ, LinearMap.smul_apply, map_smul]

@[simp]
theorem map_regularRegion (p : RationalOperatorContinuationData Ω A)
    (S : V' →ₗ[ℂ] V) (T : W →ₗ[ℂ] W') :
    (p.map S T).regularRegion = p.regularRegion := rfl

/-- The continued value itself is transported by the same fixed maps. -/
theorem map_continuedOperator (p : RationalOperatorContinuationData Ω A)
    (S : V' →ₗ[ℂ] V) (T : W →ₗ[ℂ] W') (χ : p.regularRegion) :
    (p.map S T).continuedOperator χ = T.comp ((p.continuedOperator χ).comp S) := by
  apply LinearMap.ext
  intro v
  simp only [continuedOperator, map, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul]

end UnramifiedOperatorFamily.RationalOperatorContinuationData

section RationalNaturality

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

/-- A representative square on one common nonempty ambient open subset
persists on the intersection of two independently chosen regular loci.
The original regions and the chosen denominators may differ. -/
theorem rationalOperatorContinuationData_natural
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B)
    (S : V →ₗ[ℂ] V') (T : W →ₗ[ℂ] W')
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) (hDΛ : D ⊆ Λ)
    (hnat : ∀ χ (hχ : χ ∈ D),
      (B ⟨χ, hDΛ hχ⟩).comp S = T.comp (A ⟨χ, hDΩ hχ⟩))
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    (q.continuedOperator ⟨χ.val, χ.property.2⟩).comp S =
      T.comp (p.continuedOperator ⟨χ.val, χ.property.1⟩) := by
  apply rationalUnramifiedOperator_eq_of_eqOn_isOpen L hp hL hD hne
    (show D ⊆ p.regularRegion ∩ q.regularRegion from fun ψ hψ =>
      ⟨p.subset_regularRegion (hDΩ hψ), q.subset_regularRegion (hDΛ hψ)⟩)
    _ _
    ((q.continuedOperator_rational.restrict Set.inter_subset_right).precomp S)
    ((p.continuedOperator_rational.restrict Set.inter_subset_left).postcomp T)
    (fun ψ hψ => by
      rw [p.continuedOperator_agrees ⟨ψ, hDΩ hψ⟩,
        q.continuedOperator_agrees ⟨ψ, hDΛ hψ⟩]
      exact hnat ψ hψ)
    χ

end RationalNaturality

section CompactSquare

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
  {A : Langlands.SmoothRep.{0, uG, uV} ℂ M}
  {B : Langlands.SmoothRep.{0, uG, uW} ℂ M}

/-- Compact conjugation reflects as well as preserves representative squares. -/
theorem compactIntertwiningOperator_natural_iff (χ : unramifiedCharacters ν)
    (φ : A.representation.Equiv B.representation)
    (JA : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (JB : (UnramifiedLeviInduction h₀ hU₀ ν χ B).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ B).representation) :
    (∀ f, JB (inducedMap h₀ hU₀ (twistEquiv χ.val.toMonoidHom φ).toIntertwiningMap f) =
      inducedMap h₁ hU₁ (twistEquiv χ.val.toMonoidHom φ).toIntertwiningMap (JA f)) ↔
    (∀ f, compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ B JB (compactInductionPictureEquiv h₀ K φ f) =
      compactInductionPictureEquiv h₁ K φ
        (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
          h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A JA f)) := by
  constructor
  · exact compactIntertwiningOperator_natural h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ φ JA JB
  · intro hJ f
    have hc := hJ
      (unramifiedLeviInductionCompactEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ χ A f)
    simp only [compactIntertwiningOperator, LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
    rw [unramifiedLeviInductionCompactEquiv_symm_natural,
      LinearEquiv.symm_apply_apply] at hc
    apply (unramifiedLeviInductionCompactEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ χ B).injective
    rw [unramifiedLeviInductionCompactEquiv_natural]
    exact hc

end CompactSquare

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
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (B : Langlands.SmoothRep.{0, uG, uW} ℂ M)
  {Ω Λ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)
local notation "T" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁

variable
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
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (JA χ)))
  (q : RationalOperatorContinuationData Λ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (JB χ)))
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) (hDΛ : D ⊆ Λ)
  (φ : A.representation.Equiv B.representation)
  (hnat : ∀ χ (hχ : χ ∈ D)
    (f : UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ) A),
    JB ⟨χ, hDΛ hχ⟩
        (inducedMap h₀ hU₀
          (twistEquiv (unramifiedCharactersHomeomorph e
            (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
          f) =
      inducedMap h₁ hU₁
        (twistEquiv (unramifiedCharactersHomeomorph e
          (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
        (JA ⟨χ, hDΩ hχ⟩ f))

include hp hL hD hne hDΩ hDΛ hnat

/-- The original representative square propagates to the independent
compact continuations on their common regular locus. -/
theorem continuedCompactIntertwiner_natural
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (f : CompactInductionPicture h₀ K A) :
    q.continuedOperator ⟨χ.val, χ.property.2⟩ (compactInductionPictureEquiv h₀ K φ f) =
      compactInductionPictureEquiv h₁ K φ (p.continuedOperator ⟨χ.val, χ.property.1⟩ f) := by
  have he := rationalOperatorContinuationData_natural L hp hL p q
    (compactInductionPictureEquiv h₀ K φ).toLinearMap
    (compactInductionPictureEquiv h₁ K φ).toLinearMap hD hne hDΩ hDΛ
    (fun ψ hψ => by
      apply LinearMap.ext
      intro v
      exact compactIntertwiningOperator_natural h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (χM ψ) φ (JA ⟨ψ, hDΩ hψ⟩) (JB ⟨ψ, hDΛ hψ⟩) (hnat ψ hψ) v)
    χ
  exact congrArg (fun Z => Z f) he

local notation "JextA" => continuedInductionIntertwiner L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  JA p hD hne hDΩ
local notation "JextB" => continuedInductionIntertwiner L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν B
  JB q hD hne hDΛ

/-- Independent rational continuations preserve the inducing-representative
square on the actual normalized induction spaces. -/
theorem continuedInductionIntertwiner_natural
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (f : UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A) :
    JextB ⟨χ.val, χ.property.2⟩
        (inducedMap h₀ hU₀ (twistEquiv (χM χ.val).val.toMonoidHom φ).toIntertwiningMap f) =
      inducedMap h₁ hU₁ (twistEquiv (χM χ.val).val.toMonoidHom φ).toIntertwiningMap
        (JextA ⟨χ.val, χ.property.1⟩ f) := by
  refine ((compactIntertwiningOperator_natural_iff
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ νM hνM
    (χM χ.val) φ (JextA ⟨χ.val, χ.property.1⟩) (JextB ⟨χ.val, χ.property.2⟩)).mpr ?_) f
  intro v
  have hc := continuedCompactIntertwiner_natural L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
    e hν A B JA JB p q hD hne hDΩ hDΛ φ hnat χ v
  have hA := congrArg (fun Z => Z v)
    (continuedInductionIntertwiner_compact L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
      e hν A JA p hD hne hDΩ ⟨χ.val, χ.property.1⟩)
  have hB := congrArg (fun Z => Z (compactInductionPictureEquiv h₀ K φ v))
    (continuedInductionIntertwiner_compact L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
      e hν B JB q hD hne hDΛ ⟨χ.val, χ.property.2⟩)
  exact hB.trans (hc.trans
    (congrArg (compactInductionPictureEquiv h₁ K φ) hA).symm)

end ActualInduction

end Langlands.Plancherel
