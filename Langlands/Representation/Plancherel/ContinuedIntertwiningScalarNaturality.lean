import Langlands.Representation.Plancherel.ContinuedIntertwiningScalar
import Langlands.Representation.Plancherel.ContinuedIntertwiningNaturality

/-! # Representative invariance of continued composite scalars -/

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
  {Ω Λ : Set (unramifiedCharacters ν)}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}

/-- Change the source and target representatives while retaining the
original whole-operator denominator. -/
def congr (p : RationalOperatorContinuationData Ω A)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W') :
    RationalOperatorContinuationData Ω
      (fun χ => T.toLinearMap.comp ((A χ).comp S.symm.toLinearMap)) :=
  p.map S.symm.toLinearMap T.toLinearMap

@[simp]
theorem congr_regularRegion (p : RationalOperatorContinuationData Ω A)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W') :
    (p.congr S T).regularRegion = p.regularRegion := rfl

theorem congr_continuedOperator (p : RationalOperatorContinuationData Ω A)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W') (χ : p.regularRegion) :
    (p.congr S T).continuedOperator χ =
      T.toLinearMap.comp ((p.continuedOperator χ).comp S.symm.toLinearMap) :=
  p.map_continuedOperator S.symm.toLinearMap T.toLinearMap χ

/-- The intermediate representative cancels in the actual continued
composite, leaving conjugation by the source representative. -/
theorem continuedComposite_congr
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) (v : V) :
    (p.congr S T).continuedComposite (q.congr T S) ⟨χ.val, χ.property⟩ (S v) =
      S (p.continuedComposite q χ v) := by
  simp only [continuedComposite, continuedOperator, congr, map,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    map_smul, LinearEquiv.symm_apply_apply]

/-- Transporting a vector and pulling back its functional preserves its
composite coefficient, even when the composite is not scalar. -/
theorem continuedCompositeScalar_congr
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    (p.congr S T).continuedCompositeScalar (q.congr T S)
        (S v) (ℓ.comp S.symm.toLinearMap) ⟨χ.val, χ.property⟩ =
      p.continuedCompositeScalar q v ℓ χ := by
  change ℓ (S.symm
    ((p.congr S T).continuedComposite (q.congr T S) ⟨χ.val, χ.property⟩ (S v))) =
      ℓ (p.continuedComposite q χ v)
  rw [continuedComposite_congr, LinearEquiv.symm_apply_apply]

end UnramifiedOperatorFamily.RationalOperatorContinuationData

section ActualCharacters

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
  {Ω Λ Ω' Λ' D E :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  {A' : Ω' → V' →ₗ[ℂ] W'} {B' : Λ' → W' →ₗ[ℂ] V'}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)

include hp hL

/-- The coefficient fraction is unchanged by simultaneous conjugation of
the continuation data and transport of the extraction pair. -/
theorem continuedCompositeRationalScalar_congr
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL (p.congr S T) (q.congr T S)
        hΩ hΛ (S v) (ℓ.comp S.symm.toLinearMap) =
      continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ := by
  have hR := continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hR hR (p.regularRegion_isOpen.inter q.regularRegion_isOpen) hR
    Set.Subset.rfl Set.Subset.rfl
  intro χ hχ
  exact p.continuedCompositeScalar_congr q S T v ℓ ⟨χ, hχ⟩

variable
  (p' : RationalOperatorContinuationData Ω' A')
  (q' : RationalOperatorContinuationData Λ' B')
  (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
  (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω) (hDΩ' : D ⊆ Ω')
  (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ) (hEΛ' : E ⊆ Λ')
  (hnatA : ∀ χ (hχ : χ ∈ D),
    (A' ⟨χ, hDΩ' hχ⟩).comp S.toLinearMap =
      T.toLinearMap.comp (A ⟨χ, hDΩ hχ⟩))
  (hnatB : ∀ χ (hχ : χ ∈ E),
    (B' ⟨χ, hEΛ' hχ⟩).comp T.toLinearMap =
      S.toLinearMap.comp (B ⟨χ, hEΛ hχ⟩))

include hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB

/-- Separate original representative squares give the composite square
on the intersection of all four independently chosen regular regions.
The forward and reverse original open sets need not intersect. -/
theorem continuedComposite_natural
    (χ : ↥((p.regularRegion ∩ q.regularRegion) ∩
      (p'.regularRegion ∩ q'.regularRegion))) (v : V) :
    p'.continuedComposite q' ⟨χ.val, χ.property.2⟩ (S v) =
      S (p.continuedComposite q ⟨χ.val, χ.property.1⟩ v) := by
  have hA := congrArg (fun Z => Z v)
    (rationalOperatorContinuationData_natural L hp hL p p'
      S.toLinearMap T.toLinearMap hD hneD hDΩ hDΩ' hnatA
      ⟨χ.val, χ.property.1.1, χ.property.2.1⟩)
  have hB := congrArg
    (fun Z => Z (p.continuedOperator ⟨χ.val, χ.property.1.1⟩ v))
    (rationalOperatorContinuationData_natural L hp hL q q'
      T.toLinearMap S.toLinearMap hE hneE hEΛ hEΛ' hnatB
      ⟨χ.val, χ.property.1.2, χ.property.2.2⟩)
  change q'.continuedOperator ⟨χ.val, χ.property.2.2⟩
      (p'.continuedOperator ⟨χ.val, χ.property.2.1⟩ (S v)) =
    S (q.continuedOperator ⟨χ.val, χ.property.1.2⟩
      (p.continuedOperator ⟨χ.val, χ.property.1.1⟩ v))
  change p'.continuedOperator _ (S v) = T (p.continuedOperator _ v) at hA
  change q'.continuedOperator _ (T _) = S (q.continuedOperator _ _) at hB
  rw [hA]
  exact hB

/-- Arbitrary independent continuation data preserve the rational
coefficient fraction when the extraction pair is transported. -/
theorem continuedCompositeRationalScalar_natural
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL p q
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ =
      continuedCompositeRationalScalar L hp hL p' q'
        (hneD.mono hDΩ') (hneE.mono hEΛ') (S v) (ℓ.comp S.symm.toLinearMap) := by
  have hR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  have hR' := p'.regularRegion_isOpen.inter q'.regularRegion_isOpen
  have hneR := continuedCompositeRegion_nonempty L hp hL p q
    (hneD.mono hDΩ) (hneE.mono hEΛ)
  have hneR' := continuedCompositeRegion_nonempty L hp hL p' q'
    (hneD.mono hDΩ') (hneE.mono hEΛ')
  have hneRR := (continuedCompositeRegion_dense L hp hL p' q'
    (hneD.mono hDΩ') (hneE.mono hEΛ')).inter_open_nonempty
      (p.regularRegion ∩ q.regularRegion) hR hneR
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hneR hneR' (hR.inter hR') hneRR Set.inter_subset_left Set.inter_subset_right
  intro χ hχ
  change ℓ (p.continuedComposite q ⟨χ, hχ.1⟩ v) =
    ℓ (S.symm (p'.continuedComposite q' ⟨χ, hχ.2⟩ (S v)))
  rw [continuedComposite_natural L hp hL p q p' q' S T
    hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB ⟨χ, hχ⟩,
    LinearEquiv.symm_apply_apply]

/-- Generic scalarity on just the first representative makes its rational
scalar independent of both representatives, all four continuation choices
and arbitrary normalized extraction pairs. The scalarity open set need
not avoid any denominator. -/
theorem continuedCompositeRationalScalar_representative_independent
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : V') (m : V' →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p q
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ =
      continuedCompositeRationalScalar L hp hL p' q'
        (hneD.mono hDΩ') (hneE.mono hEΛ') w m := by
  have hR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  have hR' := p'.regularRegion_isOpen.inter q'.regularRegion_isOpen
  have hneR := continuedCompositeRegion_nonempty L hp hL p q
    (hneD.mono hDΩ) (hneE.mono hEΛ)
  have hneR' := continuedCompositeRegion_nonempty L hp hL p' q'
    (hneD.mono hDΩ') (hneE.mono hEΛ')
  have hneUR := (continuedCompositeRegion_dense L hp hL p q
    (hneD.mono hDΩ) (hneE.mono hEΛ)).inter_open_nonempty U hU hneU
  have hsca := rationalUnramifiedScalarContinuation L hp hL
    (hU.inter hR) hneUR Set.inter_subset_right
    (p.continuedComposite q) (p.continuedComposite_rational q) v ℓ hℓ
    (fun χ hχ => hscalar ⟨χ, hχ.2⟩ hχ.1)
  have hneRR := (continuedCompositeRegion_dense L hp hL p' q'
    (hneD.mono hDΩ') (hneE.mono hEΛ')).inter_open_nonempty
      (p.regularRegion ∩ q.regularRegion) hR hneR
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hneR hneR' (hR.inter hR') hneRR Set.inter_subset_left Set.inter_subset_right
  intro χ hχ
  have hsca' : p'.continuedComposite q' ⟨χ, hχ.2⟩ =
      endomorphismScalarCoefficient v ℓ
        (p.continuedComposite q ⟨χ, hχ.1⟩) • LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := S.surjective z
    rw [continuedComposite_natural L hp hL p q p' q' S T
      hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB ⟨χ, hχ⟩]
    have hval := congrArg (fun Z => Z y) (hsca ⟨χ, hχ.1⟩)
    exact (congrArg S hval).trans (by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul])
  rw [hsca', endomorphismScalarCoefficient_smul_id w m hm]

end ActualCharacters

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
  {Ω₁₀ Ω₀₁ Ω₁₀' Ω₀₁' D₁₀ D₀₁ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)

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
  (J₁₀' : ∀ χ : Ω₁₀',
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation)
  (J₀₁' : ∀ χ : Ω₀₁',
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation.IntertwiningMap
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation)
  (p' : RationalOperatorContinuationData Ω₁₀' (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (J₁₀' χ)))
  (q' : RationalOperatorContinuationData Ω₀₁' (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (J₀₁' χ)))
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ Ω₁₀) (hD₁₀Ω' : D₁₀ ⊆ Ω₁₀')
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ Ω₀₁) (hD₀₁Ω' : D₀₁ ⊆ Ω₀₁')
  (φ : A.representation.Equiv B.representation)
  (hnat₁₀ : ∀ χ (hχ : χ ∈ D₁₀)
    (f : UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ) A),
    J₁₀' ⟨χ, hD₁₀Ω' hχ⟩
        (inducedMap h₀ hU₀
          (twistEquiv (unramifiedCharactersHomeomorph e
            (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
          f) =
      inducedMap h₁ hU₁
        (twistEquiv (unramifiedCharactersHomeomorph e
          (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
        (J₁₀ ⟨χ, hD₁₀Ω hχ⟩ f))
  (hnat₀₁ : ∀ χ (hχ : χ ∈ D₀₁)
    (f : UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ) A),
    J₀₁' ⟨χ, hD₀₁Ω' hχ⟩
        (inducedMap h₁ hU₁
          (twistEquiv (unramifiedCharactersHomeomorph e
            (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
          f) =
      inducedMap h₀ hU₀
        (twistEquiv (unramifiedCharactersHomeomorph e
          (fun ψ => (rationalNormCharacters L ψ).toMul) χ).val.toMonoidHom φ).toIntertwiningMap
        (J₀₁ ⟨χ, hD₀₁Ω hχ⟩ f))

include hp hL hD₁₀ hne₁₀ hD₁₀Ω hD₁₀Ω' hD₀₁ hne₀₁ hD₀₁Ω hD₀₁Ω' hnat₁₀ hnat₀₁

/-- The rational scalar of independently continued actual induction
intertwiners is independent of the inducing representative, all four
continuation data and normalized extraction pairs. Only the first
representative needs a generic induced-irreducibility premise. -/
theorem continuedInductionCompositeRationalScalar_representative_independent
    [TopologicalSpace.SeparableSpace G]
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hi : ∀ χ ∈ U,
      (UnramifiedLeviInduction h₀ hU₀ νM (χM χ) A).IsIrreducible)
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : CompactInductionPicture h₀ K B)
    (m : CompactInductionPicture h₀ K B →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p q
        (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) v ℓ =
      continuedCompositeRationalScalar L hp hL p' q'
        (hne₁₀.mono hD₁₀Ω') (hne₀₁.mono hD₀₁Ω') w m := by
  refine continuedCompositeRationalScalar_representative_independent L hp hL
    p q p' q' (compactInductionPictureEquiv h₀ K φ).toLinearEquiv
    (compactInductionPictureEquiv h₁ K φ).toLinearEquiv
    hD₁₀ hne₁₀ hD₁₀Ω hD₁₀Ω' hD₀₁ hne₀₁ hD₀₁Ω hD₀₁Ω'
    ?_ ?_ hU hneU ?_ v ℓ hℓ w m hm
  · intro χ hχ
    apply LinearMap.ext
    intro z
    exact compactIntertwiningOperator_natural h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (χM χ) φ
      (J₁₀ ⟨χ, hD₁₀Ω hχ⟩) (J₁₀' ⟨χ, hD₁₀Ω' hχ⟩) (hnat₁₀ χ hχ) z
  · intro χ hχ
    apply LinearMap.ext
    intro z
    exact compactIntertwiningOperator_natural h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      νM hνM hr₁ h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (χM χ) φ
      (J₀₁ ⟨χ, hD₀₁Ω hχ⟩) (J₀₁' ⟨χ, hD₀₁Ω' hχ⟩) (hnat₀₁ χ hχ) z
  · intro χ hχ
    exact continuedInductionComposite_generic_scalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hi
      ⟨χ.val, hχ, χ.property⟩

end ActualInduction

end Langlands.Plancherel
