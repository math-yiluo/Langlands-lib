import Langlands.Representation.Plancherel.DynamicOppositePairScalar
import Langlands.Representation.Plancherel.StandardInductionScalarSymmetry

/-! # Proof that the scalar `j` depends only on the opposite pair `{P, P̄}` -/

noncomputable section

universe u uG uI uI' uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

/-! ### Constructions depending on an unramified parameter only through its value -/

section ParameterValue

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G}
  {I : Type uI} {I' : Type uI'} {ν : I → (M →* ℝ≥0ˣ)} {ν' : I' → (M →* ℝ≥0ˣ)}

omit [LocallyCompactSpace G] in
/-- Twisting by an unramified parameter depends only on its underlying character. -/
theorem unramifiedTwist_congr (A : SmoothRep.{0, uG, uV} ℂ M)
    (χ : unramifiedCharacters ν) (χ' : unramifiedCharacters ν') (h : χ.val = χ'.val) :
    A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) =
      A.twist χ'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' χ') := by
  obtain ⟨c, hc⟩ := χ
  obtain ⟨c', hc'⟩ := χ'
  obtain rfl : c = c' := h
  rfl

variable {P₀ P₁ U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)

/-- The actual normalized induction at an unramified parameter depends only on its
underlying character. -/
theorem unramifiedLeviInduction_congr (A : SmoothRep.{0, uG, uV} ℂ M)
    (χ : unramifiedCharacters ν) (χ' : unramifiedCharacters ν') (h : χ.val = χ'.val) :
    UnramifiedLeviInduction h₀ hU₀ ν χ A = UnramifiedLeviInduction h₀ hU₀ ν' χ' A := by
  obtain ⟨c, hc⟩ := χ
  obtain ⟨c', hc'⟩ := χ'
  obtain rfl : c = c' := h
  rfl

variable [T2Space G]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)

/-- The compact picture of the actual full-source standard integral at an unramified
parameter depends only on its underlying character. -/
theorem compactFullSourceIntertwiner_congr (A : SmoothRep.{0, uG, uV} ℂ M)
    (hν : ∀ i, Continuous (ν i)) (hν' : ∀ i, Continuous (ν' i))
    (χ : unramifiedCharacters ν) (χ' : unramifiedCharacters ν') (h : χ.val = χ'.val)
    (hfull : domain h₀ hU₀ U₁
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) q₁₀ = ⊤)
    (hfull' : domain h₀ hU₀ U₁
      (A.twist χ'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' χ')) q₁₀ = ⊤) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A
        (fullSourceIntertwiner h₀ hU₀ h₁ hU₁
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
          q₁₀ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ hfull) =
      compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν' hν' hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ' A
        (fullSourceIntertwiner h₀ hU₀ h₁ hU₁
          (A.twist χ'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' χ'))
          q₁₀ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ hfull') := by
  obtain ⟨c, hc⟩ := χ
  obtain ⟨c', hc'⟩ := χ'
  obtain rfl : c = c' := h
  rfl

end ParameterValue

/-! ### Restriction of continuation data along a group-scheme morphism -/

section ContinuationRestriction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {L L' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine L.X.left] [IsAffine L'.X.left]

local instance pairScalarPointTopology (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine H.X.left] : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "XL" => unramifiedCharacters (fun φ => (rationalNormCharacters L φ).toMul)
set_option hygiene false in
local notation "XL'" => unramifiedCharacters (fun φ => (rationalNormCharacters L' φ).toMul)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Continuation data along `z' ↦ z' ∘ f`.** Continuation data of a family `A` on `Ω`
restrict along the character map `rationalUnramifiedCharacterRestrict f` to continuation data of
any family `A'` on `Ω'` that is `A` read through this map: the denominator and numerators are
precomposed with the character map. -/
def continuationRestrict (f : L ⟶ L') {Ω : Set XL} {A : Ω → V →ₗ[ℂ] W}
    (p : RationalOperatorContinuationData Ω A) {Ω' : Set XL'} {A' : Ω' → V →ₗ[ℂ] W}
    (hΩ : ∀ z ∈ Ω', rationalUnramifiedCharacterRestrict f z ∈ Ω)
    (hA : ∀ z : Ω', A' z = A ⟨rationalUnramifiedCharacterRestrict f z.val, hΩ z.val z.property⟩) :
    RationalOperatorContinuationData Ω' A' where
  denominator := rationalUnramifiedRegularFunctionsMap f p.denominator
  denominator_nonzero z := p.denominator_nonzero ⟨_, hΩ z.val z.property⟩
  numerator z := p.numerator (rationalUnramifiedCharacterRestrict f z)
  polynomial v := by
    obtain ⟨n, b, w, hb⟩ := p.polynomial v
    exact ⟨n, fun i => rationalUnramifiedRegularFunctionsMap f (b i), w,
      fun z => hb ⟨_, Set.mem_univ _⟩⟩
  clears z := by
    rw [hA z]
    exact p.clears ⟨_, hΩ z.val z.property⟩

variable (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  (hp' : Continuous (rationalValuationImageProjection L'))
  (hL' : GroupScheme.IsConnectedReductive L')

/-- **Transport of the continued composite scalar.** If the two families on the side of
`L'` are those on the side of `L` read through `z' ↦ z' ∘ iso`, their continued composite
scalars correspond under the function-field isomorphism of `iso`. The continuations on the side
of `L'` are arbitrary; their original regions contain nonempty open sets. -/
theorem continuedCompositeRationalScalar_transport (iso : L ≅ L')
    {Ω Λ : Set XL} {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    {Ω' Λ' : Set XL'} {A' : Ω' → V →ₗ[ℂ] W} {B' : Λ' → W →ₗ[ℂ] V}
    (p' : RationalOperatorContinuationData Ω' A') (q' : RationalOperatorContinuationData Λ' B')
    (hΩmap : ∀ z ∈ Ω', rationalUnramifiedCharacterRestrict iso.hom z ∈ Ω)
    (hA : ∀ z : Ω', A' z =
      A ⟨rationalUnramifiedCharacterRestrict iso.hom z.val, hΩmap z.val z.property⟩)
    (hΛmap : ∀ z ∈ Λ', rationalUnramifiedCharacterRestrict iso.hom z ∈ Λ)
    (hB : ∀ z : Λ', B' z =
      B ⟨rationalUnramifiedCharacterRestrict iso.hom z.val, hΛmap z.val z.property⟩)
    {D E : Set XL'} (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω')
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ')
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L' hp' hL' p' q' (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ =
      rationalUnramifiedFunctionFieldEquiv hp hL hp' hL' iso
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  let pT := continuationRestrict iso.hom p hΩmap hA
  let qT := continuationRestrict iso.hom q hΛmap hB
  rw [continuedCompositeRationalScalar_continuation_independent L' hp' hL' p' q' pT qT
    hD hneD hDΩ hE hneE hEΛ v ℓ]
  obtain ⟨a, b, -, hbreg, hfC, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ℓ
  rw [hfC, map_div₀, rationalUnramifiedFunctionFieldEquiv_algebraMap,
    rationalUnramifiedFunctionFieldEquiv_algebraMap]
  let P : ScalarPresentation (pT.regularRegion ∩ qT.regularRegion)
      (fun z => endomorphismScalarCoefficient v ℓ (pT.continuedComposite qT z)) :=
    { numerator := rationalUnramifiedRegularFunctionsEquiv iso a
      denominator := rationalUnramifiedRegularFunctionsEquiv iso b
      denominator_nonzero := fun z =>
        hbreg ⟨rationalUnramifiedCharacterRestrict iso.hom z.val, z.property.1, z.property.2⟩
      clears := fun z => by
        have hz := hval ⟨rationalUnramifiedCharacterRestrict iso.hom z.val,
          z.property.1, z.property.2⟩
        change b.val (rationalUnramifiedCharacterRestrict iso.hom z.val) *
            p.continuedCompositeScalar q v ℓ
              ⟨rationalUnramifiedCharacterRestrict iso.hom z.val, z.property.1, z.property.2⟩ =
          a.val (rationalUnramifiedCharacterRestrict iso.hom z.val)
        rw [hz, mul_div_cancel₀ _
          (hbreg ⟨rationalUnramifiedCharacterRestrict iso.hom z.val, z.property.1,
            z.property.2⟩)] }
  have hR := pT.regularRegion_isOpen.inter qT.regularRegion_isOpen
  have hneR := continuedCompositeRegion_nonempty L' hp' hL' pT qT
    (hneD.mono hDΩ) (hneE.mono hEΛ)
  rw [← P.toFunctionField_eq_div L' hp' hL' hneR]
  exact rationalUnramifiedOperatorScalar_eq_presentation L' hp' hL' _ _ v ℓ P hneR hR hneR
    subset_rfl

end ContinuationRestriction

/-! ### Transport of the canonical scalar along a parameter isomorphism -/

section CanonicalTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {L L' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine L.X.left] [IsAffine L'.X.left]

attribute [local instance] pairScalarPointTopology

set_option hygiene false in
local notation "XL" => unramifiedCharacters (fun φ => (rationalNormCharacters L φ).toMul)
set_option hygiene false in
local notation "XL'" => unramifiedCharacters (fun φ => (rationalNormCharacters L' φ).toMul)

section Characters

variable {G : Type uG} [Group G] [TopologicalSpace G] {M : Subgroup G}

/-- **Characters of the Levi along a parameter isomorphism.** If the identifications
`e : L(F) ≃ M` and `e' : L'(F) ≃ M` are compatible with `iso : L ≅ L'`, the character of `M`
attached to `z'` through `e'` is the one attached to `z' ∘ iso` through `e`. -/
theorem unramifiedCharactersHomeomorph_restrict (iso : L ≅ L')
    (e : GroupScheme.rationalPoints L ≃ₜ* M) (e' : GroupScheme.rationalPoints L' ≃ₜ* M)
    (he : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = e y) (z : XL') :
    (unramifiedCharactersHomeomorph e' (fun φ => (rationalNormCharacters L' φ).toMul) z).val =
      (unramifiedCharactersHomeomorph e (fun φ => (rationalNormCharacters L φ).toMul)
        (rationalUnramifiedCharacterRestrict iso.hom z)).val := by
  apply ContinuousMonoidHom.ext
  intro m
  rw [unramifiedCharactersHomeomorph_apply, unramifiedCharactersHomeomorph_apply,
    rationalUnramifiedCharacterRestrict_apply]
  have hm : GroupScheme.rationalPoints.map iso.hom (e.symm m) = e'.symm m := by
    rw [← e'.symm_apply_apply (GroupScheme.rationalPoints.map iso.hom (e.symm m)), he,
      e.apply_symm_apply]
  rw [hm]

end Characters

section Families

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
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ φ, Continuous (rationalNormCharacters L φ).toMul)
  (e' : GroupScheme.rationalPoints L' ≃ₜ* M)
  (hν' : ∀ φ, Continuous (rationalNormCharacters L' φ).toMul)
  (A : SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))

set_option hygiene false in
local notation "νL" => (fun φ => (rationalNormCharacters L φ).toMul)
set_option hygiene false in
local notation "νL'" => (fun φ => (rationalNormCharacters L' φ).toMul)
set_option hygiene false in
local notation "R" => rationalUnramifiedCharacterRestrict iso.hom

/-- **Full domains along a parameter isomorphism.** The full domain of the standard integral
for `e'` is the preimage of the full domain for `e` under `z' ↦ z' ∘ iso`. -/
theorem standardIntertwiningFullDomainRegion_restrict_iff (iso : L ≅ L')
    (he : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = e y) (z : XL') :
    z ∈ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A ↔
      R z ∈ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A := by
  simp only [standardIntertwiningFullDomainRegion, Set.mem_ofPred_eq]
  rw [unramifiedTwist_congr A _ _ (unramifiedCharactersHomeomorph_restrict iso e e' he z)]

variable [T2Space G]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)

/-- **Compact standard integrals along a parameter isomorphism.** At `z'` in the full domain
for `e'`, the compact picture of the standard integral for `e'` is the one for `e` at
`z' ∘ iso`. -/
theorem standardInductionIntertwinerFamily_compact_restrict (iso : L ≅ L')
    (he : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = e y)
    (z : standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun φ => (rationalNormCharacters L' φ).toMul.comp e'.symm.toMulEquiv.toMonoidHom)
        (fun φ => (hν' φ).comp e'.symm.continuous) hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e' νL' z.val) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e' νL' q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A z) =
      compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun φ => (rationalNormCharacters L φ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun φ => (hν φ).comp e.symm.continuous) hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e νL (R z.val)) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
          ⟨R z.val, (standardIntertwiningFullDomainRegion_restrict_iff h₀ hU₀ e e' A q₁₀ iso he
            z.val).mp z.property⟩) :=
  compactFullSourceIntertwiner_congr h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
    q₁₀ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A _ _ _ _
    (unramifiedCharactersHomeomorph_restrict iso e e' he z.val) z.property _

end Families

section Canonical

variable (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  (hp' : Continuous (rationalValuationImageProjection L'))
  (hL' : GroupScheme.IsConnectedReductive L')
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
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
  (hν : ∀ φ, Continuous (rationalNormCharacters L φ).toMul)
  (e' : GroupScheme.rationalPoints L' ≃ₜ* M)
  (hν' : ∀ φ, Continuous (rationalNormCharacters L' φ).toMul)
  (A : SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace U₀] [BorelSpace U₀]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₀)] [BorelSpace (U₁.subgroupOf U₀)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₀)]
  [BorelSpace (QuotientSpace (U := U₁) U₀)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (q₀₁ : Measure (QuotientSpace (U := U₁) U₀))
  (μU₀ : Measure U₀) (μU₁ : Measure U₁)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₀₁ : Measure (U₁.subgroupOf U₀))
  [IsHaarMeasure μU₀] [μU₀.Regular] [IsMulRightInvariant μU₀]
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₀₁] [μI₀₁.Regular] [IsMulRightInvariant μI₀₁]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hq₀₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₀) μU₀ μI₀₁ q₀₁)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)
  [TopologicalSpace.SeparableSpace G]

set_option hygiene false in
local notation "νL" => (fun φ => (rationalNormCharacters L φ).toMul)
set_option hygiene false in
local notation "νL'" => (fun φ => (rationalNormCharacters L' φ).toMul)
set_option hygiene false in
local notation "νM" =>
  (fun φ => (rationalNormCharacters L φ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
set_option hygiene false in
local notation "νM'" =>
  (fun φ => (rationalNormCharacters L' φ).toMul.comp e'.symm.toMulEquiv.toMonoidHom)
set_option hygiene false in
local notation "hνM" => (fun φ => (hν φ).comp e.symm.continuous)
set_option hygiene false in
local notation "hνM'" => (fun φ => (hν' φ).comp e'.symm.continuous)
set_option hygiene false in
local notation "R" => rationalUnramifiedCharacterRestrict iso.hom

/-- **Transport of the canonical scalar, same order.** Let `iso : L ≅ L'` be compatible with
the identifications `e : L(F) ≃ M` and `e' : L'(F) ≃ M`. For the same subgroups, measures and
representation, the canonical scalar of the composite `J₀₁ J₁₀` computed through `e'` is the
one computed through `e`, transported by `iso`. The continuation data, convergence domains and
irreducibility loci on the two sides are independent; only those for `e'` are required to be
open. -/
theorem standardInductionCompositeCanonicalRationalScalar_transport (iso : L ≅ L')
    (he : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = e y)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A)
      (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM hνM hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e νL χ.val) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
    (q : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A)
      (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K νM hνM hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (unramifiedCharactersHomeomorph e νL χ.val) A
        (standardInductionIntertwinerFamily h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀
          μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
    {D₁₀ D₀₁ : Set XL} (hne₁₀ : D₁₀.Nonempty)
    (hD₁₀Ω : D₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A)
    (hne₀₁ : D₀₁.Nonempty)
    (hD₀₁Ω : D₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A)
    {D : Set XL} (hne : D.Nonempty)
    (hi : ∀ χ ∈ D, (UnramifiedLeviInduction h₀ hU₀ νM
      (unramifiedCharactersHomeomorph e νL χ) A).IsIrreducible)
    (p' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A)
      (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM' hνM' hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e' νL' χ.val) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e' νL' q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
    (q' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e' νL' q₀₁ A)
      (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K νM' hνM' hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (unramifiedCharactersHomeomorph e' νL' χ.val) A
        (standardInductionIntertwinerFamily h₁ hU₁ U₀ e' νL' q₀₁ h₀ hU₀
          μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
    {D₁₀' D₀₁' : Set XL'} (hD₁₀' : IsOpen D₁₀') (hne₁₀' : D₁₀'.Nonempty)
    (hD₁₀Ω' : D₁₀' ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A)
    (hD₀₁' : IsOpen D₀₁') (hne₀₁' : D₀₁'.Nonempty)
    (hD₀₁Ω' : D₀₁' ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e' νL' q₀₁ A)
    {D' : Set XL'} (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ χ ∈ D', (UnramifiedLeviInduction h₀ hU₀ νM'
      (unramifiedCharactersHomeomorph e' νL' χ) A).IsIrreducible) :
    standardInductionCompositeCanonicalRationalScalar L' hp' hL'
        h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e' hν' A
        q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
        p' q' hne₁₀' hD₁₀Ω' hne₀₁' hD₀₁Ω' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv hp hL hp' hL' iso
        (standardInductionCompositeCanonicalRationalScalar L hp hL
          h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
          q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
          p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi) := by
  let s := compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM hνM hr₀ A
    (unramifiedCharactersHomeomorph e νL (Classical.choose hne)) (hi _ (Classical.choose_spec hne))
  rw [standardInductionCompositeCanonicalRationalScalar_eq_extraction L' hp' hL'
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e' hν' A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p' q' hD₁₀' hne₁₀' hD₁₀Ω' hD₀₁' hne₀₁' hD₀₁Ω' hD' hne' hi' s.val.1 s.val.2 s.property]
  exact continuedCompositeRationalScalar_transport hp hL hp' hL' iso p q
    (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) p' q'
    (fun z hz => (standardIntertwiningFullDomainRegion_restrict_iff h₀ hU₀ e e' A q₁₀ iso he
      z).mp hz)
    (fun z => standardInductionIntertwinerFamily_compact_restrict h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν e' hν' A q₁₀ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ iso he z)
    (fun z hz => (standardIntertwiningFullDomainRegion_restrict_iff h₁ hU₁ e e' A q₀₁ iso he
      z).mp hz)
    (fun z => standardInductionIntertwinerFamily_compact_restrict h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK
      hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν e' hν' A q₀₁ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ iso he z)
    hD₁₀' hne₁₀' hD₁₀Ω' hD₀₁' hne₀₁' hD₀₁Ω' s.val.1 s.val.2

/-- **Transport of the canonical scalar, exchanged order.** Under the same compatibility of
`iso`, `e` and `e'`, the canonical scalar of the composite `J₁₀ J₀₁` (the order starting from
the decomposition `h₁`) computed through `e'` is the canonical scalar of `J₀₁ J₁₀` computed
through `e`, transported by `iso`. The irreducibility locus of `h₁` needed on the side of `e`
is the transport of the given locus for `e'`; the two orders are compared by
`standardInductionCompositeCanonicalRationalScalar_eq_reverse`. -/
theorem standardInductionCompositeCanonicalRationalScalar_transport_reverse (iso : L ≅ L')
    (he : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = e y)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A)
      (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM hνM hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e νL χ.val) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
    (q : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A)
      (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K νM hνM hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (unramifiedCharactersHomeomorph e νL χ.val) A
        (standardInductionIntertwinerFamily h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀
          μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
    {D₁₀ D₀₁ : Set XL} (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
    (hD₁₀Ω : D₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A)
    (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
    (hD₀₁Ω : D₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A)
    {D : Set XL} (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ χ ∈ D, (UnramifiedLeviInduction h₀ hU₀ νM
      (unramifiedCharactersHomeomorph e νL χ) A).IsIrreducible)
    (p' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e' νL' q₀₁ A)
      (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K νM' hνM' hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (unramifiedCharactersHomeomorph e' νL' χ.val) A
        (standardInductionIntertwinerFamily h₁ hU₁ U₀ e' νL' q₀₁ h₀ hU₀
          μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
    (q' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A)
      (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM' hνM' hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ (unramifiedCharactersHomeomorph e' νL' χ.val) A
        (standardInductionIntertwinerFamily h₀ hU₀ U₁ e' νL' q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
    {D₀₁' D₁₀' : Set XL'} (hD₀₁' : IsOpen D₀₁') (hne₀₁' : D₀₁'.Nonempty)
    (hD₀₁Ω' : D₀₁' ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e' νL' q₀₁ A)
    (hD₁₀' : IsOpen D₁₀') (hne₁₀' : D₁₀'.Nonempty)
    (hD₁₀Ω' : D₁₀' ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e' νL' q₁₀ A)
    {D' : Set XL'} (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ χ ∈ D', (UnramifiedLeviInduction h₁ hU₁ νM'
      (unramifiedCharactersHomeomorph e' νL' χ) A).IsIrreducible) :
    standardInductionCompositeCanonicalRationalScalar L' hp' hL'
        h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e' hν' A
        q₀₁ q₁₀ μU₁ μU₀ μI₀₁ μI₁₀ hq₀₁ hq₁₀ hM hsq₀₁ hsq₁₀
        p' q' hne₀₁' hD₀₁Ω' hne₁₀' hD₁₀Ω' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv hp hL hp' hL' iso
        (standardInductionCompositeCanonicalRationalScalar L hp hL
          h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
          q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
          p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi) := by
  let D₁ : Set XL := rationalUnramifiedCharacterTransport iso ⁻¹' D'
  have hD₁ : IsOpen D₁ := hD'.preimage (rationalUnramifiedCharacterTransport iso).continuous
  have hne₁ : D₁.Nonempty := by
    obtain ⟨z', hz'⟩ := hne'
    refine ⟨R z', ?_⟩
    change rationalUnramifiedCharacterRestrict iso.inv (R z') ∈ D'
    rwa [← rationalUnramifiedCharacterRestrict_comp, Iso.inv_hom_id,
      rationalUnramifiedCharacterRestrict_id]
  have hi₁ : ∀ χ ∈ D₁, (UnramifiedLeviInduction h₁ hU₁ νM
      (unramifiedCharactersHomeomorph e νL χ) A).IsIrreducible := by
    intro χ hχ
    have h := hi' (rationalUnramifiedCharacterTransport iso χ) hχ
    rwa [unramifiedLeviInduction_congr h₁ hU₁ A _ _
      (unramifiedCharactersHomeomorph_restrict iso e e' he _),
      rationalUnramifiedCharacterRestrict_transport] at h
  rw [standardInductionCompositeCanonicalRationalScalar_eq_reverse L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi hD₁ hne₁ hi₁]
  exact standardInductionCompositeCanonicalRationalScalar_transport hp hL hp' hL'
    h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν e' hν' A
    q₀₁ q₁₀ μU₁ μU₀ μI₀₁ μI₁₀ hq₀₁ hq₁₀ hM hsq₀₁ hsq₁₀ iso he
    q p hne₀₁ hD₀₁Ω hne₁₀ hD₁₀Ω hne₁ hi₁
    p' q' hD₀₁' hne₀₁' hD₀₁Ω' hD₁₀' hne₁₀' hD₁₀Ω' hD' hne' hi'

end Canonical

end CanonicalTransport

/-! ### The dynamic scalar under a change of cocharacter -/

section Dynamic

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open StandardIntertwining.OrderedSubgroupFactorization Haar QuotientIntegration

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  pairScalarPointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Borel structure on a subgroup of `G(F)`, as in the construction of the dynamic scalar. -/
local instance pairScalarSubgroupMeasurableSpace (H : Subgroup (RationalPoint F G.X)) :
    MeasurableSpace H := borel _
local instance pairScalarSubgroupBorelSpace (H : Subgroup (RationalPoint F G.X)) :
    BorelSpace H := ⟨rfl⟩
/-- Borel structure on an intersection `H ∩ H'` inside `H'`. -/
local instance pairScalarIntersectionMeasurableSpace (H H' : Subgroup (RationalPoint F G.X)) :
    MeasurableSpace (H.subgroupOf H') := borel _
local instance pairScalarIntersectionBorelSpace (H H' : Subgroup (RationalPoint F G.X)) :
    BorelSpace (H.subgroupOf H') := ⟨rfl⟩
/-- Borel structure on the quotient `(H ∩ H') \ H'`. -/
local instance pairScalarQuotientMeasurableSpace (H H' : Subgroup (RationalPoint F G.X)) :
    MeasurableSpace (QuotientSpace (U := H) H') := borel _
local instance pairScalarQuotientBorelSpace (H H' : Subgroup (RationalPoint F G.X)) :
    BorelSpace (QuotientSpace (U := H) H') := ⟨rfl⟩

/-- Every point of an actual dynamic radical lies in a compact open subgroup. -/
theorem pairScalarRadicalCover (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (x : radical χ) :
    ∃ C : OpenSubgroup (radical χ), IsCompact (C : Set (radical χ)) ∧ x ∈ C := by
  obtain ⟨C, hC, hx⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup χ {x} isCompact_singleton
  exact ⟨C, hC, hx (Set.mem_singleton x)⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The same representation pulled back along the identity of its group. -/
theorem pairScalar_pullback_refl {M : Subgroup (RationalPoint F G.X)}
    (A : SmoothRep.{0, u, uV} ℂ M) :
    SmoothRep.pullback (ContinuousMulEquiv.refl M).symm A = A :=
  rfl

set_option hygiene false in
local notation "νL'" => (fun φ => (rationalNormCharacters L' φ).toMul)
set_option hygiene false in
local notation "νM'" =>
  (fun φ => (rationalNormCharacters L' φ).toMul.comp e'.symm.toMulEquiv.toMonoidHom)
set_option hygiene false in
local notation "hνM'" => (fun φ => (hν' φ).comp e'.symm.continuous)
set_option hygiene false in
local notation "qF" => sourceQuotientMeasure K hK U₀' U₁' hU₀' hU₁' hc₀' hc₁'
set_option hygiene false in
local notation "qR" => sourceQuotientMeasure K hK U₁' U₀' hU₁' hU₀' hc₁' hc₀'
set_option hygiene false in
local notation "μ₀" => subgroupCompactOpenHaar K hK U₀' hU₀'
set_option hygiene false in
local notation "μ₁" => subgroupCompactOpenHaar K hK U₁' hU₁'
set_option hygiene false in
local notation "ιF" => sourceIntersectionHaar K hK U₀' U₁' hU₀' hU₁'
set_option hygiene false in
local notation "ιR" => sourceIntersectionHaar K hK U₁' U₀' hU₁' hU₀'

/-- Canonical data on a second set of subgroups, with the same source normalization `K`.
After substituting the subgroup equalities, the isomorphism of the literal Levis is
the identity; the remaining comparison is just transport along `iso`, with or without
exchanging the two operators. -/
private theorem pairScalar_transport
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))} (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    {L' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine L'.X.left]
    (hp' : Continuous (rationalValuationImageProjection L'))
    (hL' : GroupScheme.IsConnectedReductive L')
    (iso : parameterScheme χ ≅ L')
    {P₀' P₁' M' U₀' U₁' : Subgroup (RationalPoint F G.X)}
    (h₀' : IsSemidirectDecomposition P₀' M' U₀')
    (hU₀' : IsClosed (U₀' : Set (RationalPoint F G.X)))
    (hδ₀' : IsUnimodularModulus U₀' hU₀')
    (h₁' : IsSemidirectDecomposition P₁' M' U₁')
    (hU₁' : IsClosed (U₁' : Set (RationalPoint F G.X)))
    (hδ₁' : IsUnimodularModulus U₁' hU₁')
    (hP₀' : IsClosed (P₀' : Set (RationalPoint F G.X)))
    (hP₁' : IsClosed (P₁' : Set (RationalPoint F G.X)))
    (hP₀K' : ∀ g : RationalPoint F G.X,
      ∃ p : P₀', ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hP₁K' : ∀ g : RationalPoint F G.X,
      ∃ p : P₁', ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hr₀' : Continuous h₀'.projection) (hr₁' : Continuous h₁'.projection)
    (e' : GroupScheme.rationalPoints L' ≃ₜ* M')
    (hν' : ∀ φ, Continuous (rationalNormCharacters L' φ).toMul)
    (f : levi χ ≃ₜ* M') (hf : ∀ m, (f m : RationalPoint F G.X) = m)
    (he' : ∀ y, e' (GroupScheme.rationalPoints.map iso.hom y) = f (parameterHomeomorph χ y))
    (A' : SmoothRep.{0, u, uV} ℂ M') (hA' : A' = SmoothRep.pullback f.symm A)
    (hc₀' : ∀ x : U₀', ∃ C : OpenSubgroup U₀', IsCompact (C : Set U₀') ∧ x ∈ C)
    (hc₁' : ∀ x : U₁', ∃ C : OpenSubgroup U₁', IsCompact (C : Set U₁') ∧ x ∈ C)
    [IsMulRightInvariant μ₀] [IsMulRightInvariant μ₁]
    [IsMulRightInvariant ιF] [IsMulRightInvariant ιR]
    (hq₁₀' : IsCompatible (U₀'.subgroupOf U₁') μ₁ ιF qF)
    (hq₀₁' : IsCompatible (U₁'.subgroupOf U₀') μ₀ ιR qR)
    (hM' : IsClosed (M' : Set (RationalPoint F G.X)))
    (hsq₁₀' : SquaredModulusCompatibility h₀' hU₀' h₁' hU₁')
    (hsq₀₁' : SquaredModulusCompatibility h₁' hU₁' h₀' hU₀')
    (p' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₀' hU₀' U₁' e' νL' qF A')
      (fun z => compactIntertwiningOperator h₀' hU₀' hδ₀' K hP₀' hK hP₀K' νM' hνM' hr₀'
        h₁' hU₁' hδ₁' hP₁' hP₁K' hr₁' (unramifiedCharactersHomeomorph e' νL' z.val) A'
        (standardInductionIntertwinerFamily h₀' hU₀' U₁' e' νL' qF h₁' hU₁'
          μ₁ ιF hq₁₀' hM' hsq₁₀' A' z)))
    (q' : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h₁' hU₁' U₀' e' νL' qR A')
      (fun z => compactIntertwiningOperator h₁' hU₁' hδ₁' K hP₁' hK hP₁K' νM' hνM' hr₁'
        h₀' hU₀' hδ₀' hP₀' hP₀K' hr₀' (unramifiedCharactersHomeomorph e' νL' z.val) A'
        (standardInductionIntertwinerFamily h₁' hU₁' U₀' e' νL' qR h₀' hU₀'
          μ₀ ιR hq₀₁' hM' hsq₀₁' A' z)))
    {DForward' DReverse' : Set (unramifiedCharacters νL')}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ standardIntertwiningFullDomainRegion h₀' hU₀' U₁' e' νL' qF A')
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ standardIntertwiningFullDomainRegion h₁' hU₁' U₀' e' νL' qR A')
    {D' : Set (unramifiedCharacters νL')} (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D', (UnramifiedLeviInduction h₀' hU₀' νM'
      (unramifiedCharactersHomeomorph e' νL' z) A').IsIrreducible)
    (hMeq : M' = levi χ)
    (hpair : (P₀' = parabolic χ ∧ U₀' = radical χ ∧
        P₁' = oppositeParabolic χ ∧ U₁' = oppositeRadical χ) ∨
      (P₀' = oppositeParabolic χ ∧ U₀' = oppositeRadical χ ∧
        P₁' = parabolic χ ∧ U₁' = radical χ)) :
    standardInductionCompositeCanonicalRationalScalar L' hp' hL'
        h₀' hU₀' hδ₀' h₁' hU₁' hδ₁' K hK hP₀' hP₁' hP₀K' hP₁K' hr₀' hr₁' e' hν' A'
        qF qR μ₀ μ₁ ιF ιR hq₁₀' hq₀₁' hM' hsq₁₀' hsq₀₁'
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv (parameterProjection_continuous χ)
        (parameterScheme_isConnectedReductive χ hG) hp' hL' iso
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  subst M'
  obtain rfl : f = ContinuousMulEquiv.refl (levi χ) :=
    ContinuousMulEquiv.ext fun m => Subtype.ext (hf m)
  have hA : A' = A := hA'.trans (pairScalar_pullback_refl A)
  subst A'
  rcases hpair with ⟨hP₀eq, hU₀eq, hP₁eq, hU₁eq⟩ | ⟨hP₀eq, hU₀eq, hP₁eq, hU₁eq⟩ <;>
    subst hP₀eq hU₀eq hP₁eq hU₁eq
  · exact standardInductionCompositeCanonicalRationalScalar_transport
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) hp' hL'
      (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
      (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG)
      K hK (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
      (projection_continuous χ) (oppositeProjection_continuous χ)
      (parameterHomeomorph χ) (normCharacters_continuous χ) e' hν' A
      (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
      (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
      (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
      (forwardQuotientMeasure_isCompatible χ K hK)
      (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
      (conditionalSquaredModulus χ hRefl hCST hG)
      (conditionalReverseSquaredModulus χ hRefl hCST hG)
      iso he' p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi
      p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
  · exact standardInductionCompositeCanonicalRationalScalar_transport_reverse
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) hp' hL'
      (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
      (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG)
      K hK (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
      (projection_continuous χ) (oppositeProjection_continuous χ)
      (parameterHomeomorph χ) (normCharacters_continuous χ) e' hν' A
      (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
      (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
      (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
      (forwardQuotientMeasure_isCompatible χ K hK)
      (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
      (conditionalSquaredModulus χ hRefl hCST hG)
      (conditionalReverseSquaredModulus χ hRefl hCST hG)
      iso he' p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
      p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'

/-- The dynamic canonical scalar depends only on the opposite pair, after
identification of the parameters through the common centralizer scheme. -/
theorem conditionalDynamicOppositePairScalar :
    ConditionalDynamicOppositePairScalarStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ ψ hRefl hCST hG hM hpair K hK hPK hOppK hPK' hOppK' A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi p' q' DForward' DReverse' hDForward' hneForward' hDForwardΩ'
    hDReverse' hneReverse' hDReverseΩ' D' hD' hne' hi'
  have hMeq : levi ψ = levi χ := Subgroup.ext (changeLevi_mem_iff χ ψ hM)
  exact pairScalar_transport χ hRefl hCST hG K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    (parameterProjection_continuous ψ) (parameterScheme_isConnectedReductive ψ hG)
    (parameterChangeIso χ ψ hM)
    (decomposition ψ) (radical_isClosed ψ) (radical_unimodular ψ hG)
    (oppositeDecomposition ψ) (oppositeRadical_isClosed ψ) (oppositeRadical_unimodular ψ hG)
    (parabolic_isClosed ψ) (oppositeParabolic_isClosed ψ) hPK' hOppK'
    (projection_continuous ψ) (oppositeProjection_continuous ψ)
    (parameterHomeomorph ψ) (normCharacters_continuous ψ)
    (leviChange χ ψ hM) (leviChange_apply_coe χ ψ hM)
    (parameterHomeomorph_parameterChangeIso χ ψ hM) (changeRepresentation χ ψ hM A) rfl
    (pairScalarRadicalCover ψ) (pairScalarRadicalCover (Dynamic.inverseCocharacter ψ))
    (forwardQuotientMeasure_isCompatible ψ K hK) (reverseQuotientMeasure_isCompatible ψ K hK)
    (levi_isClosed ψ) (conditionalSquaredModulus ψ hRefl hCST hG)
    (conditionalReverseSquaredModulus ψ hRefl hCST hG)
    p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
    hMeq hpair

end Dynamic

end Langlands.Plancherel
