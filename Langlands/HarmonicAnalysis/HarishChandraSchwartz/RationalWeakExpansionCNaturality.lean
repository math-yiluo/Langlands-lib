import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily

/-! # Naturality of the c-family in the inducing representation -/

noncomputable section

universe u uV uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

/-- The equivalence of smooth duals `B̌ ≃ B̌'` induced by an equivalence `b : B ≃ B'` (inverse
transpose). -/
abbrev contragredientEquivOf {M : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    {B B' : SmoothRep.{0, _, uV} ℂ M} (b : B.representation.Equiv B'.representation) :
    B.contragredient.representation.Equiv B'.contragredient.representation :=
  smoothContragredientEquiv b.symm


section CoefficientTensor

variable {Gg : Type uG} [Group Gg] [TopologicalSpace Gg] [LocallyCompactSpace Gg]
  [NonarchimedeanGroup Gg] [SecondCountableTopology Gg] {P M U : Subgroup Gg}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set Gg))
  [CompactSpace (Induction.LeftQuotient P)]

/-- The product comparison `I(A) ⊗ I(Ǎ) ≃ I^{G×G}(A ⊠ Ǎ)`, as a linear map with codomain the
coefficient object `productInducedCoefficientObject`. -/
def productCoefficientTensorMap (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj A ⊗[ℂ]
        (normalizedInductionFunctor h hU).obj A.contragredient) →ₗ[ℂ]
      productInducedCoefficientObject h hU A :=
  (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).toLinearMap

theorem coefficientTensorMap_surjective (A : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Surjective (productCoefficientTensorMap h hU A) :=
  (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).toLinearEquiv.surjective

/-- Coefficient transport on a pure tensor is the tensor of the pointwise transports. -/
theorem transport_coefficientTensorMap {A B : SmoothRep.{0, uG, uV} ℂ M}
    (e : A.representation.Equiv B.representation)
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) :
    productInducedCoefficientTransport h hU e (productCoefficientTensorMap h hU A (f ⊗ₜ[ℂ] fdual)) =
      productCoefficientTensorMap h hU B (normalizedInductionEquivOfEquiv h hU e f ⊗ₜ[ℂ]
        normalizedInductionEquivOfEquiv h hU (contragredientEquivOf e) fdual) :=
  productInducedCoefficientTransport_tensor h hU e f fdual

end CoefficientTensor

section CompactSquare

variable {Gg : Type uG} [Group Gg] [TopologicalSpace Gg] [NonarchimedeanGroup Gg]
  [LocallyCompactSpace Gg] {M : Subgroup Gg} {ιν : Type*} (νg : ιν → (M →* ℝ≥0ˣ))
  {P U : Subgroup Gg} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup Gg)
  (hP : IsClosed (P : Set Gg)) (hK : IsCompact (K : Set Gg))
  (hν : ∀ i, Continuous (νg i)) (hr : Continuous h.projection)
  (hU : IsClosed (U : Set Gg)) (hPK : ∀ g : Gg, ∃ p : P, ∃ k : K, g = (p : Gg) * (k : Gg))

/-- **Self-twist square on the fixed compact picture.** If `e₁ : X ≃ A₀ ⊗ χ₁`,
`e₂ : X' ≃ A₀ ⊗ χ₂`, `c : X ≃ X'` and a self-twist `a : A₀ ≃ A₀ ⊗ τ` satisfy `e₂ ∘ c = a ∘ e₁`
on vectors, then restricting `e₂ c Y` to the compact picture is the self-twist operator of `a`
applied to the restriction of `e₁ Y`. -/
theorem productInducedCompactEquiv_transport_selfTwist {X X' A₀ : SmoothRep.{0, uG, uV} ℂ M}
    (χ₁ χ₂ τ : unramifiedCharacters νg)
    (e₁ : X.representation.Equiv
      (A₀.twist χ₁.val.toMonoidHom (unramifiedCharacter_isOpen_ker νg χ₁)).representation)
    (e₂ : X'.representation.Equiv
      (A₀.twist χ₂.val.toMonoidHom (unramifiedCharacter_isOpen_ker νg χ₂)).representation)
    (c : X.representation.Equiv X'.representation)
    (a : A₀.representation.Equiv
      (A₀.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νg τ)).representation)
    (hcomp : ∀ v, e₂ (c v) = a (e₁ v)) (Y : productInducedCoefficientObject h hU X) :
    productInducedCompactEquiv νg h K hP hK hν hr hU hPK χ₂ A₀
        (productInducedCoefficientTransport h hU e₂ (productInducedCoefficientTransport h hU c Y)) =
      productCompactSelfTwistEquiv νg A₀ h K hP hK hν hr τ a
        (productInducedCompactEquiv νg h K hP hK hν hr hU hPK χ₁ A₀
          (productInducedCoefficientTransport h hU e₁ Y)) := by
  have key : ∀ t : CoefficientTensor X,
      productCompactTwistTensorEquiv νg χ₂ A₀ (coefficientTensorCongr e₂ (coefficientTensorCongr c t)) =
        selfTwistTensorEquiv νg A₀ τ a
          (productCompactTwistTensorEquiv νg χ₁ A₀ (coefficientTensorCongr e₁ t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul v ℓ =>
      show e₂ (c v) ⊗ₜ[ℂ] _ = a (e₁ v) ⊗ₜ[ℂ] _
      congr 1
      · exact hcomp v
      · apply Subtype.ext
        apply LinearMap.ext
        intro w
        change ℓ.val (c.symm (e₂.symm w)) = ℓ.val (e₁.symm (a.symm w))
        have h1 : e₂ (c (e₁.symm (a.symm w))) = w := by
          rw [hcomp, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
        calc ℓ.val (c.symm (e₂.symm w))
            = ℓ.val (c.symm (e₂.symm (e₂ (c (e₁.symm (a.symm w)))))) := by rw [h1]
          _ = ℓ.val (e₁.symm (a.symm w)) := by
            rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]
    | add t s ht hs => simp only [map_add, ht, hs]
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact key (Y.1.1 (k : Gg × Gg))

end CompactSquare

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine
  cFamilyLeviFiniteType

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "jI'" => Standard.leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

section Factor

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  cFamilyRadicalMeasurableSpace cFamilyRadicalBorelSpace cFamilyIntersectionMeasurableSpace
  cFamilyIntersectionBorelSpace cFamilyQuotientMeasurableSpace cFamilyQuotientBorelSpace

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "θα" => CommGroupScheme.groupHom α ≫ i
set_option hygiene false in
local notation "hθψ" => (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).symm
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

variable {B B' : SmoothRep.{0, u, uV} ℂ 𝐌} (b : B.representation.Equiv B'.representation)

/-- The equivalence `sB ≃ sB'` of the pullbacks along `e⁻¹`, with the linear map of `b`. -/
abbrev lowerPullbackEquiv :
    (SmoothRep.pullback (eₛ).symm B).representation.Equiv
      (SmoothRep.pullback (eₛ).symm B').representation :=
  SmoothRep.pullbackEquiv _ b

/-- The equivalence `ⁿB ≃ ⁿB'` of conjugates, with the linear map of `b`. -/
abbrev conjugateRepEquiv :
    (conjugateRep hG hi hν I I' hζ n hn α hα B).representation.Equiv
      (conjugateRep hG hi hν I I' hζ n hn α hα B').representation :=
  SmoothRep.pullbackEquiv _ b

/-- `λ(s)` commutes with pointwise transport. -/
theorem factorTranslation_natural
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B) :
    factorTranslation hG hi hν I I' hζ n hn α hα B'
        (normalizedInductionEquivOfEquiv _ _ b f) =
      normalizedInductionEquivOfEquiv _ _ (conjugateRepEquiv hG hi hν I I' hζ n hn α hα b)
        (factorTranslation hG hi hν I I' hζ n hn α hα B f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  rfl


variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

variable {A A' : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα)}
  (c : A.representation.Equiv A'.representation)

/-- The standard integral `J_{P_α|s·P}` commutes with pointwise transport. -/
theorem factorIntertwiner_natural
    (hA : FactorConverges hG hi hν I I' hζ n hn α hα K hK A)
    (hA' : FactorConverges hG hi hν I I' hζ n hn α hα K hK A')
    (g : (DynamicNormalization.leviTwistedInductionFunctor (commonDecomposition ψα θs hθψ)
        (radical_isClosed θs)).obj A) :
    factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST A' hA'
        (StandardIntertwining.inducedMap _ _ c.toIntertwiningMap g) =
      StandardIntertwining.inducedMap _ _ c.toIntertwiningMap
        (factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST A hA g) :=
  DFunLike.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (StandardIntertwining.fullSourceIntertwiner_natural _ _ _ _ _ _ _ _ _ _ hA hA'
      c.toIntertwiningMap)) g

/-- The source Levi-twist comparison commutes with pointwise transport. -/
theorem normalizedInductionLeviEquiv_transport_source
    (f : (normalizedInductionFunctor (commonDecomposition ψα θs hθψ) (radical_isClosed θs)).obj A) :
    normalizedInductionLeviEquiv (commonDecomposition ψα θs hθψ) (radical_isClosed θs)
        (DynamicOppositeCanonicalScalar.radical_unimodular θs hG) A'
        (normalizedInductionEquivOfEquiv _ _ c f) =
      StandardIntertwining.inducedMap _ _ c.toIntertwiningMap
        (normalizedInductionLeviEquiv (commonDecomposition ψα θs hθψ) (radical_isClosed θs)
          (DynamicOppositeCanonicalScalar.radical_unimodular θs hG) A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  rfl

/-- The target Levi-twist comparison commutes with pointwise transport. -/
theorem normalizedInductionLeviEquiv_symm_transport_target
    (f : (DynamicNormalization.leviTwistedInductionFunctor (commonDecomposition ψα ψα rfl)
        (radical_isClosed ψα)).obj A) :
    (normalizedInductionLeviEquiv (commonDecomposition ψα ψα rfl) (radical_isClosed ψα)
        (DynamicOppositeCanonicalScalar.radical_unimodular ψα hG) A').symm
        (StandardIntertwining.inducedMap _ _ c.toIntertwiningMap f) =
      normalizedInductionEquivOfEquiv _ _ c
        ((normalizedInductionLeviEquiv (commonDecomposition ψα ψα rfl) (radical_isClosed ψα)
          (DynamicOppositeCanonicalScalar.radical_unimodular ψα hG) A).symm f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  rfl


set_option hygiene false in
local notation "hRα" => auxiliary_realization hG hi hν I I' hζ n hn α hα
set_option hygiene false in
local notation "hjα" => outer_isRepresentedBy (i := i) (ν := ν) I' α hα

/-- The pointwise transport of the restricted representation along `c`. -/
abbrev restrictedRepEquiv :
    ((SmoothRep.pullbackFunctor (RealizedLeviTransport.centralizerEquiv F θα jI' hjα
        (Standard.isClosedSubgroup_leviHom i ν _) χs ψα hRα)).obj
      ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv
        (Dynamic.realized_centralizer_le θα jI' hjα χs ψα hRα.2.1 X₀))).obj A)).representation.Equiv
    ((SmoothRep.pullbackFunctor (RealizedLeviTransport.centralizerEquiv F θα jI' hjα
        (Standard.isClosedSubgroup_leviHom i ν _) χs ψα hRα)).obj
      ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv
        (Dynamic.realized_centralizer_le θα jI' hjα χs ψα hRα.2.1 X₀))).obj A')).representation :=
  SmoothRep.pullbackEquiv _ (SmoothRep.pullbackEquiv _ c)

set_option maxHeartbeats 1600000 in
/-- Restriction to `M'` commutes with pointwise transport. -/
theorem factorRestriction_natural
    (f : (normalizedInductionFunctor (decomposition ψα) (radical_isClosed ψα)).obj A) :
    factorRestriction hG hi hν I I' hζ n hn α hα A' (normalizedInductionEquivOfEquiv _ _ c f) =
      normalizedInductionEquivOfEquiv _ _ (restrictedRepEquiv hG hi hν I I' hζ n hn α hα c)
        (factorRestriction hG hi hν I I' hζ n hn α hα A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact (c.toLinearMap.map_smul_of_tower _ _).symm


/-- `cFactor` unfolded into its six steps. -/
theorem cFactor_apply (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hB : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B))
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B) :
    cFactor hG hi hν I I' hζ n hn α hα K hK hCST B hB f =
      normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
        (restrictedConjugateEquiv hG hi hν I I' hζ n hn α hα B)
        (factorRestriction hG hi hν I I' hζ n hn α hα (conjugateRep hG hi hν I I' hζ n hn α hα B)
          ((normalizedInductionLeviEquiv (commonDecomposition ψα ψα rfl) (radical_isClosed ψα)
            (DynamicOppositeCanonicalScalar.radical_unimodular ψα hG)
            (conjugateRep hG hi hν I I' hζ n hn α hα B)).symm
            (factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST
              (conjugateRep hG hi hν I I' hζ n hn α hα B) hB
              (normalizedInductionLeviEquiv (commonDecomposition ψα θs hθψ) (radical_isClosed θs)
                (DynamicOppositeCanonicalScalar.radical_unimodular θs hG)
                (conjugateRep hG hi hν I I' hζ n hn α hα B)
                (factorTranslation hG hi hν I I' hζ n hn α hα B f))))) :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **Naturality of one factor `v ↦ v_s`**: for an equivalence `b : B ≃ B'` of representations of
`M_I(F)`, the factor of `B'` after pointwise transport by `b` is the pointwise transport by `b`
of the factor of `B`. -/
theorem cFactor_lowerPullback_natural
    (hB : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B))
    (hB' : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B'))
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B) :
    cFactor hG hi hν I I' hζ n hn α hα K hK hCST B' hB'
        (normalizedInductionEquivOfEquiv _ _ b f) =
      normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
        (lowerPullbackEquiv hG hi hν I I' hζ n hn b)
        (cFactor hG hi hν I I' hζ n hn α hα K hK hCST B hB f) := by
  rw [cFactor_apply, cFactor_apply, factorTranslation_natural,
    normalizedInductionLeviEquiv_transport_source (hG := hG) (hi := hi) (hν := hν) (I := I)
      (I' := I') (hζ := hζ) (hn := hn) (hα := hα),
    factorIntertwiner_natural _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB,
    normalizedInductionLeviEquiv_symm_transport_target (hG := hG) (n := n) (α := α),
    factorRestriction_natural]
  apply Subtype.ext
  apply Subtype.ext
  funext l
  rfl


include b in
/-- Convergence of `J_{P_α|s·P}` is invariant under equivalence of the inducing representation. -/
theorem factorConverges_of_equiv
    (hB : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B)) :
    FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B') :=
  StandardIntertwining.domain_eq_top_of_equiv _ _ _ _
    (conjugateRepEquiv hG hi hν I I' hζ n hn α hα b) hB

end Factor

section CMap

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "hα₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "hα₋" => outerCentralizer_neg hG hi hν I' hζ'

variable {B B' : SmoothRep.{0, u, uV} ℂ 𝐌} (b : B.representation.Equiv B'.representation)

include b in
/-- Joint convergence is invariant under equivalence of the inducing representation. -/
theorem cConverges_of_equiv (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B) :
    CConverges hG hi hν I I' hζ hζ' n hn K hK B' :=
  ⟨factorConverges_of_equiv hG hi hν I I' hζ n hn ζ' hα₊ b K hK hB.1,
    factorConverges_of_equiv hG hi hν I I' hζ n hn (-ζ') hα₋ (contragredientEquivOf b) K hK hB.2⟩

/-- `cDualFactor` unfolded. -/
theorem cDualFactor_apply (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hB : FactorConverges hG hi hν I I' hζ n hn (-ζ') hα₋ K hK
      (conjugateRep hG hi hν I I' hζ n hn (-ζ') hα₋ B.contragredient))
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B.contragredient) :
    cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB f =
      normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
        (SmoothRep.equivOfIso (contragredientPullbackIso (eₛ).symm B).symm)
        (cFactor hG hi hν I I' hζ n hn (-ζ') hα₋ K hK hCST B.contragredient hB f) :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **Naturality of the dual factor `v̌ ↦ v̌_s`**. -/
theorem cDualFactor_natural
    (hB : FactorConverges hG hi hν I I' hζ n hn (-ζ') hα₋ K hK
      (conjugateRep hG hi hν I I' hζ n hn (-ζ') hα₋ B.contragredient))
    (hB' : FactorConverges hG hi hν I I' hζ n hn (-ζ') hα₋ K hK
      (conjugateRep hG hi hν I I' hζ n hn (-ζ') hα₋ B'.contragredient))
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B.contragredient) :
    cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B' hB'
        (normalizedInductionEquivOfEquiv _ _ (contragredientEquivOf b) f) =
      normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
        (contragredientEquivOf (lowerPullbackEquiv hG hi hν I I' hζ n hn b))
        (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB f) := by
  rw [cDualFactor_apply, cDualFactor_apply, cFactor_lowerPullback_natural]
  apply Subtype.ext
  apply Subtype.ext
  funext l
  apply Subtype.ext
  rfl

variable (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- `cMap` unfolded: `γ(G|M')⁻¹` times the tensor of the two factors. -/
theorem cMap_apply [CompactSpace (Induction.LeftQuotient (standardParabolicPoints i ν (rootSet i ν I)))]
    [CompactSpace (Induction.LeftQuotient (DynamicOppositeStandardIntertwining.parabolic χs))]
    (B : SmoothRep.{0, u, uV} ℂ 𝐌) (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B)
    (F : productInducedCoefficientObject
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B) :
    cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB F =
      ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹) •
        normalizedProductInductionTensorEquiv (decomposition χs) (decomposition χs)
          (radical_isClosed χs) (radical_isClosed χs)
          (SmoothRep.pullback (eₛ).symm B) (SmoothRep.pullback (eₛ).symm B).contragredient
          (TensorProduct.map (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1)
            (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2)
            ((normalizedProductInductionTensorEquiv
              (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
              (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
              (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
              (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
              B B.contragredient).symm F)) :=
  rfl


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The c-map on a pure tensor `v ⊗ v̌` is `γ(G|M')⁻¹ (v_s ⊗ v̌_s)`. -/
theorem cMap_tmul [CompactSpace (Induction.LeftQuotient (standardParabolicPoints i ν (rootSet i ν I)))]
    [CompactSpace (Induction.LeftQuotient (DynamicOppositeStandardIntertwining.parabolic χs))]
    (B : SmoothRep.{0, u, uV} ℂ 𝐌) (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B)
    (f : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B)
    (f' : (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B.contragredient) :
    cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB
        (productCoefficientTensorMap
          (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B (f ⊗ₜ[ℂ] f')) =
      ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹) •
        productCoefficientTensorMap (decomposition χs) (radical_isClosed χs)
          (SmoothRep.pullback (eₛ).symm B)
          (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1 f ⊗ₜ[ℂ]
            cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2 f') :=
  ((cMap_apply hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB _).trans
    (congrArg (fun t => ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK :
        ℂ)⁻¹) • normalizedProductInductionTensorEquiv (decomposition χs) (decomposition χs)
          (radical_isClosed χs) (radical_isClosed χs)
          (SmoothRep.pullback (eₛ).symm B) (SmoothRep.pullback (eₛ).symm B).contragredient
          (TensorProduct.map (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1)
            (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2) t))
      (Representation.Equiv.symm_apply_apply (normalizedProductInductionTensorEquiv
          (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
          (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
          (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
          B B.contragredient) (f ⊗ₜ[ℂ] f')))).trans
    (congrArg (fun t => ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK :
        ℂ)⁻¹) • normalizedProductInductionTensorEquiv (decomposition χs) (decomposition χs)
          (radical_isClosed χs) (radical_isClosed χs)
          (SmoothRep.pullback (eₛ).symm B) (SmoothRep.pullback (eₛ).symm B).contragredient t)
      (TensorProduct.map_tmul (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1)
        (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2) f f'))

attribute [local irreducible] cMap in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Naturality of the c-map**: for an equivalence `b : B ≃ B'` of representations of `M_I(F)`
on which both integrals converge, the c-map of `B'` after the coefficient transport by `b` is
the coefficient transport by `b` (read on `s·M`) of the c-map of `B`. -/
theorem cMap_natural (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B)
    (hB' : CConverges hG hi hν I I' hζ hζ' n hn K hK B')
    (F : productInducedCoefficientObject
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B) :
    cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B' hB'
        (productInducedCoefficientTransport _ _ b F) =
      productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
        (lowerPullbackEquiv hG hi hν I I' hζ n hn b)
        (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB F) := by
  have : CompactSpace (Induction.LeftQuotient (standardParabolicPoints i ν (rootSet i ν I))) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK
      (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
  have : CompactSpace (Induction.LeftQuotient (DynamicOppositeStandardIntertwining.parabolic χs)) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK' (fun g => by
      obtain ⟨p, k, h⟩ := hPK' g
      exact ⟨p, p.property, k, k.property, h⟩)
  have key : (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B' hB').comp
      ((productInducedCoefficientTransport _ _ b).toLinearMap.comp
        (productCoefficientTensorMap (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B)) =
      (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
        (lowerPullbackEquiv hG hi hν I I' hζ n hn b)).toLinearMap.comp
        ((cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB).comp
          (productCoefficientTensorMap (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B)) := by
    apply TensorProduct.ext'
    intro f f'
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      Representation.Equiv.coe_toLinearMap, Representation.Equiv.coe_toLinearMap,
      transport_coefficientTensorMap,
      cMap_tmul hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B' hB',
      cFactor_lowerPullback_natural, cDualFactor_natural,
      cMap_tmul hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB, map_smul,
      transport_coefficientTensorMap]
  obtain ⟨t, ht⟩ := coefficientTensorMap_surjective
    (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B F
  subst ht
  have h := LinearMap.congr_fun key t
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Representation.Equiv.coe_toLinearMap, Representation.Equiv.coe_toLinearMap] at h
  exact h

end CMap

end WeakExpansion

end Langlands.HarishChandraSchwartz
