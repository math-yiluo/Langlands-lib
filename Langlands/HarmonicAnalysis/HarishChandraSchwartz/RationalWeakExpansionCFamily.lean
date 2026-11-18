import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLowerOrbit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionAuxiliaryParabolics
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.Representation.Plancherel.DynamicCommonLeviSquaredModulus
import Langlands.Representation.Aubert.General.RealizedLeviStages
import Langlands.Representation.Plancherel.LeviCoefficientConjugation
import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Plancherel.RationalSourceGammaIntegral
import Langlands.Group.LeftQuotientInversion
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicInducedOrbitWavePacket

/-! # The c-family `c_{P'|P}(s, ω)` of Waldspurger V.1 on actual rational points

For `s ∈ W(M'|G|M)` with representative `n` (`n M_I n⁻¹ ⊂ M'`), Waldspurger V.1 (printed
pp.288–289) defines
`c_{P'|P}(s, ω)(v ⊗ v̌) = γ(G|M')⁻¹ [J_{P_s|s·P}(sω)λ(s)v ⊗ J_{P̃_s|s·P}(sω̌)λ(s)v̌]`,
`P_s = (M' ∩ s·P)U'`, `P̃_s = (M' ∩ s·P)Ū'`, read through restriction to `M'`.

* `cFactor`: `v ↦ v_s = δ_{P(α)}^{-1/2} (J_{P_α|s·P} λ(s) v)|_{M'}` for `α = ±ζ'`, built from
  the published `inductionConjugationIsoApp`, `fullSourceIntertwiner` (with the pair measures at
  `K`) and `RealizedLeviStages.inductionInStagesIso`.
* `cMap`: `γ(G|M')⁻¹ (v_s ⊗ v̌_s)` on the actual product-induced coefficient spaces, at a
  representation where both integrals converge (`CConverges`).
* `cFamily`, `cCompactFamily`: the family in the unramified parameter on its joint convergence
  domain `cDomain`, and its form on the fixed compact pictures.
* `cWeightedCompactFamily`: `c̃_{P'|P}(s, ω) = µ^G(ω) µ^{M'}(sω)⁻¹ c_{P'|P}(s, ω)` (V.2.3) at
  the points of `cWeightedDomain`.

Rationality and regularity are targets of `RationalWeakExpansionTargets`, not premises.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance cFamilyAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance cFamilyLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cFamilyLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance cFamilyLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
set_option hygiene false in
local notation "ψs" => CommGroupScheme.groupHom (cParabolicCocharacter i ζ' ζ n) ≫ i
set_option hygiene false in
local notation "ψ̃s" => CommGroupScheme.groupHom (cOppositeParabolicCocharacter i ζ' ζ n) ≫ i
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "jI'" => Standard.leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

/-! ### Geometry of `s·P`, `P_s` and `P̃_s` -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- `s·P = n P_I(F) n⁻¹`: membership in the actual dynamic parabolic of the conjugated
cocharacter is membership of the conjugate by `n⁻¹` in `P_I(F)`. -/
theorem mem_conjugatedParabolic_iff (x : rationalPoints G) :
    x ∈ (Dynamic.parabolic θs).carrier X₀ ↔
      (n : rationalPoints G)⁻¹ * x * n ∈ standardParabolicPoints i ν (rootSet i ν I) := by
  rw [(conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ
    n).1]
  change x ∈ (conjugatedParabolic i ν (rootSet i ν I) n).rationalPoints ↔ _
  rw [conjugatedParabolic, SubgroupFunctor.rationalPoints_comap_innerIso_inv]
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- The radical of `s·P` is `n U_I(F) n⁻¹`. -/
theorem mem_conjugatedRadical_iff (x : rationalPoints G) :
    x ∈ (Dynamic.unipotent θs).carrier X₀ ↔
      (n : rationalPoints G)⁻¹ * x * n ∈ standardUnipotentPoints i ν (rootSet i ν I) := by
  rw [(conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ
    n).2.2]
  change x ∈ (conjugatedUnipotent i ν (rootSet i ν I) n).rationalPoints ↔ _
  rw [conjugatedUnipotent, SubgroupFunctor.rationalPoints_comap_innerIso_inv]
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- The Levi `s·M = n M_I(F) n⁻¹`, as the centralizer of any cocharacter with the centralizer
of `θ_s`. -/
theorem mem_conjugatedLevi_iff_of_centralizer_eq
    {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer θs) (x : rationalPoints G) :
    x ∈ (Dynamic.centralizer ψ).carrier X₀ ↔
      (n : rationalPoints G)⁻¹ * x * n ∈ standardLeviPoints i ν (rootSet i ν I) := by
  rw [hψ, (conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ
    hζ n).2.1]
  change x ∈ (conjugatedLevi i ν (rootSet i ν I) n).rationalPoints ↔ _
  rw [conjugatedLevi_points]
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-! ### The auxiliary parabolics `P_s = (M' ∩ s·P)U'` and `P̃_s = (M' ∩ s·P)Ū'`

Both are treated at once: `α` is a cocharacter of `T` whose centralizer is `M' = M_{I'}`
(`α = ζ'` gives `P' = M'U'` and `P_s`; `α = -ζ'` gives `P̄' = M'Ū'` and `P̃_s`), and
`ψ_α = auxiliaryCocharacter i α (sζ)` is the auxiliary cocharacter of
`RationalWeakExpansionAuxiliaryParabolics`. -/

section Auxiliary

variable (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "θα" => CommGroupScheme.groupHom α ≫ i

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hα in
/-- The outer Levi `M'` is represented by the actual standard Levi scheme. -/
theorem outer_isRepresentedBy : (Dynamic.centralizer θα).IsRepresentedBy jI' :=
  hα.symm ▸ Standard.isRepresentedBy_leviHom i ν _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hn hα in
/-- The auxiliary parabolic has the Levi `s·M`. -/
theorem centralizer_auxiliary : Dynamic.centralizer ψα = Dynamic.centralizer θs :=
  (auxiliaryParabolic_geometry i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
    (rootSet_subset i ν I) ζ hζ n hn α hα).1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hn hα in
/-- **Realization of the auxiliary parabolic through `M'`**: its parabolic and radical are the
extensions from `M'` of those of the lower cocharacter `χ_s`, and its Levi is the image of the
Levi of `χ_s`. These are the hypotheses of `RealizedLeviStages`. -/
theorem auxiliary_realization :
    Dynamic.parabolic ψα = Dynamic.extendFromCentralizer θα jI'
        (outer_isRepresentedBy (i := i) (ν := ν) I' α hα) (Dynamic.parabolic χs) ∧
      Dynamic.centralizer ψα = (Dynamic.centralizer χs).map jI' ∧
      Dynamic.unipotent ψα = Dynamic.extendFromCentralizer θα jI'
        (outer_isRepresentedBy (i := i) (ν := ν) I' α hα) (Dynamic.unipotent χs) := by
  have h := auxiliaryParabolic_geometry i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
    (rootSet_subset i ν I) ζ hζ n hn α hα
  have hlow := lowerCocharacter_dynamic i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
    (rootSet_subset i ν I) ζ hζ n
  refine ⟨?_, ?_, ?_⟩
  · rw [hlow.1]
    exact h.2.2.2.1
  · rw [h.1, hlow.2.1, lowerLevi, SubgroupFunctor.map_comap,
      (Standard.isRepresentedBy_leviHom i ν _).2,
      (conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ
        n).2.1]
    apply SubgroupFunctor.ext
    intro X
    ext x
    exact ⟨fun hx => ⟨hn X hx, hx⟩, fun hx => hx.2⟩
  · rw [hlow.2.2]
    exact h.2.2.2.2

end Auxiliary

/-- Evaluation of smooth induced functions at the identity, as a linear map. -/
def evalOneLinear {X : Type*} [Group X] [TopologicalSpace X] {P : Subgroup X} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ P V) :
    Induction.SmoothFunctions P σ →ₗ[ℂ] V where
  toFun f := Induction.eval P σ f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### One factor `v ↦ δ_{P'}(·)^{-1/2} (J_{P_α|s·P} λ(s) v)|_{M'}` -/

section Factor

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology

local instance cFamilyRadicalMeasurableSpace
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : MeasurableSpace (radical ψ) := borel _
local instance cFamilyRadicalBorelSpace
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : BorelSpace (radical ψ) := ⟨rfl⟩
local instance cFamilyIntersectionMeasurableSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace ((radical ψ).subgroupOf (radical ψ')) := borel _
local instance cFamilyIntersectionBorelSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace ((radical ψ).subgroupOf (radical ψ')) := ⟨rfl⟩
local instance cFamilyQuotientMeasurableSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (StandardIntertwining.QuotientSpace (U := radical ψ) (radical ψ')) := borel _
local instance cFamilyQuotientBorelSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (StandardIntertwining.QuotientSpace (U := radical ψ) (radical ψ')) := ⟨rfl⟩

-- `M_I(F)` as a subtype of `G(F)`, written as in `rationalInducedSmoothOrbitSections`.
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

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hn hα in
/-- The conjugation `x ↦ n⁻¹ x n` carries the Levi `Z_G(ψ_α)(F) = s·M` onto `M_I(F)`. -/
theorem auxiliaryLevi_conj_iff (x : rationalPoints G) :
    x ∈ DynamicOppositeStandardIntertwining.levi ψα ↔
      (n : rationalPoints G)⁻¹ * x * n ∈ standardLeviPoints i ν (rootSet i ν I) :=
  mem_conjugatedLevi_iff_of_centralizer_eq hG hi hν I hζ n
    (centralizer_auxiliary hG hi hν I I' hζ n hn α hα) x

/-- **The left translation `λ(s)`** (`f ↦ f(n⁻¹ ·)`), from the normalized induction
`I_{P_I}^G B` to the normalized induction from `s·P = n P_I(F) n⁻¹` of the conjugate
`ⁿB = B(n⁻¹ · n)` of `B`, a representation of `s·M = Z_G(ψ_α)(F)`. This is the published
`inductionConjugationIsoApp`. -/
def factorTranslation (B : SmoothRep.{0, u, uV} ℂ 𝐌) :
    ((normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B).representation.Equiv
      ((normalizedInductionFunctor (commonDecomposition ψα θs hθψ) (radical_isClosed θs)).obj
        ((conjugationFunctor (n : rationalPoints G)
          (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)).obj B)).representation :=
  SmoothRep.equivOfIso
    (inductionConjugationIsoApp
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
      (commonDecomposition ψα θs hθψ) (n : rationalPoints G)
      (mem_conjugatedParabolic_iff hG hi hν I hζ n)
      (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)
      (mem_conjugatedRadical_iff hG hi hν I hζ n)
      (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) (radical_isClosed θs) B)

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

/-- **Convergence of `J_{P_α|s·P}` on a representation `A` of `s·M`**: every vector of the
normalized induction from `s·P` has absolutely convergent smooth-dual integrals over
`(U_{s·P} ∩ U_α)\U_α`, represented in the carrier of `A` (the full domain of the published
standard integral, for the source quotient measure normalized at `K`). -/
def FactorConverges
    (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα)) : Prop :=
  StandardIntertwining.domain (commonDecomposition ψα θs hθψ) (radical_isClosed θs) (radical ψα) A
    (pairQuotientMeasure K hK θs ψα) = ⊤

/-- **The standard integral `J_{P_α|s·P}`** on a representation `A` of `s·M` where it converges:
the published full-source standard integral between the two parabolics with the common Levi
`s·M`, with the pair Haar measures normalized at `K`. Its squared-modulus premise is discharged by
`squaredModulus_of_centralSplitTorusCharacter`. At the twist of `A` by an unramified parameter it
is the published `pairFamily`. -/
def factorIntertwiner (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα))
    (hA : FactorConverges hG hi hν I I' hζ n hn α hα K hK A) :
    ((DynamicNormalization.leviTwistedInductionFunctor (commonDecomposition ψα θs hθψ)
        (radical_isClosed θs)).obj A).representation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor (commonDecomposition ψα ψα rfl)
        (radical_isClosed ψα)).obj A).representation :=
  StandardIntertwining.fullSourceIntertwiner (commonDecomposition ψα θs hθψ) (radical_isClosed θs)
    (commonDecomposition ψα ψα rfl) (radical_isClosed ψα) A (pairQuotientMeasure K hK θs ψα)
    (radicalHaar ψα K hK) (pairIntersectionHaar K hK θs ψα)
    (pairQuotientMeasure_isCompatible K hK θs ψα) (levi_isClosed ψα)
    (squaredModulus_of_centralSplitTorusCharacter ψα i (conjugatedCocharacter i ζ n) hθψ
      (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) rfl hCST hG hi) hA

/-- The conjugate `ⁿB` of `B`, a representation of `s·M = Z_G(ψ_α)(F)`. -/
abbrev conjugateRep (B : SmoothRep.{0, u, uV} ℂ 𝐌) :
    SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα) :=
  (conjugationFunctor (n : rationalPoints G) (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)).obj B

set_option hygiene false in
local notation "hRα" => auxiliary_realization hG hi hν I I' hζ n hn α hα
set_option hygiene false in
local notation "hjα" => outer_isRepresentedBy (i := i) (ν := ν) I' α hα

/-- The value at `1` of the induction-in-stages comparison (auxiliary form, with inferred
codomain). -/
def factorRestrictionAux
    (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα)) :=
  (evalOneLinear _).comp
    (SmoothRep.hom ((RealizedLeviStages.inductionInStagesIso F hG θα jI' hjα
      (Standard.isClosedSubgroup_leviHom i ν _) χs ψα hRα (radical_isClosed ψα)
      (radical_isClosed θα) (levi_isClosed θα)).app A).hom).toLinearMap

set_option maxHeartbeats 1600000 in
/-- **Restriction to `M'`** (Waldspurger V.1, the maps `v ↦ v_s` of the proof of V.1.1): the
value at `1` of the published induction-in-stages comparison
`I_{P_α}^G ≅ I_{P(α)}^G ∘ I_{M' ∩ s·P}^{M'}` through the actual Levi scheme `M'`, where
`P(α)` is the outer parabolic. On functions it is `f ↦ (m' ↦ δ_{P(α)}(m')^{-1/2} f(m'))`
(`RealizedLeviStages.inductionInStagesIso_hom_eval`). -/
def factorRestriction (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα)) :
    (normalizedInductionFunctor (decomposition ψα) (radical_isClosed ψα)).obj A →ₗ[ℂ]
      (normalizedInductionFunctor (decomposition χs) (radical_isClosed χs)).obj
        ((SmoothRep.pullbackFunctor (RealizedLeviTransport.centralizerEquiv F θα jI' hjα
          (Standard.isClosedSubgroup_leviHom i ν _) χs ψα hRα)).obj
        ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv
          (Dynamic.realized_centralizer_le θα jI' hjα χs ψα hRα.2.1 X₀))).obj A)) where
  toFun f := factorRestrictionAux hG hi hν I I' hζ n hn α hα A f
  map_add' := (factorRestrictionAux hG hi hν I I' hζ n hn α hα A).map_add
  map_smul' := (factorRestrictionAux hG hi hν I I' hζ n hn α hα A).map_smul

set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

/-- The coefficient of the restricted function is the original `B`, read through `e⁻¹`: the
inner representation produced by `factorRestriction` from `ⁿB` acts by `B(n⁻¹ j(m) n)`, which is
`B(e⁻¹ m)` for `e = lowerLeviConjugation`. The identity map of the carrier is an equivalence. -/
def restrictedConjugateEquiv (B : SmoothRep.{0, u, uV} ℂ 𝐌) :
    ((SmoothRep.pullbackFunctor (RealizedLeviTransport.centralizerEquiv F θα jI' hjα
        (Standard.isClosedSubgroup_leviHom i ν _) χs ψα hRα)).obj
      ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv
        (Dynamic.realized_centralizer_le θα jI' hjα χs ψα hRα.2.1 X₀))).obj
          (conjugateRep hG hi hν I I' hζ n hn α hα B))).representation.Equiv
      (SmoothRep.pullback (eₛ).symm B).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun m => by
    apply LinearMap.ext
    intro v
    change B.representation _ v = B.representation _ v
    congr 2)

/-- **One factor of the c-family**: for a representation `B` of `M_I(F)` on which `J_{P_α|s·P}`
converges (on the conjugate `ⁿB`), the map
`I_{P_I}^G B → I_{M' ∩ s·P}^{M'} (B ∘ e⁻¹)`, `v ↦ (m' ↦ δ_{P(α)}(m')^{-1/2} (J_{P_α|s·P} λ(s) v)(m'))`.
For `α = ζ'` this is Waldspurger's `v ↦ v_s`, for `α = -ζ'` (applied to the contragredient) his
`v̌ ↦ v̌_s` (proof of V.1.1, printed p.289). -/
def cFactor (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hB : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B)) :
    (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B →ₗ[ℂ]
      (normalizedInductionFunctor (decomposition χs) (radical_isClosed χs)).obj
        (SmoothRep.pullback (eₛ).symm B) :=
  (normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
      (restrictedConjugateEquiv hG hi hν I I' hζ n hn α hα B)).toLinearMap ∘ₗ
    factorRestriction hG hi hν I I' hζ n hn α hα (conjugateRep hG hi hν I I' hζ n hn α hα B) ∘ₗ
    (normalizedInductionLeviEquiv (commonDecomposition ψα ψα rfl) (radical_isClosed ψα)
      (DynamicOppositeCanonicalScalar.radical_unimodular ψα hG)
      (conjugateRep hG hi hν I I' hζ n hn α hα B)).symm.toLinearMap ∘ₗ
    (factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST
      (conjugateRep hG hi hν I I' hζ n hn α hα B) hB).toLinearMap ∘ₗ
    (normalizedInductionLeviEquiv (commonDecomposition ψα θs hθψ) (radical_isClosed θs)
      (DynamicOppositeCanonicalScalar.radical_unimodular θs hG)
      (conjugateRep hG hi hν I I' hζ n hn α hα B)).toLinearMap ∘ₗ
    (factorTranslation hG hi hν I I' hζ n hn α hα B).toLinearMap

end Factor

/-! ### The c-family on coefficient spaces -/

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

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ' in
/-- `M' = Z_G(ζ')`. -/
theorem outerCentralizer_pos :
    Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i) = standardLevi i ν (rootSet i ν I') :=
  ((standardCocharacter F G hG T i hi ν hν (rootSet i ν I') (rootSet_subset i ν I')).2 ζ'
    hζ').2.1.symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ' in
/-- `M' = Z_G(-ζ')`. -/
theorem outerCentralizer_neg :
    Dynamic.centralizer (CommGroupScheme.groupHom (-ζ') ≫ i) =
      standardLevi i ν (rootSet i ν I') := by
  rw [Dynamic.centralizer_groupHom_neg]
  exact outerCentralizer_pos hG hi hν I' hζ'

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "hα₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "hα₋" => outerCentralizer_neg hG hi hν I' hζ'

/-- **Joint convergence** of the two standard integrals of the c-family at a representation `B`
of `M_I(F)`: `J_{P_s|s·P}` converges on `ⁿB` and `J_{P̃_s|s·P}` converges on `ⁿB̌`. In the source
these are the points `ω` where both intertwining integrals defining `c_{P'|P}(s, ω)` converge. -/
def CConverges (B : SmoothRep.{0, u, uV} ℂ 𝐌) : Prop :=
  FactorConverges hG hi hν I I' hζ n hn ζ' hα₊ K hK
      (conjugateRep hG hi hν I I' hζ n hn ζ' hα₊ B) ∧
    FactorConverges hG hi hν I I' hζ n hn (-ζ') hα₋ K hK
      (conjugateRep hG hi hν I I' hζ n hn (-ζ') hα₋ B.contragredient)

/-- The dual factor `v̌ ↦ v̌_s`, followed by the canonical identification of the pullback of the
smooth dual with the smooth dual of the pullback. -/
def cDualFactor (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hB : FactorConverges hG hi hν I I' hζ n hn (-ζ') hα₋ K hK
      (conjugateRep hG hi hν I I' hζ n hn (-ζ') hα₋ B.contragredient)) :
    (normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))).obj B.contragredient →ₗ[ℂ]
      (normalizedInductionFunctor (decomposition χs) (radical_isClosed χs)).obj
        (SmoothRep.pullback (eₛ).symm B).contragredient :=
  (normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
      (SmoothRep.equivOfIso (contragredientPullbackIso (eₛ).symm B).symm)).toLinearMap ∘ₗ
    cFactor hG hi hν I I' hζ n hn (-ζ') hα₋ K hK hCST B.contragredient hB

variable (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))

/-- **Waldspurger's c-family** `c_{P'|P}(s, ω)` (V.1, printed pp.288–289) at a representation
`B = ω` of `M_I(F)` where both integrals converge, as a linear map of the actual
source-normalized coefficient spaces
`L(ω, P) = I_{P×P}^{G×G}(B ⊗ B̌) → L^{M'}(sω, M' ∩ s·P) = I^{M'×M'}(sB ⊗ (sB)ˇ)`:
on `v ⊗ v̌` it is `γ(G|M')⁻¹ (v_s ⊗ v̌_s)`, the value at `(1,1)` of
`γ(G|M')⁻¹ [J_{P_s|s·P}(sω)λ(s)v ⊗ J_{P̃_s|s·P}(sω̌)λ(s)v̌]` read in
`I^{G×G}_{P'×P̄'} L^{M'}(sω, M' ∩ s·P)`. The constant `γ(G|M')` is the published source gamma of
the outer parabolic `P' = P(ζ')` at `K`. -/
def cMap (B : SmoothRep.{0, u, uV} ℂ 𝐌) (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B) :
    productInducedCoefficientObject
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) B →ₗ[ℂ]
      productInducedCoefficientObject (decomposition χs) (radical_isClosed χs)
        (SmoothRep.pullback (eₛ).symm B) :=
  haveI : CompactSpace (Induction.LeftQuotient (standardParabolicPoints i ν (rootSet i ν I))) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK
      (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
  haveI : CompactSpace (Induction.LeftQuotient (DynamicOppositeStandardIntertwining.parabolic χs)) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK' (fun g => by
      obtain ⟨p, k, h⟩ := hPK' g
      exact ⟨p, p.property, k, k.property, h⟩)
  ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹) •
    ((normalizedProductInductionTensorEquiv (decomposition χs) (decomposition χs)
        (radical_isClosed χs) (radical_isClosed χs)
        (SmoothRep.pullback (eₛ).symm B)
        (SmoothRep.pullback (eₛ).symm B).contragredient).toLinearEquiv.toLinearMap ∘ₗ
      TensorProduct.map (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1)
        (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2) ∘ₗ
      (normalizedProductInductionTensorEquiv
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
        B B.contragredient).symm.toLinearEquiv.toLinearMap)

/-! ### The family in the unramified parameter -/

/-- The joint convergence domain `{z ∈ X(M_I) : both integrals converge at π ⊗ z}` of the
c-family of a representation `A` of `M_I(F)`. No openness or nonemptiness is asserted. -/
def cDomain (A : SmoothRep.{0, u, uV} ℂ 𝐌) :
    Set (unramifiedCharacters (leviRationalNormCharacters i ν I)) :=
  {z | CConverges hG hi hν I I' hζ hζ' n hn K hK
    (A.twist z.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviRationalNormCharacters i ν I) z))}

/-- `s(A ⊗ z) = sA ⊗ sz`: the pullback along `e⁻¹` of the twist of `A` by `z` is the twist of
the pullback by `sz = z ∘ e⁻¹`, with the identity on the carrier. -/
def twistPullbackEquiv (A : SmoothRep.{0, u, uV} ℂ 𝐌)
    (z : unramifiedCharacters (leviRationalNormCharacters i ν I)) :
    (SmoothRep.pullback (eₛ).symm
        (A.twist z.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviRationalNormCharacters i ν I) z))).representation.Equiv
      ((SmoothRep.pullback (eₛ).symm A).twist
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z))).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ A) (fun _ => rfl)

/-- **The c-family `z ↦ c_{P'|P}(s, π ⊗ z)`** on its joint convergence domain, between the actual
coefficient spaces `L(π ⊗ z, P)` and `L^{M'}(s(π ⊗ z), M' ∩ s·P)`. -/
def cFamily (A : SmoothRep.{0, u, uV} ℂ 𝐌) (z : cDomain hG hi hν I I' hζ hζ' n hn K hK A) :
    productInducedCoefficientObject
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
        (A.twist z.val.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviRationalNormCharacters i ν I) z.val)) →ₗ[ℂ]
      productInducedCoefficientObject (decomposition χs) (radical_isClosed χs)
        ((SmoothRep.pullback (eₛ).symm A).twist
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z.val).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviNormCharacters χs)
            (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z.val))) :=
  (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
      (twistPullbackEquiv hG hi hν I I' hζ n hn A z.val)).toLinearEquiv.toLinearMap ∘ₗ
    cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ z.property

/-- **The c-family on the fixed compact pictures**: `c_{P'|P}(s, π ⊗ z)` read through restriction
to `K × K` on `G` and to `K' × K'` on `M'`, as a family of linear maps between two fixed spaces.
This is the form in which rationality in `z` is expressed (Waldspurger IV.1). -/
def cCompactFamily (A : SmoothRep.{0, u, uV} ℂ 𝐌)
    (z : cDomain hG hi hν I I' hζ hζ' n hn K hK A) :
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K A →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) K'
        (SmoothRep.pullback (eₛ).symm A) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  (productInducedCompactEquiv (leviNormCharacters χs) (decomposition χs) K'
      (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
      (DynamicInducedOrbit.leviNormCharacters_continuous χs)
      (DynamicOppositeCanonicalScalar.projection_continuous χs) (radical_isClosed χs) hPK'
      (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z.val)
      (SmoothRep.pullback (eₛ).symm A)).toLinearEquiv.toLinearMap ∘ₗ
    cFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z ∘ₗ
    (productInducedCompactEquiv (leviRationalNormCharacters i ν I)
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
      (continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
      (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      z.val A).symm.toLinearEquiv.toLinearMap

end CMap

/-! ### Densities at complex parameters and the weighted c-family `c̃` -/

section Weighted

attribute [local instance]
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

/-- **The value of a rational function at a point where it is regular**: `m(z)/n(z)` for a
chosen presentation `f = m/n` with `n(z) ≠ 0`. By `rationalFunction_value_eq` the value does not
depend on the presentation; at unitary points it is `rationalUnitaryValue`. -/
def rationalValueAt {S : GroupScheme (Spec (CommRingCat.of F))}
    [TopologicalSpace (rationalPoints S)]
    {hp : Continuous (rationalValuationImageProjection S)} {hS : IsConnectedReductive S}
    (f : rationalUnramifiedFunctionField S hp hS)
    {z : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hz : RationalFunctionRegularAt S hp hS f z) : ℂ :=
  (Classical.choose hz).val z / (Classical.choose (Classical.choose_spec hz)).val z

/-- The value is `m(z)/n(z)` for every presentation `f = m/n` with `n(z) ≠ 0`. -/
theorem rationalValueAt_eq {S : GroupScheme (Spec (CommRingCat.of F))}
    [TopologicalSpace (rationalPoints S)]
    {hp : Continuous (rationalValuationImageProjection S)} {hS : IsConnectedReductive S}
    {f : rationalUnramifiedFunctionField S hp hS}
    {z : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hz : RationalFunctionRegularAt S hp hS f z)
    {m d : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hd : d.val z ≠ 0)
    (hf : f = algebraMap _ (rationalUnramifiedFunctionField S hp hS) m /
      algebraMap _ (rationalUnramifiedFunctionField S hp hS) d) :
    rationalValueAt f hz = m.val z / d.val z := by
  have hspec := Classical.choose_spec (Classical.choose_spec hz)
  exact rationalFunction_value_eq S hp hS hspec.1 hd hspec.2 hf

section Package

variable {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {j : S.toGrp ⟶ H} {ξ : cocharacterLattice S}
  {hRefl : RelativeRootReflectionExistenceStatement.{u}}
  {hCST : CentralSplitTorusCharacterStatement.{u}} {hH : IsConnectedReductive H}
  {A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ξ ≫ j))}

/-- **Waldspurger's density `µ = j_P⁻¹ ∏_α γ(M_α|M)²` of a density package**, as a rational
function on the unramified characters (the published `plancherelDensity` with the data of the
package). Its value function on the unitary characters is the package weight. -/
abbrev packageDensity (P : DynamicInducedOrbit.DensityPackage j ξ hRefl hCST hH A) :=
  RationalPlancherelDensity.plancherelDensity j ξ hRefl hCST hH P.K P.hK P.hPK P.hOppK A P.p P.q
    P.hneForward P.hDForwardΩ P.hneReverse P.hDReverseΩ P.hne P.hirr

end Package

-- `M_I(F)` as a subtype of `G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)

/-- **The complex restriction `X(M_I) → X(Z_G(ζ ∘ i))`**, `z ↦ z ∘ e`, the parameter at which the
density `µ^G` of the published `standardLeviPlancherelWeight` is evaluated (the complex version
of `standardLeviCharacterRestrict`). -/
def standardLeviUnramifiedRestrict
    (z : unramifiedCharacters (leviRationalNormCharacters i ν I)) :
    unramifiedCharacters (fun ψ => (rationalNormCharacters MS ψ).toMul) :=
  rationalUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom
    ((unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I)
      (fun ψ => (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) ψ).toMul)).symm
        z)

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

/-- **The common source normalization of the Haar measures** (Waldspurger I.1, printed p.240:
one special compact `K`, and every closed subgroup `H` normalized by `H ∩ K`). The density
`µ^G` of the package `PG` is formed with the compact open subgroup `K` of the c-map, and the
density `µ^{M'}` of the lower package `PM` with `K ∩ M'(F)`, read on the actual Levi scheme
(the published `leviSchemeCompact`). The other data of the packages (continuations, convergence
and irreducibility domains, regularity witnesses) remain independent. -/
structure CommonCompactNormalization : Prop where
  ambient : PG.K.toSubgroup = K.toSubgroup
  lower : PM.K.toSubgroup = leviSchemeCompact K.toSubgroup i ν (rootSet i ν I')

/-- **The domain of the weighted c-family**: the joint convergence domain of the two integrals,
intersected with the points where `µ^G` is regular at `π ⊗ z` and where `µ^{M'}` is regular at
`s(π ⊗ z)` with **nonzero value** there. At the remaining points, in particular at the zeros of
`µ^{M'}`, the weighted family is not defined by this module; its values there are those of a
rational continuation (module `RationalWeakExpansionTargets`). No openness or nonemptiness is
asserted. -/
def cWeightedDomain : Set (unramifiedCharacters (leviRationalNormCharacters i ν I)) :=
  {z | z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj ∧
    RationalFunctionRegularAt MS (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ hG) (packageDensity PG)
      (standardLeviUnramifiedRestrict hG hi hν I hζ z) ∧
    ∃ hz : RationalFunctionRegularAt (parameterScheme χs)
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ (lowerAmbient_isConnectedReductive hG hi hν I'))
      (packageDensity PM)
      ((parameterTransport χs).symm (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)),
      rationalValueAt (packageDensity PM) hz ≠ 0}

/-- **The weighted c-family** `c̃_{P'|P}(s, π ⊗ z) = µ^G(π ⊗ z) µ^{M'}(s(π ⊗ z))⁻¹ c_{P'|P}(s, π ⊗ z)`
(Waldspurger V.2.3, printed p.294), on the fixed compact pictures, at the points of
`cWeightedDomain`. The densities are the values there of the rational functions of the
published `standardLeviPlancherelWeight` (package `PG`) and of the lower density `µ^{M'}`
(package `PM`); at unitary points these values are the two weights. The value of `µ^{M'}` is
nonzero on `cWeightedDomain`, so the inverse is an actual inverse. The definition requires the
common source normalization `CommonCompactNormalization`: the c-map and both densities use the
Haar measures normalized by the same `K` (resp. `K ∩ M'(F)`), as in V.2.3. The hypothesis only
restricts the inputs; it does not enter the formula. -/
def cWeightedCompactFamily
    (_hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)
    (z : cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM) :
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) K'
        (SmoothRep.pullback (eₛ).symm π.obj) :=
  (rationalValueAt (packageDensity PG) z.property.2.1 *
      (rationalValueAt (packageDensity PM) z.property.2.2.fst)⁻¹) •
    cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' π.obj ⟨z.val, z.property.1⟩

end Weighted

end WeakExpansion

end Langlands.HarishChandraSchwartz
