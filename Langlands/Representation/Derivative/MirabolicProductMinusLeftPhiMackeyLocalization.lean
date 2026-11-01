import Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
import Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-! Actual left mixed-product Mackey projection after positive-character localization. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction MixedProductTensor Geometric
  Induction.SplitKernelLocalization

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (k r : ℕ)

set_option maxHeartbeats 800000 in
/-- The actual two-orbit Mackey sequence on smooth higher inducing coefficients,
with the cycle first and the identity quotient last. -/
theorem leftPhiMackey_exists_exact :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    ∃ (i : orbitPiece.{0, uF, uV} (R := ℂ) (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier 0) ⟶
        restrictedCompactInduction (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier))
      (q : restrictedCompactInduction.{0, uF, uV} (R := ℂ) (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) ⟶
        orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (leftRepresentative k r F.Carrier 1)),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearNonarchimedean (k + r + 3)
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearT2Space (k + r + 3)
  let := T.generalLinearSigmaCompactSpace (k + r + 3)
  let : LocallyCompactSpace (mirabolic (k + r + 2) F.Carrier) := Mirabolic.locallyCompactSpace
  let : SigmaCompactSpace (mirabolic (k + r + 2) F.Carrier) :=
    (GeneralLinear.Mirabolic.isClosed (n := k + r + 2) (F := F.Carrier)).sigmaCompactSpace
  obtain ⟨s, hs⟩ := (mirabolicMixedOrbitCoverage F T).1 k r
  have hM := closedSubgroupMackeyFiltration.{uF, uV}
    (mirabolic (k + r + 2) F.Carrier) (leftInducing k r F.Carrier)
    (plusSubgroup (k + r + 1) F.Carrier) (leftInducing_isClosed k r F.Carrier)
    plusSubgroup_isClosed 2 s
  obtain ⟨e₀⟩ := hM 0
  obtain ⟨e₁⟩ := hM 1
  rw [hs] at e₀ e₁
  exact RepFunctorFiltration.exists_exact_of_two _ e₀ e₁

/-- One natural cycle injection, chosen once on all smooth inducing coefficients. -/
def leftPhiMackeyInjection :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    orbitPiece.{0, uF, uV} (R := ℂ) (leftInducing k r F.Carrier)
        (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier 0) ⟶
      restrictedCompactInduction (leftInducing k r F.Carrier)
        (plusSubgroup (k + r + 1) F.Carrier) :=
  Classical.choose (leftPhiMackey_exists_exact T k r)

/-- The natural quotient onto the actual identity orbit. -/
def leftPhiMackeyProjection :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    restrictedCompactInduction.{0, uF, uV} (R := ℂ) (leftInducing k r F.Carrier)
        (plusSubgroup (k + r + 1) F.Carrier) ⟶
      orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
        (leftRepresentative k r F.Carrier 1) :=
  Classical.choose (Classical.choose_spec (leftPhiMackey_exists_exact T k r))

/-- Exactness and surjectivity retain the full compact-function carriers. -/
theorem leftPhiMackey_exact :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    ∀ X, Function.Injective ((leftPhiMackeyInjection T k r).app X).hom ∧
      LinearMap.range ((leftPhiMackeyInjection T k r).app X).hom.toLinearMap =
        LinearMap.ker ((leftPhiMackeyProjection T k r).app X).hom.toLinearMap ∧
      Function.Surjective ((leftPhiMackeyProjection T k r).app X).hom :=
  Classical.choose_spec (Classical.choose_spec (leftPhiMackey_exists_exact T k r))

/-- The higher coefficient uses only existing tensor, covariance twist and
continuous inducing-hom pullback functors. -/
abbrev leftPhiMackeyInput :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, uV} ℂ (leftInducing k r F.Carrier) :=
  letI := T.topology
  externalFunctor ⋙ pullbackFunctor leftProjection continuous_leftProjection ⋙
    SmoothRep.twistFunctor (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
      (T.leftCharacter (k + 1) (r + 1)).isOpen_ker ⋙
    pullbackFunctor (leftInducingHom k r F.Carrier) (continuous_leftInducingHom k r F.Carrier)

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Positive-character kernel localization with its actual successor section
 action; this is elementary subgroup localization, with no plus functor. -/
def leftPhiPlusKernelFunctor :
    letI := T.topology
    Rep.{uV} ℂ (plusSubgroup (k + r + 1) F.Carrier) ⥤
      Rep.{uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  {
  obj A := Rep.of (localizedAction
    (plusProjection (n := k + r + 1) (F := F.Carrier))
    (plusSuccessor (n := k + r + 1) (F := F.Carrier))
    (plusKernelTheta ψ (k + r + 1))
    (plusKernelTheta_sectionInvariant ψ (k + r + 1)) A.ρ)
  map f := Rep.ofHom (sectionMap
    (plusProjection (n := k + r + 1) (F := F.Carrier))
    (plusSuccessor (n := k + r + 1) (F := F.Carrier))
    (plusKernelTheta ψ (k + r + 1))
    (plusKernelTheta_sectionInvariant ψ (k + r + 1)) f.hom)
  map_id A := by
    apply Rep.hom_ext
    exact sectionMap_id _ _ _ _ _
  map_comp f g := by
    apply Rep.hom_ext
    exact sectionMap_comp _ _ _ _ _ _
  }

set_option maxHeartbeats 3000000 in
/-- The whole localized cycle orbit is zero for the actual higher normalized
coefficient, using the published full stages comparison and cycle vanishing. -/
theorem leftPhiMackeyLocalizedCycle_subsingleton
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    Subsingleton (((leftPhiMackeyInput T k r ⋙
      orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
        (leftRepresentative k r F.Carrier 0) ⋙ leftPhiPlusKernelFunctor T k r ψ).obj X) : Type _) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let σ := leftPhiNormalizedStabilizer T k r X.1.representation X.2.representation 0
  change Subsingleton (Jacquet.Localization.Coinvariants
    (compactInduced (leftStabilizer k r F.Carrier 0) σ)
    (plusProjection (n := k + r + 1) (F := F.Carrier)).ker
    (plusKernelTheta ψ (k + r + 1)))
  have hσ : IsSmooth σ := isSmooth_comp _
    (continuous_stabilizerToInducing (leftInducing k r F.Carrier)
      (leftRepresentative k r F.Carrier 0))
    ((leftPhiMackeyInput T k r).obj X).isSmooth
  let e := padic_leftPhiStagesCharacterEquiv T ψ k r 0 σ hσ
  let := leftPhiNormalizedStagesQuotient_zero_subsingleton T k r
    X.1.representation X.2.representation ψ
  have ht : Subsingleton (CompactFunctions
      ((leftStages k r F.Carrier 0).comap plusSuccessor)
      (leftPhiStagesAction k r ψ 0 σ)) := inferInstance
  exact e.toLinearEquiv.injective.subsingleton

private theorem sectionMap_bijective_of_subsingleton
    {G L : Type*} [Group G] [Group L]
    {V W Z : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (a : G →* L) (s : L →* G) (θ : a.ker →* ℂˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate a s l n) = θ n)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G Z} (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hz : Subsingleton (Jacquet.Localization.Coinvariants ρ a.ker θ)) :
    Function.Bijective (sectionMap a s θ hθ q) := by
  have hMU : (⊥ : Subgroup G) ≤ Subgroup.normalizer a.ker := bot_le
  have hinv : Jacquet.Localization.IsInvariant a.ker ⊥ hMU θ := by
    intro m n
    apply congrArg θ
    apply Subtype.ext
    have hm : (m : G) = 1 := Subgroup.mem_bot.mp m.property
    simp [Jacquet.Localization.conjugate, hm]
  have hex' :
      LinearMap.range (Jacquet.Localization.mapLinear a.ker θ i) =
        LinearMap.ker (Jacquet.Localization.mapLinear a.ker θ q) :=
    Jacquet.Localization.map_range_eq_ker a.ker θ ⊥ hMU hinv i q hq hex
  have hsurj : Function.Surjective (Jacquet.Localization.mapLinear a.ker θ q) :=
    Jacquet.Localization.map_surjective a.ker θ ⊥ hMU hinv q hq
  refine ⟨?_, hsurj⟩
  intro x y hxy
  have hmem : x - y ∈ LinearMap.ker (Jacquet.Localization.mapLinear a.ker θ q) := by
    change (sectionMap a s θ hθ q) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [← hex'] at hmem
  obtain ⟨z, hz'⟩ := hmem
  have hz0 : z = 0 := hz.elim _ _
  rw [hz0, map_zero] at hz'
  exact sub_eq_zero.mp hz'.symm

/-- The actual Mackey quotient, first restricted to the full higher normalized
coefficient, then localized along the actual positive kernel character. -/
def leftPhiMackeyLocalizedProjection :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    leftPhiMackeyInput T k r ⋙
        restrictedCompactInduction (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) ⋙ leftPhiPlusKernelFunctor T k r ψ ⟶
      leftPhiMackeyInput T k r ⋙
        orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (leftRepresentative k r F.Carrier 1) ⋙ leftPhiPlusKernelFunctor T k r ψ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  Functor.whiskerLeft (leftPhiMackeyInput T k r)
    (Functor.whiskerRight (leftPhiMackeyProjection T k r) (leftPhiPlusKernelFunctor T k r ψ))

set_option maxHeartbeats 3000000 in
/-- Right exactness and full cycle vanishing make the actual localized
identity-orbit projection bijective at every input pair. -/
theorem leftPhiMackeyLocalizedProjection_bijective
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    Function.Bijective ((leftPhiMackeyLocalizedProjection T k r ψ).app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let Y := (leftPhiMackeyInput T k r).obj X
  obtain ⟨_, hex, hq⟩ := leftPhiMackey_exact T k r Y
  exact sectionMap_bijective_of_subsingleton
    (plusProjection (n := k + r + 1) (F := F.Carrier))
    (plusSuccessor (n := k + r + 1) (F := F.Carrier))
    (plusKernelTheta ψ (k + r + 1))
    (plusKernelTheta_sectionInvariant ψ (k + r + 1))
    ((leftPhiMackeyInjection T k r).app Y).hom
    ((leftPhiMackeyProjection T k r).app Y).hom hq hex
    (leftPhiMackeyLocalizedCycle_subsingleton T k r ψ X)

set_option maxHeartbeats 3000000 in
/-- The entire character-localized mixed compact induction is naturally
isomorphic to its actual identity orbit, by the actual Mackey quotient. -/
def leftPhiMackeyLocalizedIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    leftPhiMackeyInput T k r ⋙
        restrictedCompactInduction (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) ⋙ leftPhiPlusKernelFunctor T k r ψ ≅
      leftPhiMackeyInput T k r ⋙
        orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (leftRepresentative k r F.Carrier 1) ⋙ leftPhiPlusKernelFunctor T k r ψ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let q := leftPhiMackeyLocalizedProjection.{uF, uV} T k r ψ
  refine NatIso.ofComponents (fun X => Rep.mkIso
    { toLinearEquiv := LinearEquiv.ofBijective (q.app X).hom.toLinearMap
        (leftPhiMackeyLocalizedProjection_bijective T k r ψ X)
      isIntertwining' := (q.app X).hom.isIntertwining' }) ?_
  intro X Y f
  exact q.naturality f

end Langlands.Derivative.MirabolicProductMinus
