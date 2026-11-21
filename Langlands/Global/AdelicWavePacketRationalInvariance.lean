import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinRationalCosets
import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone

/-! # Rational invariance of pointwise Eisenstein continuations and wave packets

Reindex the convergent-region sum, propagate the invariance by scalar meromorphic uniqueness,
then integrate coefficients supported where the continuations are holomorphic. Only rational
invariance, not automorphic growth or regularity in the adelic variable, is asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Global.AdelicGroupPoints Langlands.Plancherel Langlands.LinearAlgebra
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

-- The following surjectivity and scaling argument uses the regular-region proof of
-- AdelicIntertwiningCocycleReduction, through its actual parabolic and split-component data.
private theorem realPart_surjective : Function.Surjective (parameterRealPart F P) := by
  let f : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
    AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id
  have hf : (parameterRealPart F P).comp f = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro s χ
    change (s : ℂ).re ⊗ₜ[ℤ] χ = s ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  exact fun y => ⟨f y, LinearMap.congr_fun hf y⟩

private theorem restriction_real_surjective
    (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    Function.Surjective (realParameterRestriction (F := F) (a ≫ l)) := by
  let f := (characterRestrict (a ≫ l)).toIntLinearMap
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  have hsurj : Function.Surjective (characterRestrict l) := by
    intro χ
    refine ⟨characterRestrict π χ, ?_⟩
    change ((characterRestrict l).comp (characterRestrict π)) χ = χ
    rw [← characterRestrict_comp, hπ, characterRestrict_id]
    rfl
  have hf : Function.Surjective (f.baseChange ℚ) := by
    have hs₁ := LinearMap.baseChange_surjective ℚ
      (g := (characterRestrict l).toIntLinearMap) hsurj
    have hs₂ := ha.rationalCharacterRestrictRat_surjective hl.isConnectedReductive
    change Function.Surjective (((characterRestrict (a ≫ l)).toIntLinearMap).baseChange ℚ)
    rw [characterRestrict_comp]
    change Function.Surjective (((characterRestrict a).toIntLinearMap.comp
      (characterRestrict l).toIntLinearMap).baseChange ℚ)
    rw [LinearMap.baseChange_comp]
    exact hs₂.comp hs₁
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.baseChange_surjective ℝ hf)
    ((rationalRealTensorEquiv (characterLattice A)).symm y)
  refine ⟨rationalRealTensorEquiv (rationalCharacters P) x, ?_⟩
  have hnat := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) x
  change (rationalRealTensorEquiv (characterLattice A)) ((f.baseChange ℚ).baseChange ℝ x) =
    (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) at hnat
  change (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) = y
  rw [← hnat, hx, LinearEquiv.apply_symm_apply]

/-- The set of parameters with real part `R`-regular for the given presentation is nonempty. -/
theorem regularParameter_nonempty (R : ℝ) :
    {lam : ComplexCharacterParameter F P | r.IsRegularParameter hA hT R lam}.Nonempty := by
  let : Module.Finite ℤ (characterLattice A) := hA.finite_characterLattice
  let : FiniteDimensional ℝ (RealTorusSpace.Vstar A) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] characterLattice A))
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  have hB := weylInducedCharacterForm_nondegenerate hA hT r.data.f r.data.i
  let s := max R 0 + 1
  obtain ⟨v, hv⟩ := (B.toDual hB).surjective (s • r.splitComponentEvaluation)
  obtain ⟨m, hm⟩ := restriction_real_surjective
    r.isCompatible.levi r.isCompatible.splitComponent v
  obtain ⟨lam, hlam⟩ := realPart_surjective m
  refine ⟨lam, ?_⟩
  rintro α ⟨hne, β, hβ, rfl⟩
  have hroot := (r.restrict_positive_eq_zero_or_mem hβ).resolve_left hne
  have hone : (1 : ℤ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    have hpos := hroot.2
    omega
  have hone' : (1 : ℝ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    exact_mod_cast hone
  have hs : 0 ≤ s := (le_max_right R 0).trans (le_add_of_nonneg_right zero_le_one)
  change R < B (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))
    ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ β))
  rw [hlam, hm, ← LinearMap.BilinForm.toDual_def hB, hv, LinearMap.smul_apply,
    r.splitComponentEvaluation_tmul, one_mul, smul_eq_mul]
  calc
    R < s := (le_max_left R 0).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone' hs

/-- Scalar meromorphic uniqueness starting from the actual adelic convergence chamber. -/
theorem eqOn_of_regularParameter (hG : IsConnectedReductive G)
    {f g : ComplexCharacterParameter F P → ℂ} {D D' : Set (ComplexCharacterParameter F P)}
    (hf : IsMeromorphicInCoordinatesOn f D) (hg : IsMeromorphicInCoordinatesOn g D')
    (R : ℝ) (h : ∀ lam, r.IsRegularParameter hA hT R lam → f lam = g lam) :
    EqOn f g (D ∩ D') := by
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := hf.1
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  obtain ⟨lam, hlam⟩ := r.regularParameter_nonempty hA hT R
  have hne : {s | r.IsRegularParameter hA hT R (e s)}.Nonempty :=
    ⟨e.symm lam, by simpa only [mem_ofPred_eq, LinearEquiv.apply_symm_apply] using hlam⟩
  exact hf.eqOn_of_eqOn_open hg e (Langlands.Global.isOpen_setOf_isRegularParameter r hA hT hG R e)
    hne (fun s hs => h (e s) hs.1)

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {φ : AdelicGroupPoints F G → ℂ}
  (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include hφ hU in
/-- Reindexing by right multiplication gives left rational invariance of the actual series.
This holds for the total sum: reindexing also preserves the nonsummable case. -/
theorem eisensteinSeries_leftRationalInvariant (hl : IsRationalLeviSubgroup l)
    (lam : ComplexCharacterParameter F P) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) (hK.eisensteinSeries φ lam) := by
  intro d hd x
  let q : rationalSubgroup F G := ⟨d, hd⟩
  let H := parabolicRationalSubgroup F p
  let e := (LeftCosetSpace.rightTranslateHomeomorph H q).toEquiv
  unfold IsIwasawaCompact.eisensteinSeries
  calc
    _ = ∑' c : ParabolicRationalCosets F p, hK.eisensteinTerm φ lam x (e c) := by
      apply tsum_congr
      intro c
      have hc : Quotient.mk (QuotientGroup.rightRel H) (c.out * q) = e c := by
        change LeftCosetSpace.rightTranslate H q (LeftCosetSpace.mk H c.out) =
          LeftCosetSpace.rightTranslate H q c
        exact congrArg (LeftCosetSpace.rightTranslate H q) (Quotient.out_eq c)
      rw [hK.eisensteinTerm_eq_of_representative hφ hl hU lam x (e c) (c.out * q) hc]
      simp only [IsIwasawaCompact.eisensteinTerm, Subgroup.coe_mul, mul_assoc, q]
    _ = _ := e.tsum_eq _

variable (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)

include hφ hU hG in
/-- The full holomorphy domain of a pointwise continuation has left rational invariance.
No shrinkage of that domain depending on the adelic argument is needed. -/
theorem eisensteinContinuation_leftRationalInvariant
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ x, IsMeromorphicInCoordinatesOn (fun lam => E lam x) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {lam : ComplexCharacterParameter F P} (hlam : lam ∈ D) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) (E lam) := by
  intro d hd x
  obtain ⟨R, hR⟩ := hreg
  apply r.eqOn_of_regularParameter hA hT hG (hE (d * x)) (hE x) R _ ⟨hlam, hlam⟩
  intro lam' hlam'
  rw [hR lam' hlam']
  exact eisensteinSeries_leftRationalInvariant hK hφ hU r.isCompatible.levi lam' d hd x

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] in
/-- A finite packet is left-rational-invariant once each continuation is invariant on the
parts of parameter space where its coefficient is nonzero. This step does not require
Bochner integrability; it identifies the pointwise integrands by equality. -/
theorem packetIntegral_leftRationalInvariant {X : Type*} [MeasurableSpace X] (m : Measure X)
    {J : Type*} [Fintype J] {D : Set (ComplexCharacterParameter F P)}
    (e : X → ComplexCharacterParameter F P) (c : J → X → ℂ)
    (E : J → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (hsupp : ∀ j x, c j x ≠ 0 → e x ∈ D)
    (hE : ∀ j lam, lam ∈ D → IsLeftInvariantUnder F G (rationalSubgroup F G) (E j lam)) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) (fun g => ∫ x, ∑ j, c j x * E j (e x) g ∂m) := by
  intro d hd g
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : c j x = 0
  · simp only [hc, zero_mul]
  · rw [hE j _ (hsupp j x hc) d hd g]

end Langlands.Global

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Left rational invariance of every regular value of a pointwise meromorphic continuation of
an Eisenstein series that matches the defining series in the sufficiently regular chamber. -/
def EisensteinContinuationRationalInvarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (φ : AdelicGroupPoints F G → ℂ),
      IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ →
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
        ∀ lam ∈ D, IsLeftInvariantUnder F G (rationalSubgroup F G) (E lam)

theorem eisensteinContinuationRationalInvariance :
    EisensteinContinuationRationalInvarianceStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK φ hφ E D hE hreg lam hlam
  exact eisensteinContinuation_leftRationalInvariant hK hφ hU r hA hT hG hE hreg hlam

end Langlands.Global
