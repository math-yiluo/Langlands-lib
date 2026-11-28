import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicSelfWeylParameters
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.Global.AdelicWeylParameterEquivalence

/-! # Finite Weyl data and estimates along a regular truncation ray -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis

section Weyl

variable {F : Type} [Field F] [NumberField F]
  {G P P' M M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {p' : P' ⟶ G} {l : M ⟶ P} {l' : M' ⟶ P'} {a : A.toGrp ⟶ M}

/-- When the two parabolics are associate, a fixed reverse Weyl map injects the
parameter set into the finite set of self-Weyl maps. -/
theorem finite_weylParameterSet (r : ParabolicRootPresentation p l a)
    (hl' : IsRationalLeviSubgroup l') {π : P ⟶ M} (hπ : l ≫ π = 𝟙 M)
    {π' : P' ⟶ M'} (hπ' : l' ≫ π' = 𝟙 M') :
    (weylParameterSet p l p' l' π').Finite := by
  let S := weylParameterSet p l p' l' π'
  rcases Set.eq_empty_or_nonempty S with hS | ⟨s, hs⟩
  · change S.Finite
    rw [hS]
    exact Set.finite_empty
  · obtain ⟨w₀, c₀, hw₀, _⟩ := hs
    obtain ⟨c₁, hw₁, _, _⟩ := hw₀.exists_symm
    let : IsIso c₁ := hw₁.isIso
    obtain ⟨e, he⟩ := exists_weylParameter_linearEquiv l' l hl' r.isCompatible.levi c₁ π hπ
    have hself := (finite_weylParameterSet_self r π).to_subtype
    let W : S → weylParameterSet p l p l π := fun x =>
      ⟨e.toLinearMap.comp x.val, he.symm ▸ comp_mem_weylParameterSet_left hw₁ hπ' x.property⟩
    have hinj : Function.Injective W := by
      intro x y h
      apply Subtype.ext
      apply LinearMap.ext
      intro lam
      have heq : e.toLinearMap.comp x.val = e.toLinearMap.comp y.val := congrArg Subtype.val h
      exact e.injective (LinearMap.congr_fun heq lam)
    let : Finite S := Finite.of_injective W hinj
    exact Set.toFinite S

/-- The Weyl parameter set between two presented Levis with retractions admits a finite
enumeration by actual Weyl conjugations. -/
def WavePacketWeylEnumerationStatement : Prop :=
  ∀ {F : Type} [Field F] [NumberField F]
    {G P P' M M' : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ G} {p' : P' ⟶ G} {l : M ⟶ P} {l' : M' ⟶ P'} {a : A.toGrp ⟶ M}
    (_r : ParabolicRootPresentation p l a), IsRationalLeviSubgroup l' →
    ∀ {π : P ⟶ M}, l ≫ π = 𝟙 M → ∀ {π' : P' ⟶ M'}, l' ≫ π' = 𝟙 M' →
    ∃ (k : ℕ) (w : Fin k → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (c : Fin k → (M' ⟶ M)),
      (∀ j, IsWeylConjugation p l p' l' (w j) (c j)) ∧
      Function.Injective (fun j => weylParameter l (c j) π') ∧
      ∀ σ ∈ weylParameterSet p l p' l' π', ∃ j, weylParameter l (c j) π' = σ

/-- Choose a Weyl representative for each map in the finite parameter set. -/
theorem exists_weylParameterEnumeration : WavePacketWeylEnumerationStatement := by
  classical
  intro F _ _ G P P' M M' _ _ A p p' l l' a r hl' π hπ π' hπ'
  let S := weylParameterSet p l p' l' π'
  let : Finite S := (finite_weylParameterSet r hl' hπ hπ').to_subtype
  let : Fintype S := Fintype.ofFinite S
  let e := (Fintype.equivFin S).symm
  choose w c hW hc using fun s : S => s.property
  refine ⟨Fintype.card S, w ∘ e, c ∘ e, fun j => hW (e j), ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext ((hc (e i)).symm.trans (hij.trans (hc (e j))))
  · intro σ hσ
    obtain ⟨j, hj⟩ := e.surjective ⟨σ, hσ⟩
    exact ⟨j, (hc (e j)).trans (congrArg Subtype.val hj)⟩

end Weyl

section Forms

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} (iU : U ⟶ P) (l : M ⟶ P)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Zero is permitted as a padding vector in every square-integrable inducing space. -/
theorem zero_isSquareIntegrableInducedForm {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l 0 := by
  refine ⟨zero_isAutomorphicFunctionOn F G hsmooth hcalc _ _ rho, ?_, ?_⟩
  · intro a _ g
    simp
  · exact (integrable_zero (K × RestrictionSplitCentre.CanonicalQuotient F M) ℝ _).congr
      (Eventually.of_forall fun _ => by simp)

end Forms

/-- Exponential errors in the ray parameter tend to zero on the natural-number ray. -/
theorem tendsto_truncationRayError (B δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun j : ℕ => B * Real.exp (-(δ * (j : ℝ)))) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)
  simpa only [mul_zero, Function.comp_apply] using h.const_mul B

end Langlands.Global
