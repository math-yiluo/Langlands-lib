import Langlands.Representation.Families.RenardFamilyJacquetAdmissibilityStatement
import Langlands.Representation.Exponents.GeneralizedJacquetReduction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.LeviJacquetContragredientDynamic
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Renard VI.9.5 reduced to the generalized Jacquet lemma of VI.9.1

The finite generation of the compact-open fixed modules of the family Jacquet module
follows from the generalized Jacquet lemma `GeneralizedJacquetLemmaStatement`, applied to
the underlying complex representation of the family. The comparison of the actual
parabolic with a dynamic one uses the published proofs `parabolicDynamic` and
`dynamicGeometricUnipotentRadical`. The generalized Jacquet lemma remains a premise; a
corollary derives the same conclusion from the uniform stabilization Proposition of VI.9.1.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

universe u' uB' uV' uG uB uV

namespace Langlands.Renard.AlgebraicFamily

section Abstract

variable {Γ : Type uG} [Group Γ]
variable {B : Type uB} [CommRing B] [Algebra ℂ B]
variable {V : Type uV} [AddCommGroup V] [Module B V]

open Langlands.Jacquet Langlands.Jacquet.CoefficientRestriction

/-- If the quotient map of the underlying complex representation sends `K`-fixed vectors
onto the `K ∩ M`-fixed coinvariants, so does the quotient map of the family over `B`: the
two relation submodules have the same elements. -/
theorem fixedJacquetMap_surjective_of_complexRepresentation [Module ℂ V]
    [IsScalarTower ℂ B V] (ρ : Representation B Γ V) (N M : Subgroup Γ)
    (hMN : M ≤ Subgroup.normalizer N) (K : Subgroup Γ)
    (h : Function.Surjective (fixedJacquetMap (complexRepresentation ρ) N M hMN K)) :
    Function.Surjective (fixedJacquetMap ρ N M hMN K) := by
  intro y
  obtain ⟨v, hv⟩ := Jacquet.mk_surjective ρ N (y : Coinvariants ρ N)
  have hy : Jacquet.mk (complexRepresentation ρ) N v ∈
      fixedVectors (action (complexRepresentation ρ) N M hMN) (K.comap M.subtype) := by
    intro m
    apply (coinvariantsEquiv ρ N).injective
    change coinvariantsEquiv ρ N (action (complexRepresentation ρ) N M hMN m.val
        (Jacquet.mk (complexRepresentation ρ) N v)) =
      coinvariantsEquiv ρ N (Jacquet.mk (complexRepresentation ρ) N v)
    rw [coinvariantsEquiv_action, CoefficientRestriction.coinvariantsEquiv_mk, hv]
    exact y.property m
  obtain ⟨w, hw⟩ := h ⟨_, hy⟩
  refine ⟨⟨w.val, w.property⟩, Subtype.ext ?_⟩
  have hw' := congrArg (coinvariantsEquiv ρ N) (congrArg Subtype.val hw)
  simp only [fixedJacquetMap_apply, CoefficientRestriction.coinvariantsEquiv_mk] at hw'
  rw [fixedJacquetMap_apply, hw', hv]

/-- Surjectivity of the fixed-vector quotient map transfers along equal subgroups. -/
theorem fixedJacquetMap_surjective_congr {R : Type uB} [CommRing R] [Module R V]
    (ρ : Representation R Γ V) {N N' M M' : Subgroup Γ} (hN : N' = N) (hM : M' = M)
    (hMN : M ≤ Subgroup.normalizer N) (hMN' : M' ≤ Subgroup.normalizer N') (K : Subgroup Γ)
    (h : Function.Surjective (fixedJacquetMap ρ N M hMN K)) :
    Function.Surjective (fixedJacquetMap ρ N' M' hMN' K) := by
  subst hN hM
  exact h

end Abstract

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- The conditional reduction of VI.9.5 to the generalized Jacquet lemma of VI.9.1, at the
field universe `u'` and the carrier universe `uV'`. -/
def JacquetAdmissibleReductionStatement : Prop :=
  RationalPointFamily.GeneralizedJacquetLemmaStatement.{u', uV'} →
    JacquetAdmissibleStatement.{u', uB', uV'}

/-- **Renard VI.9.5 from VI.9.1.** The generalized Jacquet lemma for every smooth complex
representation implies that the family Jacquet module of an admissible `(G(F), B)`-module
has finitely generated compact-open fixed modules. The generalized Jacquet lemma is a
premise; the parabolic comparison inputs are discharged by published proofs. -/
theorem jacquetAdmissible_of_generalizedJacquetLemma :
    JacquetAdmissibleReductionStatement.{u', uB', uV'} := by
  intro hGJL k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro B _ _ _ _ _ V _ _ ρ hρ _ hfin K' hK'
  -- The actual parabolic and Levi are dynamic for one cocharacter.
  obtain ⟨χ, hP, hM⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
    parabolicDynamic dynamicGeometricUnipotentRadical hG hp hl
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hP hr
  have hL : pointImage (l ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) hM
  obtain ⟨g, hcomm, hBasis⟩ :=
    RationalPointFamily.dynamic_exists_central_hasOppositeIwahoriContractionBasis hG χ
  -- Notation for the literal radical and Levi images.
  have hUc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hsd := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let e := leviPointsEquiv p l hp hl
  let ψ := jacquetCharacter B (pointImage (r ≫ p)) (pointImage (l ≫ p)) hUc
    hsd.levi_le_normalizer
  -- An open subgroup of the Levi image on which `K'` is visible and `ψ` is trivial.
  let L : OpenSubgroup (pointImage (l ≫ p)) :=
    K'.comap e.symm.toMonoidHom e.symm.continuous ⊓ ⟨ψ.toMonoidHom.ker, ψ.isOpen_ker⟩
  obtain ⟨W, hW, hWL⟩ := isOpen_induced_iff.mp L.isOpen
  have h1 : (1 : rationalPoints G) ∈ W := by
    have : (1 : pointImage (l ≫ p)) ∈ (Subtype.val : pointImage (l ≫ p) → _) ⁻¹' W := by
      rw [hWL]
      exact L.one_mem
    exact this
  obtain ⟨K, hK, hKW, hKg, -⟩ := hBasis W hW h1
  have hKL : K.toSubgroup.comap (pointImage (l ≫ p)).subtype ≤ L.toSubgroup := by
    intro m hm
    change m ∈ (L : Set (pointImage (l ≫ p)))
    rw [← hWL]
    exact hKW hm
  -- The generalized Jacquet lemma for the underlying complex representation.
  let : Module ℂ V := Module.compHom V (algebraMap ℂ B)
  have : IsScalarTower ℂ B V := ⟨fun c b v => by
    change (c • b) • v = algebraMap ℂ B c • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsurjC := hGJL k G hG χ K hK g hcomm hKg V
    (Jacquet.CoefficientRestriction.complexRepresentation ρ) hρ
  have hsurj := fixedJacquetMap_surjective_congr ρ hN hL _
    hsd.levi_le_normalizer K.toSubgroup
    (fixedJacquetMap_surjective_of_complexRepresentation ρ _ _ _ K.toSubgroup hsurjC)
  -- The image of the finitely generated `K`-fixed module contains the `K'`-fixed module.
  have := hfin K hK
  let f : fixedVectors ρ K.toSubgroup →ₗ[B] Jacquet ρ (pointImage (r ≫ p)) :=
    (Jacquet.Localization.mk ρ (pointImage (r ≫ p)) 1).comp
      (fixedVectors ρ K.toSubgroup).subtype
  have hle : fixedVectors (leviJacquetRepresentation p l r hp hr hl hmul ρ) K'.toSubgroup ≤
      LinearMap.range f := by
    intro x hx
    -- `x` is fixed by the unnormalized action of `K ∩ M`.
    have hxM : ∀ m : pointImage (l ≫ p), (m : rationalPoints G) ∈ K →
        Jacquet.Localization.action ρ (pointImage (r ≫ p)) 1 (pointImage (l ≫ p))
          hsd.levi_le_normalizer
          (Jacquet.Localization.isInvariant_one _ _ hsd.levi_le_normalizer) m x = x := by
      intro m hmK
      have hmL := hKL hmK
      have hm1 : e.symm m ∈ K' := hmL.1
      have hm2 : ψ.toMonoidHom m = 1 := hmL.2
      have hfix := hx ⟨e.symm m, hm1⟩
      change jacquetRepresentation ρ (pointImage (r ≫ p)) (pointImage (l ≫ p)) hUc
        hsd.levi_le_normalizer (e (e.symm m)) x = x at hfix
      rw [show e (e.symm m) = m from e.apply_symm_apply m] at hfix
      change (ψ.toMonoidHom m : B) • _ = x at hfix
      rwa [hm2, Units.val_one, one_smul] at hfix
    let y := Jacquet.Localization.trivialEquiv ρ (pointImage (r ≫ p)) (pointImage (l ≫ p))
      hsd.levi_le_normalizer x
    have key : ∀ (m : pointImage (l ≫ p)) (z : Jacquet ρ (pointImage (r ≫ p))),
        Jacquet.action ρ _ _ hsd.levi_le_normalizer m
            (Jacquet.Localization.trivialEquiv ρ _ _ hsd.levi_le_normalizer z) =
          Jacquet.Localization.trivialEquiv ρ _ _ hsd.levi_le_normalizer
            (Jacquet.Localization.action ρ (pointImage (r ≫ p)) 1 (pointImage (l ≫ p))
              hsd.levi_le_normalizer
              (Jacquet.Localization.isInvariant_one _ _ hsd.levi_le_normalizer) m z) := by
      intro m z
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ (pointImage (r ≫ p)) 1 z
      rfl
    have hy : y ∈ fixedVectors (Jacquet.action ρ (pointImage (r ≫ p)) (pointImage (l ≫ p))
        hsd.levi_le_normalizer) (K.toSubgroup.comap (pointImage (l ≫ p)).subtype) := by
      intro m
      change Jacquet.action ρ _ _ hsd.levi_le_normalizer m.val
        (Jacquet.Localization.trivialEquiv ρ _ _ hsd.levi_le_normalizer x) = y
      rw [key, hxM m.val m.property]
    obtain ⟨w, hw⟩ := hsurj ⟨y, hy⟩
    refine ⟨w, ?_⟩
    apply (Jacquet.Localization.trivialEquiv ρ (pointImage (r ≫ p)) (pointImage (l ≫ p))
      hsd.levi_le_normalizer).toLinearEquiv.injective
    exact congrArg Subtype.val hw
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- The same conclusion from the uniform stabilization Proposition of VI.9.1, through the
published deduction `generalizedJacquetLemma_of_uniformCompressionStabilization`. -/
theorem jacquetAdmissible_of_uniformCompressionStabilization
    (hstable : RationalPointFamily.UniformCompressionStabilizationStatement.{u', uV'}) :
    JacquetAdmissibleStatement.{u', uB', uV'} :=
  jacquetAdmissible_of_generalizedJacquetLemma
    (RationalPointFamily.generalizedJacquetLemma_of_uniformCompressionStabilization hstable)

end Langlands.Renard.AlgebraicFamily
