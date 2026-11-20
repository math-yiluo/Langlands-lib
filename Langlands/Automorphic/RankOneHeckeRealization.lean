import Langlands.Automorphic.ComplexPlaceParameterHeckeTwist
import Langlands.Automorphic.ConstantSpectralPresentation
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Representation.RankinSelberg.HighlyRamified.PairInductionGenericity

/-!
# The automorphic `GL(1)` realization of a Hecke character

For a Hecke character `χ` of a number field `F`, the twist by `χ ∘ det` of the actual constant
rank-one cusp line is an actual irreducible cuspidal realization of `GL_1(𝔸_F)`, with the
twisted constant spectral presentation. This module proves that the constant line has the
trivial standard-module parameter at every complex place, so that the twist has the
parameter of `χ` there, and computes the Euler polynomials of the twisted presentation.
-/

noncomputable section

universe u uP

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.RankOneHecke

open Langlands.Global Langlands.LocalFactor.Archimedean Langlands.Archimedean NumberField

/-! ## The standard module of the trivial character on `GL_1(ℂ)` -/

/-- A matrix of `GL_1(ℂ)` is the diagonal matrix of its determinant. -/
theorem diagonalUnits_determinant (g : Langlands.GeneralLinear 1 ℂ) :
    (GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin 1 => GeneralLinear.determinant g) :
      Langlands.GeneralLinear 1 ℂ) = g := by
  apply Units.ext
  rw [GeneralLinear.Iwasawa.diagonalUnits_val]
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  rw [Matrix.diagonal_apply_eq]
  change (g : Matrix (Fin 1) (Fin 1) ℂ).det = _
  exact Matrix.det_fin_one _

/-- The principal-series character of the single trivial block is trivial. -/
theorem principalSeriesCharacter_trivial (a : Fin 1 → ℂˣ) :
    principalSeriesCharacter ℂ 1 (complexPositionCharacter [ComplexCharacterData.trivial]) a =
      1 := by
  simp [principalSeriesCharacter, complexPositionCharacter, ComplexCharacterData.trivial]

/-- Every function of the standard module of the trivial block on `GL_1(ℂ)` is constant. -/
theorem eq_of_mem_trivialStandardModule {f : Langlands.GeneralLinear 1 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 1 [ComplexCharacterData.trivial])
    (g : Langlands.GeneralLinear 1 ℂ) : f g = f 1 := by
  have h := hf.2 (fun _ => GeneralLinear.determinant g) 1 1
  rw [OneMemClass.coe_one, mul_one, mul_one, diagonalUnits_determinant,
    principalSeriesCharacter_trivial, one_mul] at h
  exact h

end Langlands.Automorphic.RankOneHecke

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean Langlands.Archimedean NumberField
open Langlands.Automorphic.RankOneHecke

variable {F : Type u} [Field F] [NumberField F]

local instance rankOneHeckeRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance rankOneHeckeContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance rankOneHeckeSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance rankOneHeckeFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance rankOneHeckeStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ConstantFunctions

local instance rankOneHeckeSpaceGroup : AddCommGroup (realization F 1).Space :=
  Submodule.addCommGroup _

/-- The constant line of `GL_1` has the trivial standard-module parameter at every complex
place: evaluation at `1` identifies the (constant) functions of the standard module of the
trivial block with the constants. -/
theorem realization_one_hasComplexPlaceParameter
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}) :
    (realization F 1).HasComplexPlaceParameter v [ComplexCharacterData.trivial] := by
  refine ⟨rfl, (scalarEquiv F 1).toLinearMap ∘ₗ
    kFiniteEval (complexStandardModule 1 [ComplexCharacterData.trivial]) 1, ?_, ?_, ?_⟩
  · intro f₁ f₂ h
    have h' : (f₁ : Langlands.GeneralLinear 1 ℂ → ℂ) 1 = (f₂ : Langlands.GeneralLinear 1 ℂ → ℂ) 1 :=
      (scalarEquiv F 1).injective h
    apply Subtype.ext
    funext g
    rw [eq_of_mem_trivialStandardModule f₁.2.1 g, eq_of_mem_trivialStandardModule f₂.2.1 g, h']
  · intro k f
    refine ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule 1 _ f.2 k.2, ?_⟩
    have h1 : (f : Langlands.GeneralLinear 1 ℂ → ℂ) (1 * (k : Langlands.GeneralLinear 1 ℂ)) =
        (f : Langlands.GeneralLinear 1 ℂ → ℂ) 1 :=
      eq_of_mem_trivialStandardModule f.2.1 _
    exact (congrArg (scalarEquiv F 1) h1).trans (compactRepresentation_scalarEquiv F 1 _ _).symm
  · intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule 1 _ f.2 X, ?_⟩
    have hconst : (f : Langlands.GeneralLinear 1 ℂ → ℂ) =
        fun _ => (f : Langlands.GeneralLinear 1 ℂ → ℂ) 1 :=
      funext (eq_of_mem_trivialStandardModule f.2.1)
    have hzero : rightDerivative (matrixModel ℂ 1) X (f : Langlands.GeneralLinear 1 ℂ → ℂ) 1 =
        0 := by
      rw [hconst]
      simp only [rightDerivative, mfderiv_const]
      rfl
    have h2 : rightDerivative (matrixModel ℂ 1) X (f : Langlands.GeneralLinear 1 ℂ → ℂ) 1 =
        ArchimedeanGL.augmentation F 1 (ArchimedeanGL.envelopingGenerator F 1
          (ArchimedeanGL.complexPlaceComplexLieInclusion F 1 v (1 ⊗ₜ X))) *
            (f : Langlands.GeneralLinear 1 ℂ → ℂ) 1 := by
      rw [ArchimedeanGL.augmentation_envelopingGenerator, zero_mul]
      exact hzero
    exact (congrArg (scalarEquiv F 1) h2).trans (envelopingAction_scalarEquiv F 1 _ _).symm

end ConstantFunctions

namespace RankOneHecke

open Langlands.Unramified

/-- The trivial block is a unit for the product of character data. -/
theorem trivial_mul (d : ComplexCharacterData) : ComplexCharacterData.trivial.mul d = d :=
  Langlands.Automorphic.Unramified.ComplexCharacterDataLemmas.ext
    (ContinuousMonoidHom.ext fun z =>
      show (1 : ℂˣ) * d.character z = d.character z from one_mul _)
    (zero_add _) (zero_add _)

variable [CompactSpace (AdeleQuotient F)]

/-- The automorphic `GL(1)` realization of the Hecke character `χ`: the actual constant cusp
line multiplied by `χ ∘ det`. -/
def cuspidal (χ : HeckeCharacter F) : CuspidalOperatorRealization F 0 :=
  (ConstantFunctions.rankOneCuspidal F).heckeDeterminantTwist χ

/-- The twisted constant spectral presentation of `cuspidal χ`. -/
def presentation (χ : HeckeCharacter F) : CuspidalSpectralPresentation.{u, uP} (cuspidal χ) :=
  (ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).heckeDeterminantTwist χ

/-- If `χ` has the parameter `d` at the complex place `v`, then `cuspidal χ` has the
one-block parameter `[d]` there. -/
theorem cuspidal_hasComplexPlaceParameter {χ : HeckeCharacter F}
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {d : ComplexCharacterData} (hχ : χ.HasComplexPlaceParameter v d) :
    (cuspidal χ).isoClass.HasComplexPlaceParameter v [d] := by
  have h := CuspidalOperatorRealization.hasComplexPlaceParameter_heckeDeterminantTwist_mul
    (ConstantFunctions.rankOneCuspidal F)
    ((CuspidalOperatorRealization.isoClass_hasComplexPlaceParameter _ v _).mpr
      (ConstantFunctions.realization_one_hasComplexPlaceParameter v)) hχ
  simpa only [List.map_cons, List.map_nil, trivial_mul, cuspidal] using h

/-- At a place outside the exceptional set, the Euler polynomial of the presentation of
`cuspidal χ` is `1 - χ_v(ϖ_v) X`. -/
theorem presentation_eulerPolynomial (χ : HeckeCharacter F) (v : Langlands.Global.FinitePlace F)
    (hv : v ∉ (presentation.{u, uP} χ).spectralSystem.exceptional) :
    (presentation.{u, uP} χ).spectralSystem.eulerPolynomial v hv =
      1 - Polynomial.C (χ.finiteUniformizerValue v : ℂ) * Polynomial.X := by
  change ((ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).heckeDeterminantTwist
    χ).spectralSystem.eulerPolynomial v hv = _
  rw [CuspidalSpectralPresentation.heckeDeterminantTwist_eulerPolynomial]
  change (Eigenvalues.eulerPolynomial rankOneTrivialSpectrum).comp _ = _
  rw [rankOneTrivialSpectrum_eulerPolynomial, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_comp]

end RankOneHecke

namespace LocalRealization

variable {v : Langlands.Global.FinitePlace F}

/-- Every irreducible admissible local realization of `GL_1` is supercuspidal: `GL_1` has no
proper block parabolic. -/
theorem isSupercuspidal_rankOne (S : LocalRealization F (0 + 1) v) (hI : S.IsIrreducible)
    (hA : S.IsAdmissible) : S.IsSupercuspidal :=
  ⟨hI, hA, ⟨Quotient.mk _ ⟨(S.padicObject hI hA).obj, (S.padicObject hI hA).property.1, by
    letI : TopologicalSpace (CompletionPadic.padicField v).Carrier :=
      (CompletionPadic.padicField v).canonicalTopologicalData.topology
    exact Langlands.RankinSelberg.HighlyRamified.isSupercuspidal_rankOne
      (S.padicObject hI hA).property.2⟩, rfl⟩⟩

end LocalRealization

namespace RankOneHecke

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 1600000 in
/-- Every local component of the twisted constant presentation is supercuspidal. -/
theorem presentation_localComponent_isSupercuspidal (χ : HeckeCharacter F)
    (v : Langlands.Global.FinitePlace F) :
    ((presentation.{u, uP} χ).localComponent v).IsSupercuspidal := by
  have hI0 : ((ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).localComponent v).IsIrreducible :=
    ((ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).presentation.localComponent_isIrreducible_iff
      (ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).finiteSlice.nonzero v).mpr
        (ConstantFunctions.tensorLocalModel_isIrreducible F 1 v)
  have hA0 : ((ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).localComponent v).IsAdmissible :=
    ((ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).presentation.localComponent_isAdmissible_iff
      (ConstantFunctions.rankOneSpectralPresentation.{u, uP} F).finiteSlice.nonzero v).mpr
        (ConstantFunctions.tensorLocalModel_isAdmissible F 1 v)
  exact LocalRealization.isSupercuspidal_rankOne _
    ((CuspidalSpectralPresentation.heckeDeterminantTwist_localComponent_isIrreducible_iff _ χ v).mpr hI0)
    ((CuspidalSpectralPresentation.heckeDeterminantTwist_localComponent_isAdmissible_iff _ χ v).mpr hA0)

/-- `cuspidal χ` has a supercuspidal local component at every finite place. -/
theorem cuspidal_hasSupercuspidalComponent (χ : HeckeCharacter F)
    (v : Langlands.Global.FinitePlace F) :
    (cuspidal χ).isoClass.HasSupercuspidalComponent.{u, uP} v :=
  (CuspidalOperatorRealization.IsoClass.hasSupercuspidalComponent_iff _ v).mpr
    ⟨presentation.{u, uP} χ, presentation_localComponent_isSupercuspidal χ v⟩

end RankOneHecke

end Langlands.Automorphic
