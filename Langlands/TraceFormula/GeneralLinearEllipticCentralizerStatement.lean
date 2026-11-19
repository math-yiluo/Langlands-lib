import Langlands.TraceFormula.TwistedOrbital
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-!
# Centralizers of rational `GL_n` elements that are regular elliptic at a finite place

Let `F` be a number field, `G = GL_n` as a group scheme over `F`, `G(𝔸_F)¹` the Library's
norm-one subgroup of `G(𝔸_F)`, and `Γ` the image of `G(F)` in it. Let `γ ∈ Γ` be regular
elliptic at one finite place `v` (mathematically, its characteristic polynomial is then
irreducible and separable over `F` and `E = F[γ]` is a field of degree `n` over `F`). Let `C` be
the centralizer of `γ` in `G(𝔸_F)¹`. For every right-invariant measure on `C` that is finite on
compact sets and positive on open sets, and all compatible quotient measures on
`C \ G(𝔸_F)¹` and on `(Γ ∩ C) \ C`, the statement asserts:

* the quotient `(Γ ∩ C) \ C` has finite volume;
* for every compactly supported continuous `φ` on `G(𝔸_F)¹`, the orbit function
  `x ↦ φ(x⁻¹ γ x)` on `C \ G(𝔸_F)¹` is integrable.

(Why: `C ≅ 𝔸_E¹`, `Γ ∩ C ≅ E^×`, and the conjugacy class of `γ` is closed; these facts are
explained in the paired Markdown and are not part of the statement.)

These are the two analytic facts about the geometric side of the simple trace formula used for
each class in `GeneralLinearSimpleTraceFormulaStatement`.

Source: Getz–Hahn 2024, §18.4 (printed p. 485), where an element `γ ∈ G(F)` is called
elliptic when `A_G C_γ(F) \ C_γ(𝔸_F)` has finite volume, and Theorem 18.2.5 (printed p. 479),
which requires closed orbits; see `GeneralLinearEllipticCentralizerStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme
open Langlands.QuotientIntegration Langlands.JacquetLanglands

namespace Langlands.TraceFormula

local instance generalLinearEllipticCentralizerIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearEllipticCentralizerSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- Centralizers of rational `GL_n` elements that are regular elliptic at a finite place.
Let `F` be a number field, `v` a finite place of `F`, and `r` a rational point of the
norm-one subgroup `GL_n(𝔸_F)¹` whose component at `v` is regular elliptic. Let `C` be the
centralizer of `r` in `GL_n(𝔸_F)¹` and `Γ` the rational subgroup of `GL_n(𝔸_F)¹`. For every
right-invariant measure `μC` on `C` that is finite on compact sets and positive on open sets
(for Borel measurable structures on both quotients), every quotient measure `νC` on `C \ GL_n(𝔸_F)¹`
compatible with the Haar measure of `GL_n(𝔸_F)¹` and `μC`, and every quotient measure `νΓC` on
`(Γ ∩ C) \ C` compatible with `μC` and counting measure, the volume `νΓC(univ)` is finite and,
for every compactly supported continuous `φ` on `GL_n(𝔸_F)¹`, the orbit function
`x ↦ φ(x⁻¹ r x)` on `C \ GL_n(𝔸_F)¹` is `νC`-integrable. -/
def GeneralLinearEllipticCentralizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (v : Langlands.Global.FinitePlace F)
    (r : rationalNormOneSubgroup F GLₙ),
    IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
        ((r : normOneSubgroup F GLₙ) : AdelicGroupPoints F GLₙ)))) →
    ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer
          (MonoidHom.id (normOneSubgroup F GLₙ)) (r : normOneSubgroup F GLₙ)))]
      [BorelSpace (LeftQuotient (twistedCentralizer
          (MonoidHom.id (normOneSubgroup F GLₙ)) (r : normOneSubgroup F GLₙ)))]
      [MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r : normOneSubgroup F GLₙ))))]
      [BorelSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r : normOneSubgroup F GLₙ))))]
      (μC : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
          (r : normOneSubgroup F GLₙ)))
      [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (νC : Measure (LeftQuotient (twistedCentralizer
          (MonoidHom.id (normOneSubgroup F GLₙ)) (r : normOneSubgroup F GLₙ))))
      (νΓC : Measure (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r : normOneSubgroup F GLₙ))))),
      Langlands.QuotientIntegration.IsCompatible
        (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) (r : normOneSubgroup F GLₙ))
        (Measure.haar : Measure (normOneSubgroup F GLₙ)) μC νC →
      Langlands.QuotientIntegration.IsCompatible
        ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r : normOneSubgroup F GLₙ)))
        μC Measure.count νΓC →
      νΓC Set.univ ≠ ⊤ ∧
      ∀ φ : normOneSubgroup F GLₙ → ℂ, Continuous φ → HasCompactSupport φ →
        Integrable (twistedOrbitFunction (MonoidHom.id (normOneSubgroup F GLₙ))
          (r : normOneSubgroup F GLₙ) φ) νC

end Langlands.TraceFormula
