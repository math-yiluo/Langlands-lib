import Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement

/-!
# Pseudo-coefficients of the discrete series of `GL_n(F)` normalized on determinant slices

For a nonarchimedean local field `F` and a character `χ` of the centre `Z` of `GL_n(F)`, a
function `f` on `GL_n(F)` is *normalized on determinant slices* for `χ` when the central
units act on `f` through `χ⁻¹` and `f` vanishes on `Z · G¹` outside `G¹`, where
`G¹ = {g : |det g| = 1}`. The cut-off of a pseudo-coefficient with fixed central character to
the determinant slice `0 ≤ v(det g) < n`, described in the Markdown of
`CuspidalPseudoCoefficientExistenceStatement`, has this form.

`DeterminantSlicePseudoCoefficientExistenceStatement` asserts the existence of an elliptic
pseudo-coefficient of an irreducible square-integrable representation that is normalized on
determinant slices: clauses (a), (b) and (d) of
`CuspidalPseudoCoefficientExistenceStatement` together with the normalization. Statement only;
not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands

universe u uV

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Normalization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- `f` is normalized on determinant slices for the central character `χ`:

* every central element `z` with `|det z| = 1` acts through `χ⁻¹`: `f (z g) = χ(z)⁻¹ f(g)`;
* if `f g ≠ 0` and some central translate `z g` has `|det (z g)| = 1`, then `|det g| = 1`;
  that is, `f` vanishes on `Z · G¹` outside `G¹ = {g : |det g| = 1}`.

Here `|det g|` is `JacquetLanglands.determinantNorm F n g`. -/
def IsDeterminantSliceNormalized (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (f : GeneralLinear n F → ℂ) : Prop :=
  (∀ z : Subgroup.center (GeneralLinear n F), determinantNorm F n z = 1 →
      ∀ g : GeneralLinear n F, f (z * g) = (χ z : ℂ)⁻¹ * f g) ∧
    ∀ (z : Subgroup.center (GeneralLinear n F)) (g : GeneralLinear n F), f g ≠ 0 →
      determinantNorm F n (z * g) = 1 → determinantNorm F n g = 1

end Normalization

/-- Existence of elliptic pseudo-coefficients normalized on determinant slices (Kazhdan 1986,
Theorem K; Henniart–Lemaire 2011, II.5.13, II.5.14, Proposition 2, II.4.10, Lemme 1,
and II.6.7, for `E = F` and `σ = 1`). Let `F` be a nonarchimedean local field of
characteristic zero and `0 < n`, with `GL_n(F)` carrying its Borel σ-algebra. Let `π` be an
irreducible admissible square-integrable representation of `GL_n(F)` on a complex vector space
`V`, with central character `χ`, and let `μ` be a Haar measure on `GL_n(F)`. Then there is
`f ∈ C^∞_c(GL_n(F))` such that

* (a) `f` is a pseudo-coefficient of `π` with central character `χ`;
* (b) for every standard block shape `B` with at least two blocks and every irreducible
  admissible representation `Ξ` of the Levi product of `B` (carrier in the universe of `V`),
  if the unnormalized smooth induction of `Ξ` from the standard upper block parabolic
  subgroup is admissible, its character vanishes at `f`;
* (n) `f` is normalized on determinant slices for `χ` (`IsDeterminantSliceNormalized`);
* (d) there is a neighbourhood `U` of `1` such that, at every regular elliptic `γ ∈ U`, the
  orbital integral of `f` is nonzero for every right Haar measure on the centralizer of `γ`
  and every compatible quotient measure. -/
def DeterminantSlicePseudoCoefficientExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    0 < n →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V)
      (hπ : IsAdmissible π), π.IsIrreducible → IsSquareIntegrable π →
      ∀ χ : Subgroup.center (GeneralLinear n F) →* ℂˣ, HasCentralCharacterRep π χ →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
      ∃ f : SchwartzBruhat (GeneralLinear n F),
        -- (a) `f` is a pseudo-coefficient of `π`
        IsPseudoCoefficient μ χ π hπ f ∧
        -- (b) the characters of properly induced representations vanish at `f`
        (∀ B : BlockShape n, 2 ≤ B.length →
          ∀ (X : Type uV) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi F) X),
            IsAdmissible Ξ → Ξ.IsIrreducible →
            ∀ h : IsAdmissible
                (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))),
              Character.distribution μ
                (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))) h f =
                0) ∧
        -- (n) normalization on determinant slices
        IsDeterminantSliceNormalized χ ⇑f ∧
        -- (d) nonvanishing at the regular elliptic elements near `1`
        ∃ U ∈ nhds (1 : GeneralLinear n F), ∀ γ ∈ U, IsRegularElliptic γ →
          ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
            (νγ : Measure (LeftQuotient (glCentralizer γ))),
            IsCompatible (glCentralizer γ) μ μγ νγ → orbitalIntegral γ νγ ⇑f ≠ 0

end Langlands.BaseChange
