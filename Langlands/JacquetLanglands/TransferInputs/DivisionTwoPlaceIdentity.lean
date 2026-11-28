import Langlands.JacquetLanglands.Relation
import Langlands.Representation.Classification.ConstituentRelations

/-!
# The two-place character identity from the global comparison

`DivisionTwoPlaceIdentityStatement` packages the local output of Deligne–Kazhdan–Vignéras
(§B.1.a–g) for a division algebra of degree `n > 1`. Globalization prescribes `B` at the
first ramified place and the trivial representation at the second, after a unitary twist
at the first place if needed. Comparing simple trace formulas and fixing the full component
outside those two places leads to a character identity on the ramified product. The split
side is the product of two irreducible square-integrable characters. The division side is a
finite sum of products of irreducible characters with positive integer multiplicities,
including the term `B ⊗ 1` after undoing the twist. In degree one the groups on each side
identify via the units of their fields, giving a direct singleton identity.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

open Langlands.Classification

/-- The two-place character identity from Deligne–Kazhdan–Vignéras (§B.1.a–g, characteristic
zero). Let `F` be a nonarchimedean local field of characteristic zero, `D` a finite-dimensional
central division algebra over `F` with its module topology and `n` with
`Module.finrank F D = n ^ 2`, and let `B` be an irreducible admissible smooth representation of
`Dˣ` (carrier in `Type uW`) on which `Fˣ` acts through a character of absolute value one.

Then there are a second nonarchimedean local field `F₂` of characteristic zero with a
finite-dimensional central division algebra `D₂` over `F₂` of dimension `n ^ 2` (both in
`Type`), and:

* irreducible smooth representations `π₁` of `GL_n(F)` (carrier in `Type uV`) and `π₂` of
  `GL_n(F₂)`, both square-integrable modulo the centre;
* a finite family `τ q`, `q ∈ Q`, of pairwise inequivalent irreducible admissible
  representations of `Dˣ` (carriers in `Type uW`) and, for each `q`, a finite family `σ q k`,
  `k ∈ K q`, of pairwise inequivalent irreducible admissible representations of `D₂ˣ`, with
  multiplicities `m q k ≥ 1`;
* indices `q₀` and `k₀` with `τ q₀` equivalent to `B` and `σ q₀ k₀` equivalent to the trivial
  representation of `D₂ˣ` on `ℂ`;

such that for every regular elliptic `x ∈ GL_n(F)` corresponding to a regular `x' ∈ Dˣ` and
every regular elliptic `y ∈ GL_n(F₂)` corresponding to a regular `y' ∈ D₂ˣ`, the characters
satisfy
`Θ_{π₁}(x) Θ_{π₂}(y) = ∑ q, Θ_{τ q}(x') ∑ k, m q k Θ_{σ q k}(y')`. -/
def DivisionTwoPlaceIdentityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    ∀ B : SmoothRep.{0, u, uW} ℂ Dˣ, B.representation.IsIrreducible →
      IsAdmissible B.representation →
      (∃ ω : Fˣ →* ℂˣ,
        HasScalarCharacter B.representation (Units.map (algebraMap F D : F →* D)) ω ∧
          ∀ z : Fˣ, ‖(ω z : ℂ)‖ = 1) →
      ∃ (F₂ : Type) (_ : Field F₂) (_ : ValuativeRel F₂) (_ : TopologicalSpace F₂)
        (_ : IsNonarchimedeanLocalField F₂) (_ : CharZero F₂)
        (D₂ : Type) (_ : DivisionRing D₂) (_ : Algebra F₂ D₂) (_ : FiniteDimensional F₂ D₂)
        (_ : Algebra.IsCentral F₂ D₂) (_ : TopologicalSpace D₂) (_ : IsModuleTopology F₂ D₂),
        Module.finrank F₂ D₂ = n ^ 2 ∧
        haveI := generalLinear_t2Space F n
        haveI := generalLinear_locallyCompactSpace F n
        haveI := generalLinear_totallyDisconnectedSpace F n
        haveI := units_isTopologicalGroup F D
        haveI := units_t2Space F D
        haveI := units_locallyCompactSpace F D
        haveI := units_totallyDisconnectedSpace F D
        haveI := generalLinear_t2Space F₂ n
        haveI := generalLinear_locallyCompactSpace F₂ n
        haveI := generalLinear_totallyDisconnectedSpace F₂ n
        haveI := units_isTopologicalGroup F₂ D₂
        haveI := units_t2Space F₂ D₂
        haveI := units_locallyCompactSpace F₂ D₂
        haveI := units_totallyDisconnectedSpace F₂ D₂
        ∃ (π₁ : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F))
          (π₂ : SmoothRep.{0, 0, 0} ℂ (GeneralLinear n F₂))
          (h₁ : IsSquareIntegrable π₁.representation) (h₂ : IsSquareIntegrable π₂.representation)
          (Q : Type) (_ : Fintype Q) (τ : Q → SmoothRep.{0, u, uW} ℂ Dˣ)
          (hτ : ∀ q, IsAdmissible (τ q).representation)
          (K : Q → Type) (_ : ∀ q, Fintype (K q)) (σ : (q : Q) → K q → SmoothRep.{0, 0, 0} ℂ D₂ˣ)
          (hσ : ∀ q k, IsAdmissible (σ q k).representation) (m : (q : Q) → K q → ℕ)
          (q₀ : Q) (k₀ : K q₀),
          π₁.representation.IsIrreducible ∧ π₂.representation.IsIrreducible ∧
          (∀ q, (τ q).representation.IsIrreducible) ∧
          (∀ q k, (σ q k).representation.IsIrreducible) ∧
          Pairwise (fun q q' => ¬ Nonempty ((τ q).representation.Equiv (τ q').representation)) ∧
          (∀ q, Pairwise (fun k k' =>
            ¬ Nonempty ((σ q k).representation.Equiv (σ q k').representation))) ∧
          (∀ q k, 0 < m q k) ∧
          Nonempty ((τ q₀).representation.Equiv B.representation) ∧
          Nonempty ((σ q₀ k₀).representation.Equiv (Representation.trivial ℂ D₂ˣ ℂ)) ∧
          ∀ (x : GeneralLinear n F) (x' : Dˣ) (y : GeneralLinear n F₂) (y' : D₂ˣ),
            Corresponds F D x x' → Corresponds F₂ D₂ y y' →
            ∃ (a b : ℂ) (c : Q → ℂ) (d : (q : Q) → K q → ℂ),
              HasCharacterValue π₁.representation h₁.isAdmissible x a ∧
              HasCharacterValue π₂.representation h₂.isAdmissible y b ∧
              (∀ q, HasCharacterValue (τ q).representation (hτ q) x' (c q)) ∧
              (∀ q k, HasCharacterValue (σ q k).representation (hσ q k) y' (d q k)) ∧
              a * b = ∑ q, c q * ∑ k, (m q k : ℂ) * d q k

end Langlands.JacquetLanglands
