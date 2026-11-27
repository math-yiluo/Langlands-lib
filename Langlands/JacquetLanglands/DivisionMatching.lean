import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.OrbitalIntegral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Matching of test functions between `GL_n(F)` and the units of a central division algebra

Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*
(1984), introduction and B.2.a, B.2.c 1) (printed pp. 33–36 and 83), and Badulescu (2002),
§5 (printed p. 733) and §6, Annexe (printed pp. 745–746).

For a field `F`, `n : ℕ` and a central division algebra `D` over `F`:

* `IsDivisionRegularSupported F D f'`: `f' : Dˣ → ℂ` vanishes off the regular units;
* `divisionCentralizer γ'`: the centralizer of `γ' : Dˣ`, as the twisted centralizer of the
  identity twist, so that its coset space is the domain of the quotient measure in
  `orbitalIntegral γ' ν f'`;
* `IsDivisionAssociatedMeasure γ γ' μγ μγ'`: the measures `μγ` on the centralizer of `γ` in
  `GL_n(F)` and `μγ'` on the centralizer of `γ'` in `Dˣ` correspond under an isomorphism of
  topological groups sending `γ` to `γ'`;
* `OrbitalIntegralsVanishOffElliptic μ f`: the orbital integrals of `f` vanish at the regular semisimple
  elements that are not regular elliptic;
* `MatchAt μ μ' f f' γ γ'` and `AreMatching μ μ' f f'`: matching of orbital integrals, modelled
  on `Langlands.BaseChange.ConcordAt` and `Langlands.BaseChange.AreConcordant` for the identity
  twist; quotient measures enter only through `QuotientIntegration.IsCompatible`.

The lemmas show that an elliptic-supported `f` vanishes off the elliptic set, so that for such
`f` matching is the equality of orbital integrals at corresponding pairs, and that the image of
a right Haar measure under an isomorphism of topological groups sending `γ` to `γ'` is a right
Haar measure associated with it. No measure is chosen or normalized inside a definition.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.TraceFormula
open Langlands.BaseChange (glCentralizer IsEllipticSupported OrbitalIntegralsVanishOffElliptic)

attribute [local instance high] Langlands.BaseChange.leftQuotientMeasurableSpace
attribute [local instance] Langlands.BaseChange.leftQuotient_borelSpace

universe u uG uH

section Support

variable (F : Type u) [Field F] (D : Type u) [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

/-- `f' : Dˣ → ℂ` is supported in the regular set of `Dˣ`: every `g'` with `f' g' ≠ 0` is
regular (its reduced characteristic polynomial is separable). -/
def IsDivisionRegularSupported (f' : Dˣ → ℂ) : Prop :=
  ∀ g' : Dˣ, f' g' ≠ 0 → IsRegular F D g'

variable {F D}

theorem isDivisionRegularSupported_zero : IsDivisionRegularSupported F D (0 : Dˣ → ℂ) :=
  fun _ hg => absurd rfl hg

theorem IsDivisionRegularSupported.add {f g : Dˣ → ℂ} (hf : IsDivisionRegularSupported F D f)
    (hg : IsDivisionRegularSupported F D g) : IsDivisionRegularSupported F D (f + g) := by
  intro x hx
  by_cases h : f x = 0
  · refine hg x fun h' => hx ?_
    rw [Pi.add_apply, h, h', add_zero]
  · exact hf x h

theorem IsDivisionRegularSupported.const_mul {f : Dˣ → ℂ} (hf : IsDivisionRegularSupported F D f)
    (c : ℂ) : IsDivisionRegularSupported F D fun x => c * f x :=
  fun x hx => hf x (right_ne_zero_of_mul hx)

end Support

section Centralizers

/-- Every element lies in its own centralizer. -/
theorem self_mem_twistedCentralizer_id {G : Type uG} [Group G] (g : G) :
    g ∈ twistedCentralizer (MonoidHom.id G) g := by
  rw [mem_twistedCentralizer, MonoidHom.id_apply, inv_mul_cancel, one_mul]

/-- `γ` lies in its centralizer `glCentralizer γ`. -/
theorem self_mem_glCentralizer {F : Type u} [Field F] {n : ℕ} (γ : GeneralLinear n F) :
    γ ∈ glCentralizer γ :=
  self_mem_twistedCentralizer_id γ

/-- The centralizer `{x ∈ Dˣ | x⁻¹ γ' x = γ'}` of `γ'` in the unit group of a division ring,
stated as the twisted centralizer for the identity twist, so that its coset space is the domain
of the quotient measure in `orbitalIntegral γ' ν f'`. -/
abbrev divisionCentralizer {D : Type u} [DivisionRing D] (γ' : Dˣ) : Subgroup Dˣ :=
  twistedCentralizer (MonoidHom.id Dˣ) γ'

/-- `divisionCentralizer γ'` is the ordinary centralizer of `γ'`. -/
theorem divisionCentralizer_eq_centralizer {D : Type u} [DivisionRing D] (γ' : Dˣ) :
    divisionCentralizer γ' = Subgroup.centralizer {γ'} :=
  twistedCentralizer_id γ'

/-- `γ'` lies in its centralizer `divisionCentralizer γ'`. -/
theorem self_mem_divisionCentralizer {D : Type u} [DivisionRing D] (γ' : Dˣ) :
    γ' ∈ divisionCentralizer γ' :=
  self_mem_twistedCentralizer_id γ'

end Centralizers

section Associated

variable {F : Type u} [Field F] [TopologicalSpace F] {n : ℕ}
  {D : Type u} [DivisionRing D] [TopologicalSpace D]
  [MeasurableSpace (GeneralLinear n F)] [MeasurableSpace Dˣ]

/-- Associated measures on the centralizers of `γ : GL_n(F)` and `γ' : Dˣ` (Badulescu 2002,
§6, printed p. 746; DKV, B.2.a): some isomorphism of topological groups `φ` from the
centralizer of `γ` in `GL_n(F)` onto the centralizer of `γ'` in `Dˣ` sends `γ` to `γ'` and
carries `μγ` to `μγ'` (`Measure.map`). The definition is stated for arbitrary topologies.
When `F` is a nonarchimedean local field, `D` a central division algebra over `F` of dimension
`n ^ 2`, both carry their finite-dimensional `F`-module topologies, and `μγ`, `μγ'` are Borel
Haar measures, then for corresponding `γ` and `γ'` it is equivalent to transport by the
isomorphism induced by the `F`-algebra isomorphism `F[γ] ≃ F[γ']` with `γ ↦ γ'` (see the
paired Markdown). The equivalence fails for other topologies: for `F = D = ℝ`, `n = 1`,
`γ = γ' = 1`, the continuous automorphism `x ↦ x ^ 3` of `ℝˣ` fixes `1` and maps the Haar
measure `dx / |x|` to a third of itself. -/
def IsDivisionAssociatedMeasure (γ : GeneralLinear n F) (γ' : Dˣ)
    (μγ : Measure (glCentralizer γ)) (μγ' : Measure (divisionCentralizer γ')) : Prop :=
  ∃ φ : glCentralizer γ ≃ₜ* divisionCentralizer γ',
    ((φ ⟨γ, self_mem_glCentralizer γ⟩ : divisionCentralizer γ') : Dˣ) = γ' ∧
      Measure.map φ μγ = μγ'

/-- The image of a measure under an isomorphism of topological groups sending `γ` to `γ'` is
associated with it. -/
theorem isDivisionAssociatedMeasure_map {γ : GeneralLinear n F} {γ' : Dˣ}
    (φ : glCentralizer γ ≃ₜ* divisionCentralizer γ')
    (hφ : ((φ ⟨γ, self_mem_glCentralizer γ⟩ : divisionCentralizer γ') : Dˣ) = γ')
    (μγ : Measure (glCentralizer γ)) :
    IsDivisionAssociatedMeasure γ γ' μγ (Measure.map φ μγ) :=
  ⟨φ, hφ, rfl⟩

end Associated

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
  [IsTopologicalGroup H]

/-- The image of a right invariant measure under an isomorphism of topological groups is right
invariant. -/
theorem isMulRightInvariant_map_continuousMulEquiv (φ : G ≃ₜ* H) (μ : Measure G)
    [μ.IsMulRightInvariant] : (Measure.map φ μ).IsMulRightInvariant := by
  have hφ : Measurable φ := φ.continuous.measurable
  refine ⟨fun h => ?_⟩
  rw [Measure.map_map (measurable_mul_const h) hφ]
  obtain ⟨g, rfl⟩ := φ.surjective h
  conv_rhs => rw [← map_mul_right_eq_self μ g]
  rw [Measure.map_map hφ (measurable_mul_const g)]
  congr 1
  funext y
  simp only [Function.comp_apply, map_mul]

end Transport

section AssociatedHaar

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {D : Type u} [DivisionRing D] [TopologicalSpace D] [IsTopologicalRing D]
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace Dˣ] [BorelSpace Dˣ]

/-- Given an isomorphism of topological groups `φ` between the centralizers sending `γ` to
`γ'`, every right Haar measure `μγ` on the centralizer of `γ` has an associated right Haar
measure on the centralizer of `γ'`, namely its image under `φ`. -/
theorem exists_isDivisionAssociatedMeasure {γ : GeneralLinear n F} {γ' : Dˣ}
    (φ : glCentralizer γ ≃ₜ* divisionCentralizer γ')
    (hφ : ((φ ⟨γ, self_mem_glCentralizer γ⟩ : divisionCentralizer γ') : Dˣ) = γ')
    (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant] :
    ∃ μγ' : Measure (divisionCentralizer γ'), μγ'.IsHaarMeasure ∧ μγ'.IsMulRightInvariant ∧
      IsDivisionAssociatedMeasure γ γ' μγ μγ' :=
  ⟨Measure.map φ μγ, inferInstance, isMulRightInvariant_map_continuousMulEquiv φ μγ,
    isDivisionAssociatedMeasure_map φ hφ μγ⟩

end AssociatedHaar

section Conjugation

variable {F : Type u} [Field F] {n : ℕ}

/-- Conjugation does not change the characteristic polynomial. -/
theorem charpoly_conj (x γ : GeneralLinear n F) :
    ((x⁻¹ * γ * x : GeneralLinear n F) : Matrix (Fin n) (Fin n) F).charpoly =
      (γ : Matrix (Fin n) (Fin n) F).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

/-- Regular ellipticity is invariant under conjugation. -/
theorem isRegularElliptic_conj_iff (x γ : GeneralLinear n F) :
    IsRegularElliptic (x⁻¹ * γ * x) ↔ IsRegularElliptic γ := by
  unfold IsRegularElliptic IsRegularSemisimple
  rw [charpoly_conj]

end Conjugation

section Matching

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

/-- A function supported in the regular elliptic set vanishes on the conjugacy class of every
element that is not regular elliptic, so its orbital integrals vanish there. -/
theorem vanishesOffElliptic_of_isEllipticSupported {f : GeneralLinear n F → ℂ}
    (hf : IsEllipticSupported f) (μ : Measure (GeneralLinear n F)) : OrbitalIntegralsVanishOffElliptic μ f := by
  intro γ _ hγ μγ _ _ νγ _
  have h0 : twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ f = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [twistedOrbitFunction_mk, MonoidHom.id_apply, Pi.zero_apply]
      by_contra hx
      exact hγ ((isRegularElliptic_conj_iff x γ).1 (hf _ hx))
  simp only [orbitalIntegral, twistedOrbitalIntegral, h0, Pi.zero_apply, integral_zero]

variable {D : Type u} [DivisionRing D] [TopologicalSpace D] [IsTopologicalRing D]
variable [MeasurableSpace Dˣ] [BorelSpace Dˣ]

/-- `f` and `f'` match at the pair `(γ, γ')`, for the measures `μ` on `GL_n(F)` and `μ'` on
`Dˣ`: for all right Haar measures `μγ` on `glCentralizer γ` and `μγ'` on
`divisionCentralizer γ'` that are associated, and all quotient measures `νγ`, `νγ'` compatible
with `μ / μγ` and `μ' / μγ'`, the orbital integral of `f` at `γ` equals that of `f'` at `γ'`. -/
def MatchAt (μ : Measure (GeneralLinear n F)) (μ' : Measure Dˣ) (f : GeneralLinear n F → ℂ)
    (f' : Dˣ → ℂ) (γ : GeneralLinear n F) (γ' : Dˣ) : Prop :=
  ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    (μγ' : Measure (divisionCentralizer γ')) [μγ'.IsHaarMeasure] [μγ'.IsMulRightInvariant]
    (νγ : Measure (LeftQuotient (glCentralizer γ)))
    (νγ' : Measure (LeftQuotient (divisionCentralizer γ'))),
    IsCompatible (glCentralizer γ) μ μγ νγ →
    IsCompatible (divisionCentralizer γ') μ' μγ' νγ' →
    IsDivisionAssociatedMeasure γ γ' μγ μγ' →
    orbitalIntegral γ νγ f = orbitalIntegral γ' νγ' f'

variable [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]

/-- `f : GL_n(F) → ℂ` and `f' : Dˣ → ℂ` match, for the measures `μ` on `GL_n(F)` and `μ'` on
`Dˣ` (DKV, B.2.a and B.2.c 1); Badulescu 2002, §5, printed p. 733): the orbital integrals of `f`
vanish at the regular semisimple elements that are not regular elliptic, and `f` and `f'` match
at every pair `(γ, γ')` of corresponding elements. No sign is built in. -/
def AreMatching (μ : Measure (GeneralLinear n F)) (μ' : Measure Dˣ) (f : GeneralLinear n F → ℂ)
    (f' : Dˣ → ℂ) : Prop :=
  OrbitalIntegralsVanishOffElliptic μ f ∧
    ∀ (γ : GeneralLinear n F) (γ' : Dˣ), Corresponds F D γ γ' → MatchAt μ μ' f f' γ γ'

/-- For `f` supported in the regular elliptic set, matching is the equality of orbital integrals
at every pair of corresponding elements. -/
theorem areMatching_iff_of_isEllipticSupported {μ : Measure (GeneralLinear n F)}
    {μ' : Measure Dˣ} {f : GeneralLinear n F → ℂ} {f' : Dˣ → ℂ} (hf : IsEllipticSupported f) :
    AreMatching μ μ' f f' ↔
      ∀ (γ : GeneralLinear n F) (γ' : Dˣ), Corresponds F D γ γ' → MatchAt μ μ' f f' γ γ' :=
  ⟨fun h => h.2, fun h => ⟨vanishesOffElliptic_of_isEllipticSupported hf μ, h⟩⟩

end Matching

end Langlands.JacquetLanglands
