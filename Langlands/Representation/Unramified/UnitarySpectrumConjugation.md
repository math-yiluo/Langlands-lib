# Spherical spectra of unitarizable representations are closed under `α ↦ conj(α)⁻¹`

Author: Worker 3657.

Lean module: `Langlands.Representation.Unramified.UnitarySpectrumConjugation`,
namespace `Langlands.Unramified` (and `Langlands.Unramified.PairedHecke` for the
local Hecke computations). It imports
`Langlands.Representation.Unramified.PairedHeckeScalars` and
`Langlands.Representation.Unitary.Basic`, and changes no published file. It is a
helper for the proof task of
`Langlands.Global.CuspidalPairAbsoluteConvergenceReductionStatement` (Task 6822).
That proof uses it for the self-pair `π × π̃`, whose coefficients are
`tr(A ^ n) tr(Ã ^ n) = |tr(A ^ n)|²`.

## Main theorem

```lean
theorem Langlands.Unramified.conjSpectrum_eq_map_inv_of_hasSphericalHeckeSpectrum
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (hU : IsUnitarizable A.obj.representation) {s : Eigenvalues (r + 1)}
    (hs : HasSphericalHeckeSpectrum F A s) :
    conjSpectrum s = s.map fun z => z⁻¹
```

Let `A` be an object of `GL_(r+1)(F)` over a p-adic field `F`. Suppose it has an
invariant positive definite Hermitian form (`IsUnitarizable`, Library
`Langlands/Representation/Unitary/Basic.lean`). Suppose also that it has
spherical Hecke spectrum `s` (`HasSphericalHeckeSpectrum`, Library
`HeckeOperators.lean`): its spherical vectors are nonzero, and the standard
double-coset operators act on them by the standard Hecke scalars of `s`. Then
the complex conjugate multiset of `s` is the inverse multiset.

## Other declarations

- `conjSpectrum s`: the multiset `s` with every parameter replaced by its
  complex conjugate (`Units.map (starRingEnd ℂ)`). `coe_conjSpectrum` describes
  its underlying multiset.
- `powerTrace_conjSpectrum`: `tr((conj s) ^ k) = conj (tr(s ^ k))`.
- `eulerPolynomial_conjSpectrum`: the Euler polynomial of `conj s` is the
  coefficientwise conjugate of that of `s`.
- `standardHeckeScalar_conjSpectrum`: the standard Hecke scalars of `conj s`
  are the conjugates of those of `s`. The normalization `q ^ (i(r+1-i)/2)` and
  the signs are real.
- `PairedHecke.formRight b a`: the linear functional `y ↦ ⟪a, y⟫` of an
  invariant positive form `b`.
- `PairedHecke.conj_standardHeckeElement`: the standard Hecke elements are
  indicator functions, so they take real values.
- `PairedHecke.scalar_conj_adjoint` (**Hermitian adjointness**). Let `a ≠ 0`
  be a spherical vector of a smooth representation `ρ` with an invariant
  positive form, and an eigenvector of the standard Hecke elements with
  scalars `l`. Then `conj (l j) = conj (l n) * l (n - j)`, where `n = r + 1`.
- `PairedHecke.conjSpectrum_eq_map_inv_of_form`: in the situation of
  `scalar_conj_adjoint` with `l` the standard Hecke scalars of `s`, one has
  `conj s = s⁻¹`.

## Proof

The proof of `scalar_conj_adjoint` follows the Library's
`PairedHecke.scalar_adjoint` step by step. That proof shows `λ'_j = λ'_n λ_(n-j)`
for spherical eigenvectors `a`, `b` of `ρ`, `σ`, paired nontrivially by an
invariant bilinear form `B`. Here `σ = ρ`, `b = a`, and `B` is replaced by the
Hermitian form `⟪·,·⟫`. Let `c(g) = ⟪a, ρ(g) a⟫`.

1. `c` is bi-invariant under the spherical subgroup `K`. Invariance of the form
   moves `ρ(k₁)` from the second argument to the first, where it fixes `a`.
2. The central element `t = diag(ϖ, …, ϖ)` acts on `a` by `l n`
   (`corner_last`), so `c(g) = conj(l n) c(t g)`. The scalar comes out of the
   conjugate-linear first argument.
3. `conj(l j) ⟪a, a⟫ = ∫ e_j(g) c(g⁻¹) dg`. By the published
   `functional_corner` applied to `y ↦ ⟪a, y⟫`, one has
   `l j ⟪a, a⟫ = ∫ e_j(g) ⟪a, ρ(g) a⟫ dg`. Take complex conjugates
   (`integral_conj`). The values of `e_j` are real, `⟪a, a⟫` is real, and
   `conj ⟪a, ρ(g) a⟫ = ⟪ρ(g) a, a⟫ = ⟪a, ρ(g⁻¹) a⟫` by invariance.
4. `∫ e_(n-j)(g) c(g) dg = l(n-j) ⟪a, a⟫`, by `functional_corner` again.
5. The comparison of the two integrals is the one in `scalar_adjoint`. It uses
   the inverse transpose `θ` (which preserves `sphericalHaar`), the relation
   `e_j(g⁻¹) = e_(n-j)(t g)` (`standardHeckeElement_inv`), and left invariance
   of the Haar measure. It gives
   `conj(l j) ⟪a, a⟫ = conj(l n) l(n-j) ⟪a, a⟫`, and `⟪a, a⟫ ≠ 0` by
   definiteness.

For `conjSpectrum_eq_map_inv_of_form`, the scalars of `conj s` are the
conjugates of those of `s`. So step 5 is the hypothesis of the published
`eq_map_inv_of_standardHeckeScalar` for the pair `s`, `conj s`, which gives
`conj s = s⁻¹`. The main theorem takes a nonzero spherical vector from
`HasSphericalHeckeSpectrum`.

## Sources and provenance

This is an internal derivation of a standard fact. A unitary representation is
isomorphic to the complex conjugate of its contragredient. So for unitary
unramified `π` the class of `π̃`, which is `A⁻¹`, equals the conjugate class
`conj(A)`. Jacquet–Shalika use it in the proof of Theorem (5.3) of *On Euler
products and the classification of automorphic representations I* (Amer. J.
Math. 103, 1981; registered as
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`),
p.556 (PDF 58). There the coefficients of (5.3.3) for `π' = π̃` are
`|T(v^n)|² ≥ 0`. The statement Markdown of the consumer,
`Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceStatement.md`, §6
item 2, records the fact in the form `A_v⁻¹ = conj(A_v)`.

The proof does not construct the conjugate representation. It adapts the
Library's Hecke-adjointness argument for contragredients,
`Langlands/Representation/Unramified/PairedHeckeScalars.lean` (whose Markdown
gives Henniart 2000, §2.2, as provenance), from an invariant bilinear pairing
to an invariant Hermitian form.

## What is not asserted

- Any bound on the parameters. Unitarity alone does not give
  `|α| ≤ q^(1/2)`; that needs genericity (Jacquet–Shalika I, Corollary (2.5)).
- Anything for ramified representations, or the converse implication.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiles
the module with no errors or warnings. The main theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.
