# The norm criterion for regular elliptic elements

The module `Langlands.BaseChange.EllipticNormCriterionStatement` states, as the proposition
`EllipticNormCriterionStatement.{u, v}`, that a regular elliptic element of `GL_n(F)` is a norm
from `GL_n(E)` exactly when its determinant is a norm from `Eˣ`. Here `F` is a nonarchimedean
local field of characteristic zero and `E` a cyclic `F`-algebra. The statement is **not** proved
here.

## Notation (Library and Mathlib)

- `GeneralLinear n F` is `GL_n(F)`, `GeneralLinear.determinant : GeneralLinear n F →* Fˣ` the
  determinant.
- `IsRegularElliptic γ` (module `Langlands.JacquetLanglands.RegularElliptic`): the
  characteristic polynomial of `γ` is separable and irreducible over `F`.
- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`): `E` is a finite reduced
  `F`-algebra of dimension `l`, `σ : E ≃ₐ[F] E` has order `l`, and the elements fixed by `σ`
  are those of `F`. This is Henniart–Lemaire's notion of a cyclic algebra (HL I.2.1); it
  includes cyclic field extensions and products `E₁ × ⋯ × E₁` of copies of one.
- `IsNorm σ l γ` (module `Langlands.BaseChange.Norm`): there is `δ ∈ GL_n(E)` with
  `N(δ) = δ · σ(δ) ⋯ σ^{l-1}(δ)` conjugate in `GL_n(E)` to the image of `γ` (HL I.1.2).
- `Algebra.norm F : E →* F` is Mathlib's algebra norm, `Units.map` its restriction to units,
  and `MonoidHom.range` the image.

## Statement

`EllipticNormCriterionStatement.{u, v}` quantifies over a field `F : Type u` with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`, a
commutative `F`-algebra `E : Type v`, `σ : E ≃ₐ[F] E`, `l n : ℕ` with `IsCyclicAlgebra σ l`,
and `γ : GeneralLinear n F` with `IsRegularElliptic γ`. It asserts

`IsNorm σ l γ ↔ GeneralLinear.determinant γ ∈ (Units.map (Algebra.norm F : E →* F)).range`.

No topology on `E` is needed.

## Sources

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Chapter 1, Lemma 1.4, printed p. 8, with its proof on
  pp. 8–9: if `E/F` is a cyclic extension of local fields and `u ∈ G(F)` is elliptic regular,
  then `u` is a norm if and only if `det u ∈ N_{E/F} E^×`. The proof uses local class field
  theory: with `F₁ = F[u]`, `u` is a norm iff it is a norm from `F₁ ⊗_F E`, and the
  compatibility of the reciprocity maps with the norm `N_{F₁/F}` reduces this to `det u`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. I.1.2, printed p. 6 (norm map and association), and
  I.2.1, printed pp. 10–11 (cyclic algebras: `E ≅ E₁^d` for a cyclic field extension `E₁/F` of degree `l/d`).

## Derived content

Arthur–Clozel state the lemma for a cyclic field extension. The statement here is made for every
cyclic `F`-algebra, as the base change argument needs it at places that do not stay inert. For
`E = E₁^d` with `σ` permuting the factors cyclically, `γ` is a norm from `GL_n(E)` iff it is a
norm from `GL_n(E₁)` for the generator `σ^d` restricted to `E₁` (HL I.2.1), and the algebra
norm `E → F` is the norm of `E₁/F` on each factor, so both sides of the equivalence reduce to
the field case. For `E = F^l` (split case) every element of `GL_n(F)` is a norm and the norm
`F^l → F` is onto, so the equivalence holds trivially.

The left-to-right direction holds for every `γ`: if `N(δ)` is conjugate to `γ`, then
`det γ = det N(δ) = N_{E/F}(det δ)`. Only the converse needs ellipticity.

The hypothesis `[CharZero F]` matches the characteristic-zero setting of Arthur–Clozel. The
statement does not assert anything for `γ` that is not regular elliptic.

## Use

In the proof of the restricted supercuspidal descent statement (B5r,
`RestrictedCyclicWeakBaseChangeSupercuspidalStatement`), the test
function at the σ-elliptic place on the `F` side is chosen supported on regular elliptic
elements whose determinant lies in `N_{E/F} E^×`. The criterion shows that these elements are
norms, so such a function vanishes off norms and has concordant partners on the `E` side.
