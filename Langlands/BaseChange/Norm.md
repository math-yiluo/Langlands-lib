# The norm map of cyclic base change for `GL_n`

This module `Langlands.BaseChange.Norm` (namespace `Langlands.BaseChange`) defines the
algebraic objects behind cyclic base change for `GL_n`: the entrywise action of an
automorphism `σ` on `GL_n(E)`, the norm `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}`, association of
elements of `GL_n(E)` and `GL_n(F)`, norms, σ-regular and σ-elliptic elements and cyclic
algebras. It proves four basic identities and states the norm lemma as the proposition
`CyclicNormLemmaStatement`. The norm lemma is **not** proved here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/pilot/literature/Henniart-Lemaire, Changement de base et induction automorphe pour GLn en caracteristique non nulle (2011).pdf`.
  PDF page = printed page + 8. Cited below as HL.
  - I.1.2, printed p. 6: the norm `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}`, association of `δ` and
    `γ` by `g⁻¹ N(δ) g = γ`, the identity `γ = N(g⁻¹ δ g^σ)`, regular elements.
  - I.2.1, printed pp. 10–11: cyclic `F`-algebras `E = E₁ × ⋯ × E_r` and the norm `N`.
  - I.2.2, printed pp. 11–12: σ-orbits `O_σ(δ)`, the Lemme (here
    `CyclicNormLemmaStatement`) and the Définition of associated elements.
  - I.2.3, printed pp. 13–14: regular and elliptic elements, the sets `G(F)'` and
    `G(F)''`, σ-regular elements.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, §1, Lemma 1.1
  (printed p. 3, PDF p. 17): the norm lemma for a cyclic extension of fields of
  characteristic zero, which HL I.2.2 cite and extend to cyclic algebras in any
  characteristic.

## Setting

Throughout, `GL_n(R)` is the Library's `Langlands.GeneralLinear n R`, the units of
`Matrix (Fin n) (Fin n) R`. For items 1–5 and 8–11, `F : Type u` is an arbitrary
commutative ring, `E : Type v` an arbitrary commutative `F`-algebra, `σ : E ≃ₐ[F] E` an
`F`-algebra automorphism and `l n : ℕ`; no finiteness, no field hypothesis and no
relation between `σ` and `l` is assumed. This generality lets the same definitions serve
local fields and their cyclic algebras, adele rings `F = 𝔸_F`, `E = 𝔸_E` of a cyclic
extension of global fields, and split places `E = F^l`. Items 6 and 7 and the statement
take `F` to be a field. As in HL, `δ^σ` denotes `σ` applied to every entry of `δ`, and
powers `σ^i` are taken in the group `E ≃ₐ[F] E`, where `(σ * τ) x = σ (τ x)`.

## Definitions

1. `entrywiseAut σ n : GeneralLinear n E ≃* GeneralLinear n E` is `δ ↦ δ^σ`. Its forward
   map is Mathlib's `Matrix.GeneralLinearGroup.map (σ : E →+* E)` and its inverse is the
   same construction for `σ.symm`; `entrywiseAut_toMonoidHom` records (by `rfl`) that
   the underlying monoid homomorphism is `Matrix.GeneralLinearGroup.map (σ : E →+* E)`.
   It is HL's `δ ↦ δ^σ` (I.1.2, I.2.1), and it is intended as the input automorphism of
   `GL_n(E)` for the generic twisted-conjugacy definitions of `Langlands.TraceFormula.TwistedOrbital`.
2. `baseChange F E n : GeneralLinear n F →* GeneralLinear n E` is
   `Matrix.GeneralLinearGroup.map (algebraMap F E)`, entrywise application of the
   structure map. When `algebraMap F E` is injective (for instance for a cyclic algebra
   over a field) it identifies `GL_n(F)` with a subgroup of `GL_n(E)`, which is how HL
   view `G(F)` inside `G(E)` (I.2.1, "le groupe `G(F)`, plongé diagonalement").
3. `cyclicNorm σ l δ`, for `δ : GeneralLinear n E`, is the ordered product
   `N(δ) = δ · δ^σ · δ^{σ²} ⋯ δ^{σ^{l-1}}` (HL I.1.2 and I.2.1, `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}`).
   In Lean it is the product of the list `[δ^{σ^0}, δ^{σ^1}, …, δ^{σ^{l-1}}]`, the empty
   product `1` when `l = 0`. `cyclicNorm_zero` and `cyclicNorm_succ`
   (`N_{l+1}(δ) = N_l(δ) · δ^{σ^l}`) give the recursion.
4. `IsNormAssociated σ l δ γ`, for `δ : GeneralLinear n E` and `γ : GeneralLinear n F`,
   holds when there is `g : GeneralLinear n E` with
   `g⁻¹ * cyclicNorm σ l δ * g = baseChange F E n γ`, that is, `N(δ)` is conjugate in
   `GL_n(E)` to `γ` viewed in `GL_n(E)`. This is HL's own formulation in I.1.2 (printed
   p. 6): "deux éléments `δ ∈ G(E)` et `γ ∈ G(F)` sont associés s'il existe un
   `g ∈ G(E)` tel que `g⁻¹ N(δ) g = γ`". See below for its agreement with the Définition
   of I.2.2.
5. `IsNorm σ l γ`, for `γ : GeneralLinear n F`, holds when `γ` is associated with some
   `δ : GeneralLinear n E`: HL's "`γ` est une norme de `G(E)`" (I.1.2, in the definition
   of matching functions).
6. For a field `F`:
   - `IsSigmaRegular σ l δ` holds when some `γ : GeneralLinear n F` with
     `IsNormAssociated σ l δ γ` is `IsRegularSemisimple` (the Library's
     `Langlands.JacquetLanglands.IsRegularSemisimple`: separable characteristic
     polynomial). HL I.2.3 (printed pp. 13–14) call `δ` σ-regular when the orbit
     `N(O_σ(δ))` is regular; with the Library's regularity notion this is the condition
     "`N(O_σ(δ))` is a regular semisimple orbit", which HL also use in Remarque 2 of I.2.3.
   - `IsSigmaElliptic σ l δ` is the same with the Library's `IsRegularElliptic`
     (separable and irreducible characteristic polynomial), that is, `N(O_σ(δ))` lies in
     HL's `G(F)'' = G(F)' ∩ G(F)_e` (I.2.3). HL do not name this notion; it is derived
     from their `G(F)''` exactly as σ-regularity is derived from regularity.

   These are existential ("some `γ`"). Under the norm lemma, all `γ` associated with a
   given `δ` are conjugate in `GL_n(F)` (statement (1b)), and both regularity predicates
   depend only on the characteristic polynomial, so "some `γ`" and "every `γ`" agree; this
   remark is not formalized here.
7. For a field `F`, `IsCyclicAlgebra σ l` is the conjunction of: `Module.Finite F E`;
   `Module.finrank F E = l`; `IsReduced E`; `orderOf σ = l` in the group `E ≃ₐ[F] E`; and
   every `x : E` with `σ x = x` lies in `(algebraMap F E).range`. It expresses that `E` is
   a cyclic `F`-algebra of group `Σ = ⟨σ⟩` of order `l` in the sense of HL I.2.1 (printed
   pp. 10–11); see the comparison below.

## Proved facts

The four identities:

8. `cyclicNorm_twistedConj σ l x δ`: for all `x δ : GeneralLinear n E`,
   `cyclicNorm σ l (x⁻¹ * δ * entrywiseAut σ n x) =
   x⁻¹ * cyclicNorm σ l δ * entrywiseAut (σ ^ l) n x`, i.e.
   `N(x⁻¹ δ x^σ) = x⁻¹ N(δ) x^{σ^l}`. Proof: induction on `l` using `cyclicNorm_succ`; in
   the inductive step the factors `x^{σ^l}` and `(x^{σ^l})⁻¹` cancel and
   `(x^σ)^{σ^l} = x^{σ^{l+1}}` (`entrywiseAut_mul_apply`, `pow_succ`); the `group` tactic
   closes the remaining group identity. With `σ^l = 1` this is HL's remark
   "`γ = N(g⁻¹ δ g^σ)`" in I.1.2 (printed p. 6).
9. `entrywiseAut_cyclicNorm σ l δ`:
   `entrywiseAut σ n (cyclicNorm σ l δ) =
   δ⁻¹ * cyclicNorm σ l δ * entrywiseAut (σ ^ l) n δ`, i.e.
   `N(δ)^σ = δ⁻¹ N(δ) δ^{σ^l}`. Proof: the auxiliary lemma
   `entrywiseAut_cyclicNorm_eq` (`N(δ)^σ = N(δ^σ)`, by induction on `l`, since `σ` and
   `σ^i` commute) and identity 8 with `x = δ`, because `δ⁻¹ δ δ^σ = δ^σ`. With
   `σ^l = 1` this is the identity `(Nx)^σ = x⁻¹ (Nx) x` in the proof of Arthur–Clozel,
   Lemma 1.1 (printed p. 3).
10. `entrywiseAut_baseChange σ γ`:
    `entrywiseAut σ n (baseChange F E n γ) = baseChange F E n γ`, because
    `σ (algebraMap F E a) = algebraMap F E a` for an `F`-algebra map; checked entrywise.
    It is the easy half of HL's remark in I.2.1 that `G(F)` is the subgroup of `G(E)`
    fixed by `σ`.
11. `IsNormAssociated.twistedConj hσ h x y`: if `σ ^ l = 1` and
    `IsNormAssociated σ l δ γ`, then
    `IsNormAssociated σ l (x⁻¹ * δ * entrywiseAut σ n x) (y⁻¹ * γ * y)` for all
    `x : GeneralLinear n E` and `y : GeneralLinear n F`. Proof: if
    `g⁻¹ N(δ) g = γ`, then by identity 8 and `σ^l = 1`,
    `N(x⁻¹ δ x^σ) = x⁻¹ N(δ) x`, and the element `x⁻¹ g y` (with `y` mapped by
    `baseChange`) conjugates it to `y⁻¹ γ y`, since `baseChange` is a homomorphism.
    So association descends to σ-conjugacy classes in `GL_n(E)` and conjugacy classes in
    `GL_n(F)`.

Auxiliary declarations: `entrywiseAut_apply_apply` and `baseChange_apply_apply` (entries,
`simp`), `entrywiseAut_one_apply` (`σ = 1` acts trivially), `entrywiseAut_mul_apply`
(`δ^{στ} = (δ^τ)^σ`), `cyclicNorm_zero`, `cyclicNorm_succ` and
`entrywiseAut_cyclicNorm_eq` as above, and for cyclic algebras:

- `IsCyclicAlgebra.pow_eq_one`: `IsCyclicAlgebra σ l` implies `σ ^ l = 1` (from
  `orderOf σ = l`), the hypothesis of identity 11.
- `IsCyclicAlgebra.pos`: `IsCyclicAlgebra σ l` implies `0 < l`. If `l = 0`, then
  `Module.finrank F E = 0` makes `E` trivial (`Module.finrank_zero_iff`), so `σ = 1` and
  `orderOf σ = 1 ≠ 0`. This matches HL's `l ≥ 1`.
- `isCyclicAlgebra_one`: nonvacuity check, `IsCyclicAlgebra (1 : F ≃ₐ[F] F) 1` for every
  field `F`.

For rational elements and their norms:

- `cyclicNorm_mul_baseChange σ l δ s (hs : Commute δ (baseChange F E n s)) :
  cyclicNorm σ l (δ * baseChange F E n s) = cyclicNorm σ l δ * baseChange F E n s ^ l`
  (any commutative `F`, `E`): `N(δ s_E) = N(δ) s_E^l` when `s_E` commutes with `δ`. Proof:
  induction on `l`; `s_E` is fixed by every `σ^i` (identity 10), so it commutes with every
  `δ^{σ^i}`. With `δ = 1` it gives `N(s_E) = s_E^l`.

## Rational points and regular semisimple elements over fields

For fields `K`, `L` with `[Algebra K L]` (and `F`, `E` with `[Algebra F E]`):

- `exists_baseChange_eq_of_entrywiseAut_eq {σ : L ≃ₐ[K] L}
  (hfix : ∀ a : L, σ a = a → a ∈ (algebraMap K L).range) {x : GeneralLinear n L}
  (hx : entrywiseAut σ n x = x) : ∃ y : GeneralLinear n K, baseChange K L n y = x`: an
  entrywise fixed invertible matrix is rational when the fixed scalars are. Proof: the
  entries are images of elements of `K`; the matrix of these has nonzero determinant, since
  its image is `det x`.
- `IsCyclicAlgebra.exists_baseChange_eq_of_entrywiseAut_eq (hσ : IsCyclicAlgebra σ l)
  {g : GeneralLinear n E} (hg : entrywiseAut σ n g = g) : ∃ x : GeneralLinear n F,
  baseChange F E n x = g` (`E` a field): the case of a cyclic algebra, whose last condition
  is `hfix` (the other half of HL's remark in I.2.1).
- `isRegularSemisimple_baseChange {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) :
  IsRegularSemisimple (baseChange F E n γ)`, and the same statement under the name
  `Langlands.JacquetLanglands.IsRegularSemisimple.baseChange` (for dot notation): the
  characteristic polynomial of `γ_E` is the image of that of `γ` (`Matrix.charpoly_map`),
  and the image of a separable polynomial is separable.
- `isRegularSemisimple_conj_iff (y γ : GeneralLinear n F) :
  IsRegularSemisimple (y⁻¹ * γ * y) ↔ IsRegularSemisimple γ`: conjugate matrices have the
  same characteristic polynomial (`Matrix.charpoly_units_conj`).

## Statement

12. `CyclicNormLemmaStatement.{u, v} : Prop` is HL I.2.2, Lemme (printed p. 12). For every
    field `F : Type u`, commutative `F`-algebra `E : Type v`, `σ : E ≃ₐ[F] E` and `l n : ℕ`
    with `IsCyclicAlgebra σ l`:
    - (1a) every `δ : GeneralLinear n E` is associated with some `γ : GeneralLinear n F`
      (HL (1), first sentence: some `g⁻¹ N(δ) g` lies in `G(F)`);
    - (1b) if `δ` is associated with `γ` and with `γ'`, then `y⁻¹ * γ * y = γ'` for some
      `y : GeneralLinear n F` (HL (1), second sentence: `O(g⁻¹ N(δ) g) = O(h⁻¹ N(δ) h)`);
    - (2) if `g⁻¹ * cyclicNorm σ l δ * g = cyclicNorm σ l δ'` for some
      `g : GeneralLinear n E`, then `x⁻¹ * δ * entrywiseAut σ n x = δ'` for some
      `x : GeneralLinear n E` (HL (2): `O_σ(δ) = O_σ(δ')`).

    HL state the Lemme for every `n ≥ 1`; for `n = 0` all three clauses hold trivially
    because `GL_0` is the trivial group. For a cyclic extension of fields of characteristic
    zero this is Arthur–Clozel, Lemma 1.1; HL note that the characteristic hypothesis is
    unnecessary and reduce cyclic algebras to the field factor `E₁` via I.2.1. Together
    (1a), (1b) and (2) say that the norm induces an injection from σ-conjugacy classes in
    `GL_n(E)` to conjugacy classes in `GL_n(F)`, the map written `𝒩` below.

## Comparison with the source

### Association: I.1.2 and the Définition of I.2.2

Item 4 is HL's own formulation of association in I.1.2. In I.2.2 HL define instead the
map on classes (in their notation a second `N`, written `𝒩` here)
`𝒩(O_σ(δ)) = O(g⁻¹ N(δ) g)` for any `g ∈ G(E)` with `g⁻¹ N(δ) g ∈ G(F)` (well defined by
(1a) and (1b)), and call `δ` and `γ` associated when `𝒩(O_σ(δ)) = O(γ)`. The two agree
once (1a) and (1b) hold (for instance for a cyclic algebra, granted the norm lemma):

- if `g⁻¹ N(δ) g = γ`, then `g` is an admissible choice in the definition of `𝒩`, so
  `𝒩(O_σ(δ)) = O(γ)`;
- conversely, if `𝒩(O_σ(δ)) = O(γ)`, choose by (1a) a `g` with `g⁻¹ N(δ) g = γ₀ ∈ G(F)`.
  Then `O(γ₀) = O(γ)`, so `γ = y⁻¹ γ₀ y` with `y ∈ G(F)`, and
  `(g y)⁻¹ N(δ) (g y) = γ`.

Here `G(F)` is viewed in `G(E)` through `baseChange F E n`, which is injective for a
cyclic algebra. This comparison is a paper argument; it is not formalized here.
Identity 11 is the Lean form of the fact that item 4 only depends on the σ-orbit of `δ`
and the orbit of `γ`.

### Regular elements

HL (I.1.2 and I.2.3) call `γ ∈ G(F)` *regular* when its characteristic polynomial is a
product of pairwise distinct irreducible polynomials over `F`, without asking them to be
separable; for a monic polynomial this means squarefree. Their set of regular semisimple
elements `G(F)'` consists of the regular `γ` with separable characteristic polynomial,
and `G(F)'' = G(F)' ∩ G(F)_e` with `G(F)_e` the regular elements with irreducible
characteristic polynomial. The Library's `IsRegularSemisimple` asks for a separable
characteristic polynomial, so it is HL's `G(F)'`, and `IsRegularElliptic` is HL's
`G(F)''`. A separable polynomial is always squarefree, and over a perfect field the
converse holds (Mathlib `PerfectField.separable_iff_squarefree`), so over perfect fields,
in particular in characteristic zero, HL's regular elements are exactly the regular
semisimple ones. The project's base fields are number fields and p-adic fields, which
have characteristic zero. Over imperfect fields, such as local fields of positive
characteristic, HL's regular elements form a larger set, and `IsSigmaRegular` is the
corresponding smaller notion "`N(O_σ(δ))` is regular semisimple". As required, this module uses the Library's notions and defines no
second notion of regular or elliptic element.

### Cyclic algebras

HL I.2.1 fix `l ≥ 1`, a cyclic group `Σ` of order `l` with generator `σ`, and a cyclic
`F`-algebra `E` of group `Σ`: `E = E₁ × ⋯ × E_r` with `r ∣ l`, `l = r l₁`, each `E_i` a
cyclic field extension of `F` whose Galois group is generated by `τ = σ^r`, with
`σ E₁ = E_r` and `σ E_{i+1} = E_i`; then `F`, embedded diagonally, is the subring of
elements fixed by `σ`. The following paper argument (not formalized here) shows that
`IsCyclicAlgebra σ l` describes exactly these algebras.

- *HL's algebras satisfy item 7.* `E` is finite over `F` of dimension `r l₁ = l`, being
  `r` copies of the degree-`l₁` extension `E₁`; it is reduced, as a product of fields.
  HL identify `E` with `E₁^r` so that `σ(x₁, …, x_r) = (x₂, …, x_r, τx₁)`. Hence
  `σ^k = 1` exactly when `r ∣ k` and `τ^{k/r} = 1` on `E₁`, so `σ` has order `r l₁ = l`;
  and the `σ`-fixed elements are the `(x, …, x)` with `τx = x`, that is, the elements
  of `F` embedded diagonally, as HL state.
- *Item 7 gives HL's algebras.* A finite-dimensional reduced commutative `F`-algebra is a
  finite product of finite field extensions `E₁ × ⋯ × E_s`, indexed by its primitive
  idempotents, which `σ` permutes. The sum `e` of the idempotents in one `σ`-orbit is
  fixed by `σ`, hence `e = algebraMap F E c` for some `c ∈ F`. As `l ≥ 1`
  (`IsCyclicAlgebra.pos`), `E ≠ 0` and `algebraMap F E` is injective, so `c` is a nonzero
  idempotent of the field `F` and `e = 1`. So there is one orbit: `s = r` and, after
  renumbering, `σ E₁ = E_r` and `σ E_{i+1} = E_i`. Then `τ = σ^r`
  preserves each factor, and HL's identification `E ≅ E₁^r` above applies, with
  `σ(x₁, …, x_r) = (x₂, …, x_r, τx₁)`. The `σ`-fixed elements are the `(x, …, x)` with
  `τx = x`, so the fixed field of `τ` on `E₁` is `F`. The group generated by `τ` on `E₁`
  is finite (`σ` has finite order), so by Artin's theorem `E₁/F` is Galois with cyclic
  group generated by `τ`, and so are the other factors, which are isomorphic to `E₁`
  under powers of `σ`. Finally `l = dim_F E = r [E₁ : F]`, so `r ∣ l`. (Given the other
  conditions, `orderOf σ = l` is in fact automatic; it is kept to fix the order of `Σ`
  explicitly.)

Examples: a cyclic Galois field extension `E/F` of degree `l` with `σ` a generator of
`Gal(E/F)` (`r = 1`); and `E = F^l` with the cyclic shift
`σ(x₁, …, x_l) = (x₂, …, x_l, x₁)` (`r = l`, `E₁ = F`, `τ = 1`), the case of a place that
splits completely. In Lean only the degenerate example `isCyclicAlgebra_one`
(`E = F`, `σ = 1`, `l = 1`) is checked.

## Scope

- Twisted conjugacy classes, twisted centralizers and (twisted) orbital integrals are
  not defined here; they belong to the generic twisted-conjugacy definitions of
  `Langlands.TraceFormula.TwistedOrbital`, which take `entrywiseAut σ n` as input. σ-conjugacy appears only as
  the explicit expression `x⁻¹ * δ * entrywiseAut σ n x`.
- No Library module is changed. `GeneralLinear`, `IsRegularSemisimple`,
  `IsRegularElliptic` and `Matrix.GeneralLinearGroup.map` are reused.
- `CyclicNormLemmaStatement` is only stated; its proof (Arthur–Clozel's argument through
  Hilbert's Theorem 90 for `GL_n`, then HL's reduction from cyclic algebras to fields) is
  separate: the Library proves the statement as `cyclicNormLemma` (module
  `Langlands.BaseChange.CyclicNormLemma`).
