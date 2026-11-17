# Satake characters and the unramified base-change homomorphism

Module `Langlands.BaseChange.UnramifiedHecke`. It contains two Prop-valued
definitions (items 1-2) and three proved lemmas (items 3-5), after
Henniart-Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011) (below: HL), Chapter I, §I.1.3
(printed p. 6) and §I.3.1 (printed pp. 24-25). It adds no axioms and no
`Classical.choose`, and it changes no existing module. A helper lemma about
scalar endomorphisms (item 4a) is also proved here.

## Setting

`p` is a prime (`[Fact p.Prime]`). `F : PadicField.{u} p` and `E : PadicField.{v} p`
are the Library's finite extensions of `ℚ_p` (in independent universes), `r : ℕ`, and the
group is `GL_{r+1}`. The module repeats, as local instances declared for every
`PadicField` over every prime, the canonical topology, valuative relation and
local-field structure of `F.Carrier`, and the canonical topology, topological-group,
Hausdorff, Borel measurable and Borel space structures on `GL_n(F)`, exactly as in
`Langlands/Representation/Unramified/HeckeOperators.lean`. So
`SphericalHeckeAlgebra F r`, `sphericalHaar F r` and the standard elements below are the
Library's own objects for both `F` and `E`.

Library objects used (none is redefined):

- `SphericalHeckeAlgebra F r`: the unital complex algebra of compactly supported
  `K`-bi-invariant functions on `GL_{r+1}(F)`, `K = GL_{r+1}(O_F)`, under convolution for
  the Haar measure `sphericalHaar F r` giving `K` mass one. This is HL's `H_F = H(G(F), K)`
  with HL's measure `dg`.
- `standardHeckeElement F r i`, `i : Fin (r + 2)`: the characteristic function of
  `K ϖ^{(i)} K`, `ϖ^{(i)} = diag(ϖ, …, ϖ, 1, …, 1)` with `i` entries `ϖ`, where `ϖ` is the
  uniformizer chosen in `F.canonicalTopologicalData`. For `i = 0` it is the unit.
- `standardHeckeScalar F s i = (√q)^{i(r+1-i)} · e_i(s)` for `s : Eigenvalues (r + 1)`,
  where `q` is the residue cardinality of `F` and `e_i(s)` is the `i`-th elementary
  symmetric function of the entries of `s` (defined in the Library as
  `(-1)^i` times the `i`-th coefficient of `∏_j (1 - s_j X)`).
- `Eigenvalues (r + 1) = Sym ℂˣ (r + 1)`: unordered `(r+1)`-tuples of nonzero complex
  numbers, the Satake parameters; `Eigenvalues.power s l` raises each entry to the power
  `l`.
- `HasSphericalHeckeSpectrum F A s`, for `A : Correspondence.AutomorphicObject F r.succPNat`
  (an irreducible admissible smooth representation of `GL_{r+1}(F)`): the `K`-fixed space of
  `A` is nonzero and every standard element acts on it by `standardHeckeScalar F s i`.
- `sphericalCornerAction F A`: the algebra homomorphism from `SphericalHeckeAlgebra F r` to
  the endomorphisms of the `K`-fixed space of `A`.

## Definitions

1. `IsSatakeCharacter F r s ω` (for `s : Eigenvalues (r + 1)` and an algebra homomorphism
   `ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ`): for every `i : Fin (r + 2)`,
   `ω (standardHeckeElement F r i) = standardHeckeScalar F s i`.
   This describes the character `φ ↦ S_F(φ)(s)`: the Satake transform `S_F` of HL I.3.1
   (printed pp. 24-25) followed by evaluation at `s`. The Satake transform sends the
   characteristic function of `K ϖ^{(i)} K` to `q^{i(r+1-i)/2} e_i(X_1, …, X_{r+1})`
   (Gross 1998, (3.14)), so its evaluation at `s` takes the prescribed values.
2. `IsUnramifiedBaseChangeHom F E l r b` (for `l : ℕ` and an algebra homomorphism
   `b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r`): for every
   `s : Eigenvalues (r + 1)`, every `ωF` with `IsSatakeCharacter F r s ωF` and every `ωE`
   with `IsSatakeCharacter E r (Eigenvalues.power s l) ωE`, `ωF.comp b = ωE`.
   This is HL's base-change homomorphism `b : H_E → H_F`, defined in HL I.1.3 (printed
   p. 6) through the Satake isomorphisms and in HL I.3.1 (printed p. 25) by
   `S_F(b(φ))(X_1, …, X_n) = S_E(φ)(X_1^l, …, X_n^l)`: evaluated at `s`, this says
   `S_F(b φ)(s) = S_E(φ)(s^l)`. No relation between `E` and `F` is needed for this
   definition; `E` need not be an extension of `F`.

## Lemmas with proofs

3. `IsSatakeCharacter.unique`: if `IsSatakeCharacter F r s ω` and
   `IsSatakeCharacter F r s ω'`, then `ω = ω'`. A Satake character is determined by its
   parameter.
   Proof: `ω` and `ω'` agree on the standard elements, hence on the complex subalgebra they
   generate (`AlgHom.eqOn_adjoin_iff`). For any `f`, the proved generation theorem
   `sphericalHeckeGeneration` gives `m` with `T^m * f` in that subalgebra, where
   `T = standardHeckeElement F r (Fin.last (r + 1))`. Hence
   `ω(T)^m ω(f) = ω'(T)^m ω'(f)`, both `ω(T)` and `ω'(T)` equal
   `standardHeckeScalar F s (Fin.last (r + 1))`, which is nonzero
   (`standardHeckeScalar_last_ne_zero`), and cancelling gives `ω f = ω' f`.

4a. `algebraMap_end_injective_of_ne_bot` (helper): for a nonzero complex submodule `N`, the
   map `ℂ → Module.End ℂ N`, `c ↦ c • id`, is injective (the endomorphism ring of a nonzero
   module is a nontrivial `ℂ`-algebra).

4. `exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum`: if
   `A : AutomorphicObject F r.succPNat` satisfies `HasSphericalHeckeSpectrum F A s`, there
   is `ω` with `IsSatakeCharacter F r s ω` such that
   `sphericalCornerAction F A f = algebraMap ℂ _ (ω f)` for every `f`: the spherical Hecke
   algebra acts on the `K`-fixed vectors of `A` through the Satake character at `s`.
   Proof: `exists_common_scalar`, applied with `B = A` and the proved
   `sphericalHeckeGeneration`, shows that every `sphericalCornerAction F A f` is a scalar
   endomorphism, i.e. lies in the bottom subalgebra `⊥`. The fixed space is nonzero, so by
   item 4a `ℂ → ⊥` is an isomorphism (`Algebra.botEquivOfInjective`); `ω` is the corner
   action, with codomain restricted to `⊥`, followed by the inverse of this isomorphism.
   This `ω` is an explicit algebra homomorphism built inside the proof, not a choice. Its
   values on the standard elements are the prescribed scalars by
   `sphericalCornerAction_standardHeckeElement_of_hasSpectrum` and item 4a.
5. `IsUnramifiedBaseChangeHom.sphericalCornerAction_eq`: if
   `IsUnramifiedBaseChangeHom F E l r b`, `HasSphericalHeckeSpectrum F A s` and
   `HasSphericalHeckeSpectrum E B (Eigenvalues.power s l)`, then for every
   `φ : SphericalHeckeAlgebra E r` and `c : ℂ` with
   `sphericalCornerAction E B φ = algebraMap ℂ _ c`, also
   `sphericalCornerAction F A (b φ) = algebraMap ℂ _ c`. So `b` is dual to unramified base
   change of spherical representations (HL I.1.3): if `B` has parameter `s^l` and `A`
   has parameter `s`, then `b φ` acts on the spherical vectors of `A` by the scalar by which
   `φ` acts on those of `B`.
   Proof: item 4 gives Satake characters `ωF` (at `s`, for `A`) and `ωE` (at `s^l`, for
   `B`); item 4a gives `ωE φ = c`; and `ωF (b φ) = (ωF.comp b) φ = ωE φ` by the hypothesis
   on `b`.

## Why characters, and how this matches HL

- The Library has no Satake transform. Items 1 and 2 therefore characterize `S_F` and `b`
  through the characters `φ ↦ S_F(φ)(s)`, without introducing a ring of symmetric Laurent
  polynomials. By the Satake isomorphism (HL I.3.1, citing Laumon 1996, 4.1; Gross 1998,
  Proposition 3.6) these characters exist for every `s` and separate the elements of
  `SphericalHeckeAlgebra F r`: this is statement 6,
  `Langlands.BaseChange.SatakeCharacterStatement`. They are moreover all the algebra
  characters (a remark, not formalized here: for any character `ω`, `ω(T)` is nonzero since
  `T` is invertible, so the numbers `ω(T_i) q^{-i(r+1-i)/2}` are the elementary symmetric
  functions of some `s : Eigenvalues (r + 1)`, and `ω` is the Satake character at `s` by
  item 3). Consequently the `b` defined by HL's formula satisfies item 2, and by statement
  6 it is the only algebra homomorphism that does; this existence and uniqueness is
  statement 7, `Langlands.BaseChange.UnramifiedBaseChangeHomStatement`. Existence uses the
  surjectivity of `S_F` onto the symmetric Laurent polynomials, not only statement 6.
- Normalization. HL's `S_F(f) = S_{0,F}(f^{P_0(F)})`, with
  `f^{P_0(F)}(a) = δ^{1/2}(a) ∫_{U_0(F)} f(au) du` and `S_{0,F}` sending the characteristic
  function of `ϖ^ν A_0(o_F)` to `X^ν`. Other authors send it to `X^{-ν}`, which replaces
  every Satake character at `s` by the one at `s^{-1}` (entrywise inverse). Item 2 does not
  depend on this choice: since `(s^{-1})^l = (s^l)^{-1}` and `s ↦ s^{-1}` is a bijection of
  `Eigenvalues (r + 1)`, the family of conditions "`ωF ∘ b = ωE` for `ωF` at `s` and `ωE`
  at `s^l`, for all `s`" is the same for both normalizations.
- Unramified extensions. If `E/F` is unramified of degree `l`, a uniformizer `ϖ_F` of `F`
  is a uniformizer of `E`, and `q_E = q_F^l`. The double cosets `K_E ϖ^{(i)} K_E` do not
  depend on the choice of uniformizer (two choices differ by a diagonal matrix in
  `K_E`), so `standardHeckeElement E r i`, built from the uniformizer of
  `E.canonicalTopologicalData`, is the characteristic function of `K_E ϖ_F^{(i)} K_E`, which
  HL use (their `S_{0,E}` is built with the uniformizer `ϖ` of `F` and does not depend on
  it). Likewise `standardHeckeScalar E` uses `q_E`, the residue cardinality of `E`, as HL's
  `S_E` (defined "de la même manière" as `S_F`) does. So the standard elements and scalars
  of `E` are those of HL I.3.1.
- Statement 9 (`Langlands.BaseChange.FundamentalLemmaStatement`, the fundamental lemma
  for the whole spherical Hecke algebra, HL I.6.6) quantifies over every `b` with
  `IsUnramifiedBaseChangeHom F E l r b`, because the map is not constructed here (that would
  need the Satake isomorphism). Statement 7 asserts that exactly one `b` satisfies this
  hypothesis, so statement 9 is not vacuous once statement 7 is proved.
- Statement 8 (`Langlands.BaseChange.UnitFundamentalLemmaStatement`, the fundamental lemma
  for the units, HL I.3.1, Proposition) is the case `φ = 1` of statement 9, since every
  algebra homomorphism satisfies `b 1 = 1`, and the units of `SphericalHeckeAlgebra E r` and
  `SphericalHeckeAlgebra F r` are the characteristic functions of `K_E` and `K` (HL:
  `b(φ_e) = f_e`). It is stated separately because HL (after Kottwitz) and Arthur-Clozel
  prove it first, by a different argument, and deduce the general case from it.
- Statements 8 and 9 use `IsCyclicAlgebra` (Task 7405) and `AreConcordant` (Task 7416);
  they are published in their own modules, not in this one.

## Sources

- Henniart-Lemaire (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
  (PDF page = printed page + 8):
  - §I.1.1, printed p. 5: `E/F` unramified of degree `l`, `K = G(o_F)`, `K_E = G(o_E)`,
    the Haar measures giving `K` and `K_E` volume one;
  - §I.1.3, printed p. 6: `H_F = H(G(F), K)`, `H_E = H(G(E), K_E)`, and `b : H_E → H_F`
    defined through the Satake isomorphisms;
  - §I.3.1, printed pp. 24-25: the Satake isomorphism `S_F` (their reference [57]: Laumon,
    *Cohomology of Drinfeld modular varieties I*, 1996, 4.1), its definition by
    `f^{P_0(F)}`, the independence of the choice of `ϖ`, the formula
    `S_F(b(φ))(X_1, …, X_n) = S_E(φ)(X_1^l, …, X_n^l)` and `b(φ_e) = f_e`.
- Gross, *On the Satake isomorphism* (1998), source ID `gross-1998-satake-isomorphism`,
  Proposition 3.6 (the Satake transform is a ring isomorphism onto the Weyl invariants) and
  (3.14) (for `GL_n`, the transform of the `i`-th standard element is `q^{i(n-i)/2}` times
  the `i`-th elementary symmetric function).
