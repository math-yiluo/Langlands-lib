# Determinant and pair-factor compatibility of the relative isometry

This is a derived **statement target**. The file contains no proof of
`Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`, whose level
parameters are `uF uW uP uE`. It is unit U4a-ii of the H3 program (Henniart's
global construction, task `34b81620-20d7-4059-9b08-6bedd1c1c029`). Worker 30,
whose task `62ea68fa` lists the same sections of Henniart as source leads,
agreed that H3 states it. The target is a finite-relative, witnessed analogue,
at a fixed finite level `E/F` and for witnessed spans, of the determinant
clause of Henniart's Proposition 2.6 (a) and of the L- and ε-factor clauses of
his Proposition 2.6 (b). Henniart states these clauses for the images of the
absolute global Weil group. The target does not identify its spans or its
isometry with those absolute-global objects (see "Relation to Henniart's
absolute-global objects" below). The analogues of the degree clause of (a) and
of the scalar-product clause of (b) are already part of the published
`RelativeGeneratedPositiveIsometry`. The contragredient and twist clauses of
(a), and all of (c), are the separate unit U4a-i
(`RelativeIsometryOperationStatement`). This file does not import it.

## Setting

The objects are those of the published `RelativePolePairingStatement`
(`Langlands/Global/Factors/RelativePolePairingStatement.lean`):

- number fields `F` and `E` in a common universe, with `E/F` Galois;
- the compact adele quotient instance;
- a fundamental class family `c` with `RelativeWeilGroup.IsArithmeticClassFamily c`;
- a finite place `v` of `F` and a nontrivial additive character `ψ` of `F_v`.

The pole-comparison input `RelativeCertifiedPoleComparisons F E c v ψ` is kept
as an explicit hypothesis. `weilImage F E c v` and `automorphicImage F E c v`
are the published integral spans of the local elements of all witnessed
generators (`RelativeGlobal.WitnessedGenerator`). They sit in the unitary Weil
lattice `LocalWeil.UnitaryLattice (padicField v)` and in the unitary
supercuspidal lattice `PadicSupercuspidal.UnitaryLattice (padicField v)`. Both
lattices are free on their bases `UnitaryBasis` of unitary irreducible classes
of positive rank. The statement concerns every linear equivalence
`T : weilImage ≃ₗ[ℤ] automorphicImage` satisfying
`RelativeGeneratedPositiveIsometry`. Under the pole hypothesis the published
theorem `relativePolePairing` gives exactly one such `T`, so the statement is
not vacuous. This `T` is the relative, witnessed analogue of Henniart's
isomorphism `ρ ↦ π(ρ)` of Theorem 2.5; it is not identified with that
isomorphism. All conclusions are restricted to the generated spans at the
fixed level `E/F`. Nothing is claimed about the full local lattices.

## Helper declarations

Henniart defines the determinant on his Weil-side lattice by `ℤ`-linearity
from the basis, and the central character and the L- and ε-factors of pairs on
his automorphic-side lattice "par leur valeur sur `B_A × B_A` et
`ℤ`-bilinéarité" (§2.6, printed p.446). The helpers below are these
extensions, written multiplicatively. A lattice element is a finitely
supported function `x` from the basis to `ℤ`; `x.prod` and `x.sum` run over
its support with the multiplicities `x a`.

On the Weil side (namespace `Langlands.VirtualRepresentation.LocalWeil`, for a
`p`-adic field `F`):

- `unitaryDeterminant F` is the `ℤ`-linear map from the unitary Weil lattice
  to `Additive (W_F →* ℂˣ)` sending a basis class `b` to the determinant
  character `FiniteRepresentation.determinantCharacterClass` of its underlying
  class. A local instance takes the additive monoid of `Additive (G →* ℂˣ)`
  from its additive group, exactly as the published
  `ExactGrothendieckGroup.determinant` does, so that the canonical
  `ℤ`-module structure applies.
- `unitaryBasisPairClass F b` is the published zero-monodromy pair class
  `Correspondence.weilPairClass` of the basis class `b`.
- `unitaryPairLFactor F x y` is
  `∏_{a ∈ supp x} ∏_{b ∈ supp y} L(s, a ⊗ b)^(x(a) y(b))`, where `L(s, a ⊗ b)`
  is the published `Correspondence.arithmeticPairLFactor` of the two pair
  classes: the Euler factor of the actual tensor product on `(ker N)^I` at the
  published geometric Frobenius lift, as a rational function of `X = q^(-s)`.
- `IsUnitaryPairEpsilonFactor F eC ε hε ψ x y e` holds when some function
  `f` assigns to each pair `(a, b)` of basis classes with `a ∈ supp x`,
  `b ∈ supp y` a pair `f a b = (c_ab, m_ab)` certified by the published
  `Correspondence.IsArithmeticPairEpsilonFactor` (that is,
  `ε(s, a ⊗ b, ψ) = c_ab q^(-m_ab s)` for the supplied local-constant system),
  and `e = (∏ c_ab^(x(a) y(b)), ∑ x(a) y(b) m_ab)`. This is the bilinear
  extension of the epsilon monomials.

On the supercuspidal side (namespace
`Langlands.VirtualRepresentation.PadicSupercuspidal`):

- `IsUnitaryBasisCentralCharacter F b ω`: every `a ∈ F^×` acts on the basis
  class `b` by `ω(a)`, in the sense of the published
  `Correspondence.SupercuspidalCentralActsBy`.
- `IsUnitaryCentralCharacter F y ω`: some function `f` gives a central
  character `f b` of every basis class `b` in the support of `y`, and
  `ω = ∏_{b ∈ supp y} (f b)^(y(b))`.
- `IsUnitaryBasisPairLPolynomial F ψ ν a b P` and
  `IsUnitaryBasisPairEpsilonFactor F ψ ν a b e` are the published JPSS
  relations `Correspondence.IsSupercuspidalPairLPolynomial` and
  `Correspondence.IsSupercuspidalPairEpsilonFactor` on two basis classes,
  written at their positive ranks `r + 1` and `n + 1`. They read
  `L(s, a × b) = 1 / P(q^(-s))` and `ε(s, a × b, ψ) = c q^(-ms)` with
  `e = (c, m)`, for the additive character `ψ` and the measure `ν`. The
  fallback case `False` covers rank zero, which basis classes never have.
- `IsUnitaryPairLFactor F ψ ν x y L`: some function `P` gives a JPSS
  L-polynomial `P a b` for every pair of basis classes in the supports, and
  `L = ∏ (1 / P a b (q^(-s)))^(x(a) y(b))`.
- `IsUnitaryPairEpsilonFactor F ψ ν x y e`: some function `f` gives a JPSS
  epsilon certificate `f a b` for every pair of basis classes in the supports,
  and `e` is their multiplicity-weighted product, as on the Weil side.

Four proved theorems check that the extensions restrict correctly to basis
vectors `generator b`:

- `LocalWeil.unitaryDeterminant_generator`: the virtual determinant of a basis
  class is its actual determinant character;
- `LocalWeil.unitaryPairLFactor_generator`: the virtual pair L-factor of two
  basis classes is their actual arithmetic pair L-factor;
- `PadicSupercuspidal.isUnitaryPairLFactor_generator_iff`: the virtual pair
  L-factor relation on two basis classes is the actual JPSS relation
  `L = 1 / P(q^(-s))`;
- `PadicSupercuspidal.isUnitaryCentralCharacter_generator_iff`: the virtual
  central-character relation on a basis class is the actual one.

## The predicates

For a fixed `T`:

- `RelativeIsometryDeterminantCompatibility T e`: for every `x` in
  `weilImage`, some character `ω` of `F_v^×` is the central character of
  `T x` (`IsUnitaryCentralCharacter`), and
  `ω(reciprocityHom e w) = (unitaryDeterminant x)(w)` for every `w` in the
  local Weil group. Here `Correspondence.reciprocityHom e` is the
  abelianization of the local Weil group followed by the reciprocity
  candidate `e`. It is the relative analogue of Henniart's
  `det ρ = ω_{π(ρ)} ∘ τ_{F_0}`.
- `RelativeIsometryPairFactorCompatibility T ψ`: a self-dual measure `ν` for
  `ψ` exists (`Correspondence.IsSelfDualMeasure`), and for every self-dual `ν`
  and all `x`, `y` in `weilImage`:
  - `IsUnitaryPairLFactor ψ ν (T x) (T y) (unitaryPairLFactor x y)`, the
    analogue of `L(π(ρ) × π(ρ'), s) = L(ρ ⊗ ρ', s)`;
  - for every local-constant system `(eC, ε, hε)`, some `e = (c, m)` is both a
    Weil-side value `LocalWeil.IsUnitaryPairEpsilonFactor eC ε hε ψ x y e` and
    a JPSS-side value `PadicSupercuspidal.IsUnitaryPairEpsilonFactor ψ ν
    (T x) (T y) e`, the analogue of
    `ε(π(ρ) × π(ρ'), s, ψ) = ε(ρ ⊗ ρ', s, ψ)`.
- `RelativeIsometryFactors T` is the determinant clause for every candidate
  `e` satisfying `Correspondence.IsGeometricReciprocity`, together with the
  pair-factor clause for every nontrivial additive character `ψ` of `F_v`.

`RelativeIsometryFactorStatement` says: for all `F, E, c, v, ψ` as above,
`IsArithmeticClassFamily c` and the certified pole comparisons at `v` and `ψ`
imply `RelativeIsometryFactors T` for every `T` satisfying
`RelativeGeneratedPositiveIsometry`.

## Conventions and adaptations

- **Reciprocity.** Henniart (§1.1, printed p.439) normalizes local reciprocity
  so that geometric Frobenius elements correspond to uniformizers. The
  determinant clause uses the published geometric relation
  `IsGeometricReciprocity` and quantifies over every candidate that satisfies
  it. By local class field theory there is exactly one such candidate. In the
  Library this existence and uniqueness is the published, still unproved
  statement `LocalClassField.WeilReciprocityExistenceUniqueness`, so the
  target fixes no candidate.
- **Local-constant systems.** The Weil-side epsilon factor is relative to a
  local-constant system `(eC, ε, hε)` with
  `LocalFactor.NonabelianSystem.IsSystem`. That property contains
  `NormalizedReciprocity` (coherent reciprocity with `|rec w| = q^(-deg w)`),
  which is the geometric normalization. No system is selected: the clause
  holds for every system, as in the published
  `RelativeWeilGroup.IsPairFactorMatch` (used in the Library form of
  Henniart's Corollary 2.4) and
  `Correspondence.SupercuspidalPairFactorCompatibility`. At a fixed system,
  the published theorem `IsArithmeticPairEpsilonFactor.unique` says that the
  certificate of each pair of basis classes is unique. So the Weil-side value
  `e` is determined by `x`, `y` and the system.
- **Additive characters and measures.** Henniart's (b) holds for every
  nontrivial additive character of `F_0`, so the target quantifies over every
  `ψ`. It is not only the `ψ` of the retained hypothesis. The JPSS relations
  depend on a measure `ν`. As in `SupercuspidalPairFactorCompatibility` and
  `IsPairLMatch`, the clause asserts that a self-dual measure exists and that
  the identities hold for every self-dual measure.
- **Factors on virtual classes.** Henniart takes the L- and ε-factors of pairs
  on his Weil-side lattice from tensor products and `ℤ`-linearity, and on his
  automorphic-side lattice from basis values and `ℤ`-bilinearity (§2.6,
  printed p.446). The helpers are these bilinear extensions, written as
  multiplicity-weighted products of basis values. On the Weil side they agree
  with the factors of actual semisimple representations, as Henniart remarks.
  The Library does not yet prove this; see the next section.
- **Unitarity.** Henniart's footnote 1 (printed p.439) calls a continuous
  homomorphism to `ℂ^×` a quasicharacter, and a character if it is unitary.
  The lattices are spanned by unitary irreducible classes, as his `B_G` and
  `B_A` in the unitary case. The central characters `ω` in the determinant
  clause are not required to be unitary; they are unitary because the basis
  classes are.
- **Universes.** The level parameters are those of the published images:
  `uF` for the fields, `uW` for Weil carriers and `uP` for presentation
  factors. The supercuspidal side uses the form-space universe `uF`. The new
  level `uE` is the universe of the local-constant assignments `ε`. The
  universe `uV` appears only in the helper declarations.

## Relation to Henniart's absolute-global objects

Henniart (§2.1, printed p.444) works with the absolute global Weil group
`W_F`. His `R_G(F, 0)` and `R_A(F, 0)` (§2.5, printed pp.445–446) are spanned
by the local data of *all* associated pairs of an irreducible unitary
representation of `W_F` and a unitary cuspidal representation. The published
`weilImage` and `automorphicImage` are instead spanned by the local elements
of the witnessed generators at one finite Galois extension `E/F`: an
irreducible unitary representation of `RelativeWeilGroup c F E`, an actual
cuspidal realization with a presentation, weak association, a local relative
Weil map at a place above `v`, an exact local expansion and a unitary
supercuspidal support, all supplied as data. As the imported `RelativeImages`
Markdown records, the comparison between relative and absolute images, global
automorphic unitarity, and the existence and uniqueness of local maps,
expansions and supports are separate obligations. This statement leaves all of
them open. It asserts the determinant and pair-factor clauses for the relative
spans only.

## Why the target is true

Henniart's proof in §2.8 (printed p.448) takes the central character from §2.2
(printed p.444). It takes the L- and ε-factors of pairs from Theorem 2.4, its
Corollary (printed p.445) and the Remark in §1.3 (printed p.441). The sketch
below carries this out at the fixed level `E/F`. Everything in it is a future
proof obligation; the named statements are published but not yet proved.

**Reduction to generators.** The pole hypothesis is not used, except through
the existence of `T`. A `T` satisfying `RelativeGeneratedPositiveIsometry`
sends `d.weilElement` to `d.automorphicElement` for every witnessed generator
`d`. Every `x` in `weilImage` is an integral combination `∑ k_i d_i.weilElement`,
and then `T x = ∑ k_i d_i.automorphicElement`. Both sides of each clause are
multiplicative in `x` (and in `y`) once the following hold for every basis
class in the supports of the generators' elements:

- each unitary supercuspidal basis class has a central character, and it is
  unique (the class is irreducible and nonzero);
- each pair of such basis classes has a unique JPSS L-polynomial and a unique
  JPSS epsilon certificate, for every `ψ` and self-dual `ν`;
- each pair of Weil basis classes has an arithmetic epsilon certificate for
  every system; it is unique by `IsArithmeticPairEpsilonFactor.unique`;
- the basis L-factors are nonzero rational functions, so their integer powers
  multiply.

With these facts, each virtual relation defines a function of its arguments,
and it is multiplicative in each argument. So each clause for `x` and `y`
follows from the clause for generators.

**Determinant, for one generator `d`.** Let `S` be its Weil representation,
`Π` its cuspidal realization with presentation `P`, and `ι` its local relative
Weil map at `v`.

- `d.weil_expansion` says that `d.weilElement` expands the exact class of
  `S ∘ ι`. The virtual determinant must be shown to agree with the published
  exact determinant (`ExactGrothendieckGroup.determinant`) along this
  expansion. Then `unitaryDeterminant d.weilElement = det(S ∘ ι) = (det S) ∘ ι`.
- Henniart §2.2 gives `det S = ω_Π ∘ τ_F`. In the Library this is
  `RelativeWeilGroup.AssociatedCentralCharacterStatement` or the presented
  form `RelativeWeilGroup.PresentedDeterminantAssociationStatement`:
  `FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω_Π`,
  where `reciprocityCharacter c F E ω_Π` is `w ↦ ω_Π(transfer c F E w)⁻¹`. As
  in U4a-i, at finite level `τ_F` is the pointwise inverse of
  `RelativeWeilGroup.transfer`, so two inversions occur. The published
  `RelativeWeilGroup.LocalTransferReciprocityStatement` gives
  `HasLocalTransferReciprocity v ι`: for every geometric candidate `e` of
  `F_v`, `transfer c F E (ι g) = (ofAdicCompletion v (reciprocityUnits e g))⁻¹`.
  Hence `(det S)(ι g) = ω_Π(ofAdicCompletion v (reciprocityUnits e g)) =
  ω_{Π,v}(reciprocityHom e g)`, where `ω_{Π,v}` is `ω_Π` restricted to
  `F_v^×`. This needs `IsArithmeticClassFamily c`, `IsLocalRelativeWeilMap`
  and a proof of `LocalTransferReciprocityStatement`.
- On the automorphic side, `d.automorphic_support` says that
  `d.automorphicElement` encodes a unitary supercuspidal support
  `{σ_1, …, σ_k}` of the local component `Π_v`: `Π_v` is an irreducible
  subquotient of `σ_1 × ⋯ × σ_k` (the published `IsSupercuspidalSupport`).
  Two facts must be supplied. First, the central character of `Π_v` is
  `ω_{Π,v}`. Second, the centre of `GL_n(F_v)` acts on the normalized
  parabolic induction `σ_1 × ⋯ × σ_k`, and hence on each of its subquotients,
  by the product of the central characters of the `σ_i`. Together they give
  `IsUnitaryCentralCharacter d.automorphicElement ω_{Π,v}`, which is the
  determinant clause for `d`.

**Pair factors, for two generators `d`, `d'`.** Let `S`, `S'`, `Π`, `Π'`,
`ι`, `ι'` be their data.

- The published `RelativeWeilGroup.AssociatedCuspidalFactorStatement` (Library
  form of Henniart's Corollary 2.4) gives `IsPairFactorMatch` at `v`: for the
  local components `Π_v`, `Π'_v` and the pair classes of `S ∘ ι`, `S' ∘ ι`,
  the L-factors agree for every self-dual measure, and the epsilon factors
  agree for every local-constant system. Its hypotheses are not all part of a
  witnessed generator, which leaves three obligations:
  - *one local map for both.* The corollary uses the same `ι` for `S` and
    `S'`, while `d'` carries its own `ι'`, possibly at another place above
    `v`. Local relative Weil maps at `v` must be shown conjugate in
    `RelativeWeilGroup c F E`, so that `S' ∘ ι' ≅ S' ∘ ι`.
  - *unitary central characters.* The corollary needs
    `HasUnitaryCentralCharacter` for `Π` and `Π'`. It should follow from
    `det S = reciprocityCharacter c F E ω_Π` with `S` unitary, together with
    the uniqueness clause of `AssociatedCentralCharacterStatement`.
  - *canonical additive characters.* The corollary applies only to a `ψ_v`
    that is the canonical component (`IsCanonicalFiniteAdditiveComponent`) of
    a global additive character trivial on `F`. Every nontrivial `ψ` of `F_v`
    is `ψ_v(a ·)` for some such `ψ_v` and some `a ∈ F_v^×`. Henniart's Remark
    in §1.3 (printed p.441) states that the ε-identity for one additive
    character implies it for all of them, provided the determinant condition
    holds. The reason is that both epsilon factors change by the same factor,
    which depends only on `a`, the degrees and the determinants (resp. central
    characters). Here it is applied to `Π_v × Π'_v` and
    `(S ∘ ι) ⊗ (S' ∘ ι)`, before passing to supports. The degree clause of `RelativeGeneratedPositiveIsometry` and
    the determinant clause above give this condition. The JPSS L-polynomial
    must also be shown independent of `ψ` and `ν`.
- *From representations to supports.* The corollary compares the factors of
  `Π_v × Π'_v` with those of `(S ∘ ι) ⊗ (S' ∘ ι')`. The target compares the
  bilinear extensions over the supports. On the automorphic side, `Π_v` must
  first be identified with the full induction `i(σ_1, …, σ_k)`. Henniart's
  Theorem 2.4 (the published
  `RelativeWeilGroup.AssociatedSupercuspidalInductionStatement`, which also
  needs `HasUnitaryCentralCharacter`) says that `Π_v` is induced from
  unitarizable supercuspidal representations. Uniqueness of supercuspidal
  supports then identifies the inducing data with `{σ_1, …, σ_k}`. Next, the
  factors of `i(σ_1, …, σ_k) × i(σ'_1, …, σ'_l)` must be shown to be the
  products of the factors of the `σ_i × σ'_j`. The published
  `RankinSelberg.MultiplicativityStatement` (JPSS 1983, Theorem (3.1)) gives
  multiplicativity of gamma factors and only a divisibility of L-factors. The
  equality needed here is for irreducible representations induced from
  unitary supercuspidal ones; Henniart uses the corresponding results
  [JPSS, Prop. 8.1 and 8.4] in the Lemma of §2.8. On the Weil side,
  `S ∘ ι` is semisimple because `S` is unitary. The arithmetic pair L-factor
  and the epsilon certificate must be shown additive over direct sums; for
  epsilon factors this is the `AdditiveRelation` part of `IsSystem`.

The target fixes neither a local map nor a global additive character, and it
claims the identities for every `ψ`, every self-dual measure and every
system. This is why the three obligations above are needed.

## Provenance

The source is Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455:

- §2.6, preamble (definitions on the lattices by `ℤ`-linearity and
  `ℤ`-bilinearity) and Proposition (a), determinant clause, and (b), L- and
  ε-factor clauses, printed pp.446–447;
- the proof in §2.8, printed p.448;
- the central character of associated pairs in §2.2, printed p.444;
- Théorème 2.4 and its Corollaire, printed p.445;
- the Remark in §1.3 on the choice of additive character, printed p.441;
- the absolute global Weil group setting in §2.1, printed p.444, and the
  definition of `R_G(F, 0)` and `R_A(F, 0)` in §2.5, printed pp.445–446;
- the normalization of reciprocity in §1.1, and footnote 1 (characters are
  unitary quasicharacters), printed p.439.

Printed page `p` is page `p - 438` of the PDF, counting from 1. The Lean
formulation is derived: it is a finite-relative, witnessed analogue of the
selected clauses. The published `weilImage` and `automorphicImage` at level
`E/F` play the roles of Henniart's `R_G(F, 0)` and `R_A(F, 0)`, and the `T` of
`RelativeGeneratedPositiveIsometry` plays the role of his isomorphism, but
they are not identified with them. His local reciprocity map `τ_{F_0}`
corresponds to a candidate satisfying the geometric relation. His factors on
virtual classes correspond to the bilinear extensions defined here.
