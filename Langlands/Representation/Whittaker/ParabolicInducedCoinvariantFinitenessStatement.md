# Preservation of finite character coinvariants by parabolic induction

Authors: Worker 288 (source audit, Lean statement and documentation) and
Worker 499 (conditional formulation and finite-orbit dependency route).

`Langlands.Whittaker.ParabolicInducedCoinvariantFinitenessStatement.{uF,uV}`
is a closed `Prop`-valued definition. It is an internal conditional derivation
from Bernstein–Zelevinsky (1976), §7.12(1)–(5), printed pp.60–61.
The source treats irreducible cuspidal inducing data. Here its coefficient
finiteness is an explicit premise on an arbitrary smooth Levi representation.
The module defines no new representation or quotient and proves no finiteness
assertion.

## Exact quantifiers and objects

For every prime `p`, with `Fact p.Prime`, every finite p-adic extension
`F : PadicField.{uF} p`, and every supplied `T : F.TopologicalData`, install
`T.topology`. For every `n : ℕ` with `0 < n` and every
`B : GeneralLinear.BlockShape n`, install
`T.generalLinearTopologicalGroup n`. The block shape consists of an ordered
finite family of positive sizes whose sum is `n`; every such shape is included.
In particular, rank one and the single-block shape are included.

Write, for explanation only,

\[
 G=\mathrm{GL}_n(F),\qquad P=B.\mathrm{parabolic}(F),\qquad
 M=B.\mathrm{Levi}(F)=\prod_{i:\mathrm{Fin}(B.\mathrm{length})}
     \mathrm{GL}_{B.\mathrm{size}(i)}(F),
\]
\[
 U=\mathrm{upperUnipotent}_n(F),\qquad
 U_M=\prod_i\mathrm{upperUnipotent}_{B.\mathrm{size}(i)}(F).
\]

These are the existing actual matrix groups. `P` is the standard upper
block parabolic, `M` is the actual product Levi, and `U` is the upper
unitriangular subgroup. In Lean the subgroup `U_M : Subgroup M` is exactly

```lean
Subgroup.pi Set.univ
  (fun i : Fin B.length =>
    GeneralLinear.upperUnipotent (B.size i) F.Carrier)
```

The field topology determines the matrix-unit topology, the product topology
on `M`, and the subgroup topologies on `P`, `U` and `U_M`.
For every actual object `σ : SmoothRep.{0,uF,uV} ℂ M`, its carrier is in
`Type uV` and its existing algebraic action is `σ.representation`.
Smoothness is bundled: every vector is fixed by an open subgroup. No topology
on the coefficient carrier is required.

The sole additional premise on `σ` is that for every homomorphism
`η : U_M →* ℂˣ` with `IsLocallyConstant (fun u => (η u : ℂ))`, the actual space

```lean
Jacquet.Localization.Coinvariants σ.representation U_M η
```

is finite-dimensional over `ℂ`. This premise concerns characters of the
whole product subgroup and requires no factorization of `σ` as a tensor
product. It gives no uniform numerical bound.

The conclusion is that for every homomorphism `θ : U →* ℂˣ` with locally
constant complex values, the actual quotient

```lean
Jacquet.Localization.Coinvariants
  (Induction.smoothInduced (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B)
      (σ.representation.comp (B.leviProjection F.Carrier))))
  (GeneralLinear.upperUnipotent n F.Carrier) θ
```

is finite-dimensional over `ℂ`. Both character quantifiers include trivial
and degenerate characters. There is no irreducibility, cuspidality,
admissibility, finite length, Whittaker-functional, or finite coefficient
dimension premise.

The universes `uF` and `uV` are independent. Smooth induced functions take
values in the original carrier of `σ`; their carrier and its character
quotient lie in `Type (max uF uV)`. The statement neither resizes the
coefficient space nor identifies its universe with the field universe.

## Induction and character conventions

`B.leviProjection F.Carrier` is the existing homomorphism extracting the
invertible diagonal blocks of an upper block triangular matrix.
`T.parabolicHalfModulus B` is the existing positive complex half-modulus,
inflated through that projection. On a Levi element `m` its square is the
positive character

\[
 \delta_P(m)=\prod_{i<j}
   \frac{|\det m_i|^{B.\mathrm{size}(j)}}
        {|\det m_j|^{B.\mathrm{size}(i)}}.
\]

Thus the covariance representation is precisely
`δ_P^(1/2) ⊗ (σ ∘ leviProjection)`. The smooth induction consists of actual
covariant functions with a uniform open right stabilizer, with
`f(pg) = δ_P(p)^(1/2) • σ(leviProjection p)(f(g))`.
The ambient action is right translation, `(g₀ • f)(g) = f(gg₀)`.
This is the Library's normalized upper-parabolic induction convention.
The source's §3.12 uses induction of inflated Levi data; passing to the
displayed normalized covariance is part of this internal formulation.

Every `Jacquet.Localization.Coinvariants ρ H χ` is the existing quotient
of the coefficient module by the complex span of
`ρ(h)v - (χ(h) : ℂ) • v`. This is the positive-character convention of
BZ76 Definition 2.30. As §2.31(a) explains, its ordinary-coinvariant
description uses the inverse-character twist. Any compact-induction
comparison must preserve this sign.

## Derivation and remaining proof obligations

BZ76 §7.12(1) realizes induction as compactly supported sections on `P \ G`,
orders its finitely many `U`-orbits, and applies localization exactness.
Parts (2)–(4) identify the orbit stabilizers and their relation to the Levi
upper unipotent. In part (5), irreducibility and cuspidality establish the
finite coefficient quotients used to bound the orbit contributions.
Replacing that last input by the displayed finiteness premise yields the
present generalized conditional target. It retains only finiteness,
without the source's factorial bound or its nondegenerate dimension-one
conclusion.

A proof of this target must implement the following comparisons and assembly;
they are obligations, not additional hypotheses of the proposition.

1. Construct the finite `U`-orbit support filtration of the actual induced
   module, with open initial unions and exhaustive endpoints. Reuse
   `Whittaker.UnipotentOrbitProof`, `Geometric.ClosedSubgroupMackeyProof`,
   `Geometric.CompactSmoothComparison` and `Parabolic.QuotientCompactProof`
   for the actual orbit geometry, compact quotient and induction comparison.
   Carry the specified positive half-modulus covariance through these maps.
2. Identify each localized orbit piece with the character quotient of its
   conjugated stabilizer coefficient representation by compact localization.
   The existing `Whittaker.CompactLocalizationStatement` and its proof module
   use canonical topological data. Applying them here requires transport
   from the supplied `T`, or a suitable generic theorem, and conversion of
   the locally constant character to the required smooth character.
   The existing supplied-topology comparisons and equality of half-modulus
   characters provide infrastructure; their application to every object and
   comparison in this argument remains to be assembled.
3. For each minimal representative, include the Levi upper unipotent in
   the conjugated stabilizer as in §7.12(4). In the source convention the
   orbit is `P w U`, its stabilizer is `H_w = U ∩ w⁻¹ P w`, and
   `w H_w w⁻¹` contains the embedded `U_M`. The Library stores a
   representative `r` for the orbit `P r⁻¹ U`, so this formula uses
   `w = r⁻¹`. Pull back the conjugated character to the actual product
   subgroup `U_M`, prove local constancy, and obtain a surjection from
   its coefficient character quotient onto the stabilizer character
   quotient. Check that the normalized covariance restricts to
   `σ.representation` on this embedded unitriangular subgroup:
   the diagonal block determinants are one, so the half-modulus is one.
   The premise then gives finite dimension for the stabilizer quotient
   and hence for the localized orbit piece.
4. Use character-localization exactness and the finite filtration to
   propagate finite dimensionality through finite extensions. Reuse
   `Jacquet.LocalizationFiltrationGradedProof` and
   `Jacquet.LocalizationExactnessProof` for localization of the actual
   successive quotients and exact sequences, then supply the finite
   dimensional linear-algebra assembly.

This statement does not depend on an unproved multiplicity-one assertion.
The independent cuspidal coefficient result can later discharge its premise
for cuspidal inducing data; neither that result nor the irreducible final
assembly is stated or proved here.

## Original source and reading

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys
**31:3** (1976), 1–68, English translation.
Registered source: `bernstein-zelevinsky-1976-representations-gln`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Read §2.23 (printed p.22), §§2.30–2.35 (pp.24–25), §3.12 (p.32),
and §7.12(1)–(5) (pp.60–61); printed pages equal one-based PDF pages.
Page 61 was also visually checked for the stabilizer, conjugation,
containment and character formulas. No source-specific erratum note was
found in the checked project or Library notes; neither checked
`notes/errata` directory exists. The arbitrary smooth coefficient premise,
normalized covariance, supplied topological data and independent universes
are this module's derived formulation, not a literal source theorem.
