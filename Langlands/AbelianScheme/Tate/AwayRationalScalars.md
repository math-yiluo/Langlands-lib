# Prime-to-modulus adelic actions on actual rational Tate modules

Worker 1060 updated the scalar-comparison status sentences after the
2026-10-29 documentation audit (finding P3-027).

This module constructs the action of the existing prime-to-modulus finite
adeles on the actual away rational Tate module. It keeps both the full scalar
comparison and its compatible away comparison as explicit hypotheses. It
proves compatibility with full-to-away restriction and rational homomorphisms,
and constructs the action of a rational endomorphism algebra tensored with
these adeles.

## Parameters and comparison witnesses

Fix a scheme `S`, a commutative group object `G` in `Over S`, a test scheme
`T : Over S`, and a natural number `m`. The carrier `RationalAway G T m` is
`ℚ ⊗[ℤ] Away G T m`: the rationalization of the compatible actual torsion
sections at positive orders coprime to `m`. For prime `m = p` this is the
prime-to-p construction. For positive composite `m` it excludes the prime
divisors of `m`; the definitions also retain `m = 1` and `m = 0`.

The hypotheses are

```lean
h : Global.RationalProfiniteIntegerAdeleComparison
hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

They are proposition proofs, not fields supplying arbitrary scalar actions.
This module does not prove either comparison. Both are published theorems in
separate modules: `Langlands.Global.rationalProfiniteIntegerAdeleComparison`,
in `Langlands.Global.RationalProfiniteIntegerComparisonProof`, proves the full
comparison, and
`Langlands.Global.primeToRationalProfiniteIntegerAdeleComparisons`, in
`Langlands.Global.PrimeToRationalProfiniteIntegerComparisonProof`, proves the
away comparison for every full comparison proof `h` and every natural `m`. A
caller can therefore supply `h` and `hAway` from these theorems; the
definitions here keep them as explicit parameters. The away proposition
requires normalized integral and rational equivalences compatible with the
coupled full witnesses chosen from `h`.

In `Global.PrimeToRationalProfiniteIntegerAdeleComparison`, `integralEquiv`
chooses the integral away witness `e₀`, and `rationalEquiv` chooses its coupled
rational witness `e`. Their domains and codomains are

\[
e_0:\widehat{\mathbb Z}^{\,m}_{\mathrm{res}}
  \simeq \mathbb A_f^{\,m,\mathrm{int}},\qquad
e:\mathbb Q\otimes_{\mathbb Z}\widehat{\mathbb Z}^{\,m}_{\mathrm{res}}
  \simeq_{\mathbb Q}\mathbb A_f^{\,m}.
\]

Here the superscript denotes the retained places, and the target is exactly
`Global.PrimeToFiniteAdeles m`, the existing restricted product of actual
finite completions. It is not a new adelic model.

`rationalEquiv_tmul` extracts the required formula
`e(q ⊗ a) = diag(q) * e₀(a)`. `integralEquiv_restrict` extracts compatibility
of integral restriction. `rationalEquiv_restrict` extends the assumed
pure-tensor restriction identity to every rationalized full residue scalar
by tensor induction and additivity. `rationalEquiv_symm_restrict` proves the
corresponding identity for the inverse equivalences by applying the injective
map `e` and cancelling both inverse pairs. The full witnesses used throughout
are exactly those from `RationalScalars` and the same `h`.

## The actual Tate action and restriction

`GroupScheme.Tate.primeToFiniteAdeleAction` composes the previously constructed
`rationalAwayScalarAction` with `e.symm`. Thus it is a rational-algebra
homomorphism

\[
\mathbb A_f^{\,m}\longrightarrow
\operatorname{End}_{\mathbb Q}(\mathbb Q\otimes_{\mathbb Z}T^mG(T)).
\]

The algebra-homomorphism type provides additivity, multiplicativity and the
unit law. `primeToFiniteAdeleModule` exposes the associated module structure
for local installation; it is not registered as a global instance.
`primeToFiniteAdeleModule_smul` identifies scalar multiplication with evaluation
of the constructed action. `primeToFiniteAdeleAction_diagonal` proves that
diagonal rational scalars act by the existing rational multiplication, and
`primeToFiniteAdeleModule_scalarTower` gives its scalar tower over `ℚ`.

`primeToFiniteAdeleAction_integral_tmul` proves

\[
e_0(a)(r\otimes x)=r\otimes(a\cdot x).
\]

Here the right side uses the actual compatible away residue action on the
integral limit. The proof uses the comparison formula at `1 ⊗ a`, cancellation
of `e` against its inverse, and the published tensor-action formula.

`rationalRestrictAway_finiteAdeleAction` is the full-to-away compatibility
identity for every full finite adele `a` and every full rational Tate element
`x`:

\[
\mathrm{res}_T(a\cdot x)=\mathrm{res}_{\mathbb A}(a)\cdot\mathrm{res}_T(x).
\]

The full action uses `h`; the away action uses `hAway`. The proof rewrites to
the existing compatibility of residue actions and the inverse comparison
square above. In particular, the two actions are not transported through
unrelated witnesses. `rationalMap_primeToFiniteAdeleAction` proves that the
map induced by an actual group-scheme homomorphism preserves this action,
using the published away residue scalar compatibility.

## Abelian schemes, rational homomorphisms and endomorphism algebras

The `AbelianScheme.Tate` namespace specializes the action and module structure
to `A.toGrp` for an actual abelian scheme `A/S`. The geometric-fibre case uses
`T = Over.mk s`, as in the imported torsion-section construction. No rank,
finiteness or characteristic hypothesis is needed for these algebraic maps.

`rationalHomMap_primeToFiniteAdeleAction` extends scalar compatibility to
`Rationalization.Hom A B = ℚ ⊗[ℤ] (A ⟶ B)`. Its proof uses tensor induction
in the rational homomorphism; the pure-tensor case follows from actual
homomorphism compatibility and rational linearity. `primeToFiniteAdeleHomMap`
bundles precisely that existing rational Tate map as linear over
`PrimeToFiniteAdeles m`. Its application, identity, composition and addition
laws follow by extensionality from the corresponding rational-map laws.
Composition sends `f` followed by `g` to the map for `g` composed with the map
for `f`.

`rationalEndAction_primeTo_commute` shows that actual rational endomorphisms
commute with this scalar action. For a possibly noncommutative rational
algebra `D` and `i : D →ₐ[ℚ] Rationalization.End A`,
`primeToFiniteAdeleAlgebraAction` uses that commutation and the tensor-product
universal property to construct

\[
D\otimes_{\mathbb Q}\mathbb A_f^{\,m}
 \longrightarrow \operatorname{End}_{\mathbb Q}(V^mA).
\]

Its pure-tensor formula first applies the adelic action of `a`, then the
rational endomorphism action of `i(d)`. `primeToFiniteAdeleAlgebraModule`
provides the resulting module structure for local installation. Neither
faithfulness of `i` nor faithfulness of the resulting action is asserted.

## Provenance and remaining obligations

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (PDF p.26), defines the away Tate limit and its
rationalization. Section III.1, printed p.92 (PDF p.100), uses
`B ⊗_ℚ A_f^p`-linear isomorphisms to the away rational Tate module in the
prime-to-p level condition. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The action transport and compatibility proofs here are derived formal
implementations of that convention using `RationalScalars`, the actual away
residue action and the explicit normalized comparison. The arbitrary test
scheme, group-scheme generality and natural-modulus extension are internal.
The carrier stays `ℚ ⊗[ℤ] T^mA`; there is no tensoring of `T^mA` over `ℤ` with
finite adeles.

The scalar comparisons are explicit hypotheses of this module. They are proved
by the published theorems named above, which this module neither imports nor
applies. No independence of comparison witnesses, rational topology,
continuity of these actions, restricted-product comparison of Tate modules,
monodromy, Weil pairing or PEL orbit construction is established here. This
focused action construction does not complete the parent PEL task.
