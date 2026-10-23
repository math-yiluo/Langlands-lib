# Tensor-algebra coherence of actual Tate base change

This module constructs tensor-algebra linear identity and composition comparisons
for the actual Tate modules of pulled-back abelian schemes. It proves their
compatibility with the actual base-change equivalences, retaining the canonical
transport of test schemes in each equation.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 (PDF p.26), defines the full and away rational Tate modules,
rational homomorphisms, and isogenies. Section III.1, printed pp.91–92
(PDF pp.99–100), uses the full and away tensor-algebra module isomorphisms in its
pointed PEL problems. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The constructions here are derived infrastructure for that application.
`AbelianScheme.BaseChangeCoherence` constructs the identity and composition
isomorphisms of actual abelian schemes and proves naturality on their actual
rational Hom groups. `Tate.AdelicTransport` and `Tate.AwayAdelicTransport`
turn intertwining rational isomorphisms into tensor-algebra linear Tate
equivalences. `Tate.BaseChangeCoherence` supplies the underlying Tate equations.
This module combines those constructions; the source is not being cited as a
separate theorem asserting these implementation-level equations.

## Parameters and actions

All declarations are in `Langlands.AbelianScheme.Tate`. Let `A` be an abelian
scheme over `S`, let `b : S' ⟶ S` and `c : S'' ⟶ S'`, and let
`i : D →ₐ[ℚ] End0 A`, where `D` is a possibly noncommutative rational algebra.
Write `b*A` for `(AbelianScheme.baseChange b).obj A`. Its action is the actual
pullback action

```lean
(AbelianScheme.rationalBaseChangeEnd b A).comp i
```

and the action on `c*(b*A)` is the successive composite of these algebra maps.
For any test scheme and predicate `P` on positive torsion orders, the rational
carrier is the existing `Rational = ℚ ⊗[ℤ] Integral`. The full tensor algebra is
`D ⊗[ℚ] Global.FiniteAdeles ℚ`. The same explicit hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison` supplies the scalar
comparison at every endpoint.

The away carrier specializes to orders `n` with `Nat.Coprime n m`, for a natural
number `m`. It uses the coefficient ring
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m` and the same coupled hypothesis
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` throughout.
For prime `m = p` this is the prime-to-p specialization. The hypotheses and
their chosen witnesses remain explicit; witness independence is not asserted.

## Intertwining and linear comparisons

Let `j_A : id*A ≅ A` and `k_A : (c ≫ b)*A ≅ c*(b*A)` denote the constructed
abelian-scheme comparisons, and use their images in the rational category.
`baseChangeId_intertwines` and `baseChangeComp_intertwines` prove

\[
j_A\circ (\mathrm{id}^*i)(d)=i(d)\circ j_A,\qquad
k_A\circ ((c\mathbin{\gg}b)^*i)(d)
   =(c^*(b^*i))(d)\circ k_A.
\]

Here `Rationalization.comp f g` means first `f`, then `g`. The proofs specialize
the established rational-Hom naturality equations to `i d`. Thus the
intertwining equations are proved for the constructed pullback actions.

`finiteAdeleAlgebraBaseChangeId A i h T P` is the resulting linear equivalence
from the Tate module of `id*A` at `T` to that of `A` at `T`.
`finiteAdeleAlgebraBaseChangeComp A i h b c T P` goes from the Tate module of
`(c ≫ b)*A` to that of `c*(b*A)`, both evaluated at `T : Over S''`.
They are obtained by applying `finiteAdeleAlgebraIso` to the rational images
of `j_A` and `k_A` and the proved intertwining equations.

Their `_apply` lemmas identify their underlying functions with `rationalMap`
of the actual integral comparison homomorphisms. The composition comparison's
`_symm_apply` lemma identifies its inverse with `rationalMap` of `k_A.inv`.
Each proof reduces `rationalHomMap` on the coefficient-one inclusion of an
integral homomorphism using `rationalHomMap_ofHom`.

The corresponding `primeToFiniteAdeleAlgebraBaseChangeId` and
`primeToFiniteAdeleAlgebraBaseChangeComp` use `primeToFiniteAdeleAlgebraIso`
and the same intertwining lemmas. Their application and inverse-application
formulas use `rationalMap` with the coprimality predicate.

## Identity and composition equations

Write `β_b` for the existing tensor-linear Tate base-change equivalence
`finiteAdeleAlgebraBaseChange b`. It maps Tate vectors of `b*A` at `T` to
vectors of `A` at `(Over.map b).obj T`.

`finiteAdeleAlgebraBaseChange_id` states that applying `β_id` and then
`rationalTestRestrict` along `(Over.mapId S).inv.app T` equals the newly
constructed linear comparison induced by `j_A`. The restriction explicitly
identifies the mapped test scheme with `T`.

For a vector `x` in the Tate module of `c*(b*A)` at `T`,
`finiteAdeleAlgebraBaseChange_base_comp` states

\[
\beta_b(\beta_c(x))
 = r_{\alpha_T}\bigl(\beta_{c\mathbin{\gg}b}
       (V(k_A)^{-1}(x))\bigr),
\qquad
\alpha_T=(\mathrm{Over.mapComp}\ c\ b)^{-1}_T.
\]

The left-hand `β_b` is evaluated at `(Over.map c).obj T`. The right-hand
restriction `r` is `rationalTestRestrict`, carrying the directly mapped test
scheme to the successively mapped test scheme. The inverse comparison on
vectors has the required direction from successive to direct pullback.
Both proofs rewrite the application formulas and apply the generic rational
Tate coherence equations for `A.toGrp`.

`primeToFiniteAdeleAlgebraBaseChange_id` and
`primeToFiniteAdeleAlgebraBaseChange_base_comp` prove exactly the corresponding
away equations by the same method, with the same test-scheme transports.

## Scope

The schemes, base morphisms and test schemes are arbitrary in one universe.
No torsion-order invertibility, finite-etaleness, dimension, faithfulness or
geometric-point hypothesis is required for these algebraic comparisons.
The full Tate specialization uses `P n = True`; the away construction uses
coprimality before rationalization. Field-valued test schemes give the
corresponding pointed algebraic equations.

This unit establishes tensor-algebra linear comparisons and pointwise identity
and binary composition laws. It does not assert separate triangle or pentagon
laws, rational topology, geometric monodromy comparison, Weil-pairing
compatibility, invariant-orbit base change or independence of a geometric base
point. These remain separate mathematical obligations.
