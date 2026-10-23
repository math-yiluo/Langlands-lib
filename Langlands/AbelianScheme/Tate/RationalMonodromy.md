# Actual geometric monodromy on rational and adelic Tate modules

Author: Worker 142.

This module extends the actual integral geometric action to the existing
rational Tate module. It proves equivariance for actual homomorphisms, rational
homomorphisms, rational isomorphisms, and rational endomorphisms. It constructs
the resulting full and away adelic linear automorphisms and representations
over the tensor algebras used by PEL level structures.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26, and Section III.1, printed
  pp.91–92 / PDF pp.99–100. Registered source:
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 defines the rational full and away Tate modules by rationalizing the
  respective integral limits, as well as rational homomorphisms and
  endomorphisms. Pages 91–92 use the geometric monodromy action and the
  endomorphism/adelic tensor algebra in the full and prime-to-prime level
  conditions.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154. Registered source:
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  These definitions identify the finite étale geometric-fibre functor and its
  automorphism group, which acts in this module.

These passages were read directly; no source-specific errata directory was
present in the available Library. The contribution is **derived**: it applies
rational scalar extension to the imported actual integral monodromy and uses
the existing residue/adelic scalar actions and rational homomorphism maps.
The generalized selected-index API and its proofs are not asserted to occur
verbatim in the sources. It supplies the algebraic monodromy prerequisite for
the cited invariant-orbit conditions, rather than a construction of those
conditions or their Weil pairings.

## Carriers and explicit hypotheses

The namespace is `Langlands.AbelianScheme.Tate`. Fix a scheme `S`, a field `Ω`,
a point `s : Spec (.of Ω) ⟶ S`, and an actual abelian scheme `A : AbelianScheme S`.
The following hypotheses remain explicit:

```lean
hfin : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
```

The acting group is the existing `FiniteEtale.FundamentalGroup s hfin`,
the natural automorphism group of the actual finite-fibre functor.
`integralMonodromy` acts by evaluation on the actual torsion-kernel fibres.
The carrier used here is exactly the existing
`Rational A (Over.mk s) P = ℚ ⊗[ℤ] Integral A (Over.mk s) P`.
It does not tensor the integral Tate carrier over the integers with the finite
adeles, replace it by a supplied module, or identify it with a restricted
product.

The intended geometric application has algebraically closed `Ω` and a connected,
locally noetherian base. The conditional algebraic construction requires no
additional assumptions once the displayed hypotheses are supplied. This broader
formal scope is not a geometric classification assertion. For the full action,
every positive order must be invertible on the base. The away action requires
invertibility only of the positive orders coprime to its modulus.

## Rational action and its laws

`rationalMonodromyMap` is `LinearMap.baseChange ℚ` applied to the integral
monodromy homomorphism viewed as an integer-linear map. Its pure tensor formula
`rationalMonodromyMap_tmul` is

```text
ρ_Q(g)(q ⊗ x) = q ⊗ ρ_Z(g)(x).
```

`rationalMonodromyMap_one` and `rationalMonodromyMap_mul` prove the left-action
identities

```text
ρ_Q(1)(v) = v,           ρ_Q(g*k)(v) = ρ_Q(g)(ρ_Q(k)(v)).
```

The implemented proofs use tensor induction. On pure tensors they reduce to the
corresponding integral action laws; additivity proves the sum cases.
`rationalMonodromy` bundles this as a rational linear equivalence, using the map
for `g⁻¹` as inverse. Both inverse laws follow from the displayed group laws.
`rationalMonodromy_apply` identifies the underlying map.
`rationalMonodromyAction` is a locally installable `DistribMulAction`; it installs
no global group action. `rationalMonodromyRepresentation` bundles the same action
as a group homomorphism into rational linear automorphisms, with multiplication
given by composition in the displayed order.

`toRational_monodromy` states equivariance of the existing integral-to-rational
map, by its pure tensor formula at `q = 1`. It does not assert injectivity of
that map or supply an integral lattice theorem.

## Actual homomorphism and endomorphism equivariance

`rationalMonodromy_map` proves equivariance for the existing rational Tate map of
an actual abelian-scheme homomorphism `f : A ⟶ B`. Tensor induction reduces it to
`integralMonodromy_map`. `rationalMonodromy_homMap` extends this to every element
of the existing `Rationalization.Hom A B`: induction on the rationalized
homomorphism reduces a pure tensor `q ⊗ f` to rational linearity and the preceding
theorem. No new equivariance assumption on the homomorphism is supplied.

`rationalMonodromy_iso` specializes this to the existing `rationalIso` of an
invertible rational homomorphism. `rationalMonodromy_endAction` specializes to
the existing action of `Rationalization.End A`, and
`rationalMonodromy_algebraAction` specializes further along any rational algebra
homomorphism `i : D →ₐ[ℚ] Rationalization.End A`. Thus the action of `D` comes
from actual rational endomorphisms. These results hold for every selected
predicate, including the full and away predicates.

## Full residue and adelic compatibility

`rationalMonodromy_scalarAction` proves compatibility with the existing action
of `ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`. Its proof applies the published
`TateScalarExtension.map_action` to `integralMonodromyLinearEquiv`. The
finite-adelic part additionally takes the explicit named proposition

```lean
h : Global.RationalProfiniteIntegerAdeleComparison
```

The module uses the existing action obtained from the witnesses chosen by the
published scalar construction under `h`. It neither proves this comparison nor
introduces a new identification. `rationalMonodromy_finiteAdeleAction` follows
by substituting the inverse scalar comparison into the residue-scalar law.
`finiteAdeleMonodromy` bundles that same map as a linear equivalence for exactly
the existing locally installed `finiteAdeleModule`. Its application formula
identifies it with `rationalMonodromy`.

`rationalMonodromy_finiteAdeleAlgebraAction` proves preservation of the existing
action of `D ⊗[ℚ] Global.FiniteAdeles ℚ` induced by `i`. Tensor induction reduces
this to commuting with the actual rational endomorphism action and with the
finite-adelic scalar action. `finiteAdeleAlgebraMonodromy` bundles the same
automorphism as linear over this tensor algebra. Its application lemma
identifies its function, and `finiteAdeleAlgebraMonodromyRepresentation` packages
the identity and multiplication laws as a group homomorphism into these
tensor-linear automorphisms. The latter laws are exactly the rational action
laws, verified by extensionality.

## Full and away specializations

`rationalFullMonodromy` uses `P(n) = True`. `rationalAwayMonodromy m` uses
`P(n) = Nat.Coprime n m`. The usual prime-to-prime setting takes prime `m`;
nonzero composite `m` excludes its prime divisors. The formal case `m = 0`
is permitted by the predicate without claiming that it is a usual
prime-to-prime setting.

`rationalRestrictAway_monodromy` proves equivariance of the existing rational
full-to-away restriction. The away invertibility proof is the restriction of
the full one. Tensor induction reduces the result to a definitional equality
on pure tensors: both sides read the same selected coordinates.

`rationalAwayMonodromy_scalarAction` uses `awayMonodromyLinearEquiv` and
`TateScalarExtension.map_action` to prove preservation of the rationalized away
residue action. For away finite adeles, the additional hypothesis is

```lean
hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

It is coupled to the same full comparison `h`, as in the existing away scalar
module. `rationalAwayMonodromy_primeToFiniteAdeleAction` substitutes its inverse
scalar comparison into the away residue law. `primeToFiniteAdeleMonodromy`
bundles the resulting away-adelic linear equivalence; its application lemma
identifies its function with the rational away action.

`rationalAwayMonodromy_primeToFiniteAdeleAlgebraAction`,
`primeToFiniteAdeleAlgebraMonodromy`, its application lemma, and
`primeToFiniteAdeleAlgebraMonodromyRepresentation` give the corresponding
tensor-algebra compatibility, linear automorphism, and group homomorphism for
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`. Their proofs repeat the full tensor
induction and extensionality arguments with the published away scalar action.
No independence of the chosen scalar-comparison witnesses is asserted.

## Scope still to be supplied

This module is algebraic. It does not put a topology on the rational Tate
carrier or prove joint continuity of rational/adelic monodromy. The existing
integral action is continuous; extending that statement to a specified rational
or adelic topology is a separate obligation. Prime-power comparisons and
restricted-product comparisons, the geometric hypotheses above, actual Weil
pairings, pointed base change, base-point independence, and invariant-orbit PEL
level structures are also not established by this unit.
