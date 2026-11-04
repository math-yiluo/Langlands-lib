# Naturality of the standard integral

## Source and scope

The source motivation is J.-L. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)*, IV.1, printed p.277
(PDF p.43), DOI 10.1017/S1474748003000082. The displayed square requires
operator families to be compatible with isomorphisms of the inducing
representation. The standard integral is defined on printed pp.277–278
(PDF pp.43–44) by scalar absolute convergence against the smooth dual
and existence of a representing vector.

This module derives that compatibility for the actual restricted standard
integral constructed in `StandardIntertwiningIntegral`. It proves more
generally preservation of the actual integration domain and commutation
with the integral for every Levi intertwiner, and exact identification of
domains for every inducing isomorphism. These are internal deductions from
the actual function model and smooth-dual weak integration, rather than a
separate source theorem with these general hypotheses.

The output remains a function on `G` on the actual domain of the integral.
The module does not establish target Levi covariance, membership in a
target induced representation, convergence on the whole source, or
rational continuation. Thus the isomorphism square proved here is the
restricted, function-valued version of the source compatibility condition,
not its application to an already completed rational operator family.

## Objects and assumptions

The ambient group `G` is locally compact and nonarchimedean. Actual
subgroups `P`, `M`, `U` have an `IsSemidirectDecomposition P M U`, and
`U` is closed. `U'` is an arbitrary subgroup. The quotient is literally
`LeftQuotient (U.subgroupOf U')`, equipped with an arbitrary measurable
structure and measure `ν`. No normality or measure invariance is required
by these naturality arguments.

`A` and `B` are canonical complex `SmoothRep` objects of `M`. Their carrier
universes `uV` and `uW` are independent of each other and of the group
universe `uG`. The source induced representations use exactly
`DynamicNormalization.leviTwistedInductionFunctor h hU`: twist on the
Levi by its positive Haar half-character, then inflate and induce.
Admissibility, irreducibility and radical unimodularity are not hypotheses.

The induced maps, integral relation, domain map, domain membership
equivalence and domain representation equivalence require no closedness
of `M`. The two selected-operator identities additionally assume `M` is
closed, as in the imported construction. This supplies compact-open
cofinality and smooth-dual separation for uniqueness. No topology or
completeness of the representation carriers is introduced.

## Actual induced map and preservation of the domain

For `T : A.representation.IntertwiningMap B.representation`,
`inducedMap` first uses the actual twist intertwiner for the same positive
half-character on both sides, pulls it through the Levi projection, and
applies `smoothInducedMap`. Its underlying linear map is pointwise
postcomposition:

```text
(inducedMap T f)(g) = T(f(g)).
```

`inducedMap_eval` records this exact identity. It constructs the map
directly, allowing distinct carrier universes even where a single
categorical induction functor fixes one carrier universe.

`integrand_map` proves that postcomposition commutes with descent to the
actual quotient. The proof is quotient induction followed by the
pointwise identity on representatives.

`HasIntegral.map_induced` applies
`SmoothWeakIntegral.HasIntegral.map` at every `g`. A smooth functional
on `B` pulls back along `T` to a smooth functional on `A`; consequently
both scalar absolute integrability and the representing-vector equality
are preserved. The new representing function is `g ↦ T(Jf(g))`.

`inducedMap_mem_domain` uses the imported `mem_domain` equivalence to
turn this representing function into actual domain membership.
`domainMap` restricts the induced linear map to these domains. Its
equivariance is inherited from the original induced intertwiner, after
one subtype extensionality step; it is an actual intertwiner of the
domain subrepresentations. `domainMap_val` identifies its underlying
source vector.

## Operator naturality and inducing isomorphisms

`operator_map` applies preservation of the weak integral to the selected
operator's specification. Uniqueness in the target carrier then proves,
for every domain element `f`,

```text
operator_B(domainMap T f)(g) = T(operator_A(f)(g)).
```

This argument proves naturality on the whole actual domain for any
intertwiner; it assumes no convergence result on other vectors.

For an inducing representation equivalence `e`,
`inducedEquiv_mem_domain_iff` applies domain preservation to both `e` and
`e.symm`. The composite induced maps cancel pointwise by
`e.symm_apply_apply`. Thus the domain is exactly transported, rather than
merely mapped into the second domain.

`domainEquiv` packages the restricted maps for `e` and `e.symm` as an
equivariant linear equivalence of the actual domain subrepresentations.
Its two inverse laws reduce through the three subtype layers (domain,
smooth vector and covariant function) to the inverse laws on the original
carriers. `operator_domainEquiv` specializes `operator_map` to this
equivalence. It proves the commutative change-of-representative square on
the entire actual domain, with the codomain map given by pointwise `e`.
