# Actual rational and adelic Tate transport along geometric paths

Author: Worker 142.

This module extends the actual integral path transport to rational Tate modules
and bundles it over the existing full and away finite-adelic scalar rings and
PEL tensor algebras. It proves the path identities, monodromy conjugation,
change-of-path formula and naturality for actual rational homomorphisms.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26; Section III.1, printed pp.91–92 /
  PDF pp.99–100. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 defines the full and away rational Tate modules by rationalizing the
  integral limits, and defines rational homomorphisms and endomorphisms.
  Pages 91–92 use the endomorphism/adelic tensor actions and geometric monodromy
  in the level conditions. Page 91 discusses independence of the geometric
  point, for which this module supplies a path-dependent intermediate map.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154, and (10.29), printed p.151 / PDF p.155. Registered source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  These passages define the finite étale fibre functor and its automorphism
  group, and describe noncanonical change of geometric base point.

The cited passages were read directly through local PDF text extraction.
No source-specific errata directory was available in the supplied Library.
The contribution is **derived**: rational scalar extension of the imported
integral path map gives the constructed equivalence; tensor induction carries
its intrinsic laws to rational Tate modules. The existing scalar actions then
give the adelic bundles. The generalized selected-index, conditional API is
internal infrastructure, not a claim that the sources state this exact API.
No restricted-product comparison is used.

## Actual objects and retained hypotheses

All declarations are in `Langlands.AbelianScheme.Tate`. Fix an actual abelian
scheme `A` over `S`, field-valued points `s` and `t`, and proofs

```lean
hs : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
ht : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber t Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
p : FiniteEtale.fiberFunctor s hs ≅ FiniteEtale.fiberFunctor t ht
```

The fields may differ but belong to the same universe as the schemes. The
path is an actual natural isomorphism of the existing finite fibre functors,
not a supplied equivalence of Tate modules. `Index P` contains precisely the
positive orders satisfying `P`. No directedness condition on `P` is needed.
The source and target are the existing carriers
`Rational A (Over.mk s) P = ℚ ⊗[ℤ] Integral A (Over.mk s) P` and its counterpart
at `t`. The integral modules are coherent families of actual torsion points.

For the intended geometric application, the fields are algebraically closed
and `S` is connected and locally noetherian. This conditional construction
requires only the displayed inputs; it proves neither existence of the path
nor the geometric Galois-category or finite-etaleness theorem.

## Rational transport and path laws

`rationalTransportMap` is `LinearMap.baseChange ℚ` applied to
`integralTransportHom`, viewed as an integer-linear map. Its tensor formula is

```text
T_p(a ⊗ x) = a ⊗ integralTransport(p)(x).
```

`rationalTransportMap_refl` and `rationalTransportMap_trans` use tensor
induction and the corresponding integral formulas to prove identity transport
and `T_(p ≪≫ q) = T_q ∘ T_p`. The sum cases use additivity.
`rationalTransport` bundles the map as a rational linear equivalence, taking
transport along `p.symm` as inverse. The inverse proofs combine the composition
formula with the natural-isomorphism identities. The `_apply`, `_tmul`,
`_refl`, `_trans` and `_symm` lemmas expose these same maps and laws.

`rationalTransport_aut` identifies transport along a loop with the published
`rationalMonodromy`, by definitional equality. `toRational_transport` states
that the existing map from integral to rational Tate modules commutes with
transport. Its proof is the tensor formula at scalar 1; it makes no assertion
of injectivity.

`rationalTransport_monodromy` and `rationalTransport_change_path` prove

```text
T_p(ρ_s(g)(v)) = ρ_t(pathConjugation(p)(g))(T_p(v)),
T_q(v) = ρ_t(p.symm ≪≫ q)(T_p(v)).
```

Here path conjugation is the existing map with underlying function
`g ↦ p ∘ g ∘ p⁻¹`, and `p.symm ≪≫ q` is the target loop with underlying
function `q ∘ p⁻¹`. Tensor induction reduces both equations to their integral
counterparts. The second equation records dependence on the path; it does not
identify arbitrary transports.

## Naturality and endomorphism actions

`rationalTransport_map` proves the square between transport for `A` and `B`
and the rational Tate maps of an actual homomorphism `f : A ⟶ B`.
Tensor induction reduces it to `integralTransport_map`.
`rationalTransport_homMap` proves the same square for every
`f : Rationalization.Hom A B`: tensor induction in `f` reduces it to the
previous result and rational linearity. `rationalTransport_iso` specializes
to an invertible rational homomorphism and the existing `rationalIso`.

`rationalTransport_endAction` specializes this to rational endomorphisms.
`rationalTransport_algebraAction` specializes further along
`i : D →ₐ[ℚ] Rationalization.End A`. Thus the same actual endomorphism algebra
acts at both points and transport intertwines those two actions.

## Full residue and finite-adelic linearity

`rationalTransport_scalarAction` preserves the existing action of
`ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`. It follows from
`TateScalarExtension.map_action` applied to the imported
`integralTransportLinearEquiv`. For finite adeles the explicit additional input is

```lean
h : Global.RationalProfiniteIntegerAdeleComparison
```

`rationalTransport_finiteAdeleAction` uses the existing scalar action, obtained
from the witnesses chosen under this same `h` at both endpoints.
`finiteAdeleTransport` bundles the same function as a linear equivalence over
`Global.FiniteAdeles ℚ`, locally installing `finiteAdeleModule` at each point.
Its application lemma identifies it with `rationalTransport`.

`rationalTransport_finiteAdeleAlgebraAction` proves compatibility with the
existing action of `D ⊗[ℚ] Global.FiniteAdeles ℚ` induced by `i`. Tensor induction
in this algebra reduces the result to endomorphism compatibility and the
finite-adelic scalar law. `finiteAdeleAlgebraTransport` bundles the same
equivalence over this tensor algebra, with the existing module instances at
both points; its application lemma again identifies the underlying function.
The construction introduces neither a new scalar identification nor a tensor
product of the integral Tate carrier over the integers with finite adeles.

## Full and away specialization

`rationalFullTransport` selects every positive order.
`rationalAwayTransport m` selects positive orders coprime to `m`. Full transport
requires all positive orders invertible on the base; away transport requires
only the selected orders invertible. Prime `m` gives the usual prime-to-prime
case; positive composite `m` excludes its prime divisors. The formal case `m = 0`
is allowed by the predicate without a usual prime-to-prime interpretation.

`rationalRestrictAway_transport` proves compatibility with the existing
rational full-to-away restriction, restricting the same full invertibility
proof to the away indices. Tensor induction reduces its pure tensor case to
definitional equality of the selected coordinates.

`rationalAwayTransport_scalarAction` applies `TateScalarExtension.map_action`
to `awayTransportLinearEquiv` for the rationalized away residue ring. The
away finite-adelic constructions additionally retain the coupled proposition

```lean
hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

`rationalAwayTransport_primeToFiniteAdeleAction` then preserves the existing
away finite-adelic action.
`primeToFiniteAdeleTransport` bundles that same equivalence over
`Global.PrimeToFiniteAdeles m`.
`rationalAwayTransport_primeToFiniteAdeleAlgebraAction` and
`primeToFiniteAdeleAlgebraTransport` give the corresponding compatibility and
linear equivalence for `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`.
The proofs use the same tensor induction as in the full case, and the two
application lemmas identify the underlying functions with
`rationalAwayTransport`. Both endpoints use the same `hAway`, coupled to `h`;
no independence of scalar-comparison witnesses is asserted.

## Remaining scope

The module constructs algebraic equivalences. It does not provide rational or
adelic topology or continuity. Path existence, prime-adic transport and
restricted-product comparisons remain separate. It also does not construct
Weil pairings, transport a Tate-twist trivialization, or prove preservation of
a polarization pairing. The change-of-path law is a prerequisite for
independence of fixed level orbits, which remains to be established before
claiming a canonical unpointed level functor. Pointed base change is separate.
