# Actual full and away adelic geometric Tate representations

Author: Worker 142.

This module constructs full and away finite-adelic representations of the actual
geometric-fibre automorphism group on the rational Tate modules of an actual
abelian scheme. It also specializes the tensor-linear representations used by
PEL levels, proves joint continuity of all four evaluations, and proves that the
actual integral images are invariant, compact and open. The geometric fibre
finiteness and torsion finite etaleness needed by the underlying constructions
are supplied by published proofs.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), printed p.18 / PDF p.26, and Section III.1, printed pp.91–92 /
  PDF pp.99–100. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 specifies the full and away torsion limits, rationalization over the
  integers, and rational endomorphisms. Pages 91–92 use invariant orbits of
  isomorphisms linear over the endomorphism/adelic tensor algebra in the full
  and prime-to-prime level conditions. These are the conventions and the
  application motivating the representations here.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft built
  2012-02-08, Chapter X, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154. Registered source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  These definitions specify the category of actual finite étale covers and its
  geometric-fibre automorphism group. The source calls this the algebraic
  fundamental group for a connected locally noetherian base.

The cited passages were read directly and both fingerprints were checked. No
source-specific errata directory was present in the supplied Library or workspace.
This is a **derived** specialization of the published `Tate.RationalMonodromy`
and `Tate.RationalTopology` implementations. Their original actual actions,
scalar structures and topologies are reused. The new representations bundle the
existing linear equivalences into monoid homomorphisms after supplying
`FiniteEtale.geometricFiberFinite s` and `AbelianScheme.torsionFiniteEtale`.
The continuity and compactness assertions specialize the corresponding named
results from `RationalTopology` with these proved geometric inputs. The sources
are not asserted to state this selected relative Lean API or its topology proofs
verbatim.

## Actual objects and remaining hypotheses

The namespace is `Langlands.AbelianScheme.Tate.Geometric`. Fix a scheme `S`, an
algebraically closed field `Ω` in the same universe, an actual morphism
`s : Spec (.of Ω) ⟶ S`, and `A : AbelianScheme S`. The acting group is exactly

```lean
FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)
```

with its existing evaluation topology. It is the group of natural automorphisms
of the finite-fibre functor on actual finite étale covers. The underlying
finite-level action is evaluation on the actual multiplication-kernel fibres,
and the integral action acts coordinatewise on the actual coherent families.
No arbitrary action or supplied comparison of the Tate carrier with another
module is an input.

The full construction takes

```lean
hunit : ∀ n : GroupScheme.Tate.Index (fun _ => True),
  IsUnit (n.val : Γ(S, ⊤))
h : Langlands.Global.RationalProfiniteIntegerAdeleComparison
```

The away construction takes a natural modulus `m`, invertibility only for
positive orders coprime to `m`, and

```lean
hAway : Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

It requires no full-order invertibility assumption. The comparisons `h` and
`hAway` concern coefficient rings only and are kept explicit. The published
scalar modules choose their witnesses; this module introduces no new scalar
identification and claims no independence from those choices. The compactness
and local compactness results do not require either coefficient comparison.

The full carrier is precisely `RationalFullAt A s`, the existing
`ℚ ⊗[ℤ] FullAt A s`. The away carrier is `RationalAwayAt A s m`, the existing
`ℚ ⊗[ℤ] AwayAt A s m`. The integral carriers are limits of actual torsion
sections, including the positivity condition in `Index`. Tensoring these
integral carriers over the integers with finite adeles is not used.

## Adelic and tensor-linear representations

`finiteAdeleRepresentation` is a monoid homomorphism from the displayed group
into the linear automorphisms of `RationalFullAt A s` over
`Global.FiniteAdeles ℚ`. Its type locally installs exactly
`finiteAdeleModule A (Over.mk s) (fun _ => True) h`. Its function is the published
`finiteAdeleMonodromy`, with the two geometric inputs proved. Its identity and
multiplication fields apply linear-equivalence extensionality to the existing
rational monodromy laws. Thus multiplication has the left-action convention

```text
ρ(g*k)(x) = ρ(g)(ρ(k)(x)).
```

`finiteAdeleRepresentation_apply` identifies the function with the existing
full rational monodromy. `finiteAdeleRepresentation_tmul` gives
`ρ(g)(q ⊗ x) = q ⊗ ρ_integral(g)(x)`. The `toRational` formula specializes this
at `q = 1` and establishes equivariance of the actual integral inclusion.

`awayFiniteAdeleRepresentation` is the analogous homomorphism over
`Global.PrimeToFiniteAdeles m`, locally using exactly `primeToFiniteAdeleModule`
under `hAway`. Its application, pure tensor and integral-inclusion formulas
have the same meaning with the coprime-order system. It uses the away scalar
action rather than identifying it with the full scalar ring. Prime `m` gives
the usual prime-to-prime setting; nonzero composite `m` excludes its prime
divisors. The formal boundary `m = 0` retains only order one, and `m = 1`
retains all positive orders. No uniqueness of numerical rank is inferred in
the zero-ring boundary case.

For a rational algebra `D` and an actual algebra homomorphism
`i : D →ₐ[ℚ] Rationalization.End A`, `finiteAdeleAlgebraRepresentation` and
`awayFiniteAdeleAlgebraRepresentation` specialize the published tensor-linear
representations. Their coefficient rings are respectively
`D ⊗[ℚ] Global.FiniteAdeles ℚ` and `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, with
exactly the existing `finiteAdeleAlgebraModule` and
`primeToFiniteAdeleAlgebraModule` locally installed. The `D` action comes from
actual rational endomorphisms. The two application lemmas identify their
functions with the respective adelic representations. The existing tensor
linearity proof is reused; it is not assumed as an extra hypothesis.

`finiteAdeleRepresentation_restrictAway` proves that the existing rational
full-to-away restriction intertwines the two constructed representations. It
specializes `rationalRestrictAway_monodromy` with the geometry proved. The away
unit witnesses are exactly the restriction of the full witnesses, and both
coefficient comparisons are retained. This is equivariance of the specified
map, not an assertion of linearity over two different scalar rings.

## Topology, integral images and continuity

All topology assertions use the published `rationalTopology`, locally installed
inside this module. On `ℚ ⊗[ℤ] T` this is the final topology for all charts
`x ↦ q ⊗ x`, where `T` has its actual product-subspace topology from discrete
torsion levels. Importing this module installs no global tensor-product
topology. Hausdorffness and the topological additive group properties for full
and away rational carriers are already available from `RationalTopology`.

`continuous_finiteAdeleRepresentation` and
`continuous_awayFiniteAdeleRepresentation` prove joint continuity of
`(g,x) ↦ ρ(g)(x)` on the product of the actual geometric group and the
corresponding rational Tate space. Their proofs are the existing full and
away continuity theorems with geometric finiteness and finite etaleness
supplied. The two `continuous_*AlgebraRepresentation` theorems use exactly the
same functions, so their continuity follows definitionally. No topology on the
whole group of linear automorphisms is introduced or used.

`finiteAdeleRepresentation_mem_integral_iff` and its away counterpart prove
that membership in the range of the actual integral-to-rational map is
invariant under each group element. In one direction the witness is acted on
by integral monodromy. In the other it is acted on by the inverse group element;
the rational linear equivalence's inverse law proves that this gives a witness
for the original point. These proofs use the actual pure tensor formula and
assume no basis or rank theorem.

`Geometric.rationalFull_compactOpen_integral` and
`Geometric.rationalAway_compactOpen_integral` prove that these integral images
are compact and open. The corresponding `rationalFull_locallyCompactSpace`
and `rationalAway_locallyCompactSpace` theorems prove local compactness of the
rational spaces. All four specialize the published topology theorems with
`geometricFiberFinite` and `torsionFiniteEtale`; only the relevant unit
hypothesis remains. Together with the membership equivalences, this gives an
invariant compact open integral image for each representation.

This unit asserts no numerical rank, chosen basis, topological
restricted-product comparison, joint finite-adelic scalar continuity, geometric
Galois-category classification, Weil-pairing or twist trivialization, or
canonical unpointed level functor. Those remain separate mathematical
obligations. The construction applies to arbitrary `S` with the displayed
units; its intended Harris–Taylor application is connected and locally
noetherian. No base-point independence is inferred from the more general
formal scope.
