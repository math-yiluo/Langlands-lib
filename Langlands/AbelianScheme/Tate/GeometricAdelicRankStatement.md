# Freeness of actual full and away Tate modules at geometric points

`Langlands.AbelianScheme.Tate.GeometricAdelicRankStatement` is a
proposition-valued definition. It states freeness assertions for the actual
Tate modules and supplies no proof.

Let `S` be a scheme, `A : AbelianScheme S`, and `g : ℕ`, with
`A.HasRelativeDimension g`. This is the existing predicate
`SmoothOfRelativeDimension g A.X.hom`. The statement has two parts.

- If every positive integer is a unit in `Γ(S, ⊤)`, then at every
  algebraically closed field-valued point `s : Spec Ω ⟶ S`, there exists a
  `Global.ProfiniteIntegerRing`-linear equivalence from
  `Fin (2 * g) → Global.ProfiniteIntegerRing` to `FullAt A s`.
  For every `h : Global.RationalProfiniteIntegerAdeleComparison`, there also
  exists a `Global.FiniteAdeles ℚ`-linear equivalence from
  `Fin (2 * g) → Global.FiniteAdeles ℚ` to `RationalFullAt A s`, using
  `finiteAdeleModule A (Over.mk s) (fun _ => True) h`.
- For every natural modulus `m`, if every positive integer coprime to `m`
  is a unit in `Γ(S, ⊤)`, then at every such point there exists a
  `Global.PrimeToProfiniteIntegerRing m`-linear equivalence from the
  corresponding `Fin (2 * g)` power to `AwayAt A s m`. For every `h` as
  above and
  `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
  there also exists a `Global.PrimeToFiniteAdeles m`-linear equivalence
  from its `Fin (2 * g)` power to `RationalAwayAt A s m`, using
  `primeToFiniteAdeleModule A (Over.mk s) hAway`.

All equivalences are existential, expressed by `Nonempty`. The field `Ω`
is in the scheme's universe. No connectedness or local noetherianity of
`S` is assumed.

## Actual inverse limits and scalar structures

The targets are the published modules from
[`AbelianScheme`](AbelianScheme.md) and [`Rational`](Rational.md).
Their finite levels are actual multiplication-kernel sections of `A`
over `Over.mk s`, with transition `[M/N]` when `N` divides `M`.
The full limit retains all positive levels; the away limit retains those
coprime to `m`. The inverse-limit groups carry the existing residue-defined
actions from [`Scalars`](Scalars.md).

The rational modules are `ℚ ⊗[ℤ] FullAt A s` and
`ℚ ⊗[ℤ] AwayAt A s m`. The tensor factors are reversed from
Harris–Taylor's convention over the commutative ring `ℤ`; the published
`rationalTensorComm` provides the comparison. The adelic actions are the
existing actions from [`RationalScalars`](RationalScalars.md) and
[`AwayRationalScalars`](AwayRationalScalars.md). The explicit `h` and
`hAway` parameters select the scalar comparisons used by those actions.
They do not contain a basis or rank assertion about `A`. These scalar
comparison propositions have separate published proofs in
`Langlands.Global.RationalProfiniteIntegerComparisonProof` and
`Langlands.Global.PrimeToRationalProfiniteIntegerComparisonProof`.

Freeness is expressed by equivalence to a standard finite free module
over each specified ring. The statement uses no finite-dimensional
vector-space terminology for the adelic rings. The inverse limit is
not tensored over `ℤ` with the finite adeles.

## Sources and derived formulation

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 (PDF p.26), defines the full Tate module
using all positive torsion orders, its rationalization over `ℤ`, and
the variants away from a finite set of primes. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
That original page was read directly, including its rendered formulas.
It supplies the conventions for the modules, rather than a theorem
stating all four freeness conclusions here.

The rank input is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, Chapter X (10.1)–(10.3), printed
pp.141–142 (PDF pp.145–146). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These original pages were read directly. They work over a field and
give noncanonical prime-adic integral rank `2g` and rational dimension
`2g` away from the characteristic. No source-specific errata file was
present in the available Library.

This target is derived from that local rank theorem, primary
decomposition, and rationalization of finite free modules. It is not
quoted as an arbitrary-base theorem from either source. At each
geometric point the actual pullback of `A` has the specified dimension,
and the selected base units remain units in the point field. A proof
must justify these specializations and their compatibility with the
actual torsion-section inverse systems and scalar actions. The
published prime-adic rank target
`Langlands.AbelianScheme.Tate.PrimeAdic.GeometricPrimeAdicRankStatement`
isolates the local rank input.

The integral prime-product and rational restricted-product
decompositions, both full and away, are separate published additive
comparison targets, with proof modules
`Langlands.AbelianScheme.Tate.PrimeComparisonProof` and
`Langlands.AbelianScheme.Tate.RestrictedProductProof`. Their additive
equivalences do not by their types supply the scalar-linear
equivalences asserted here. A proof must establish the required
compatibility with the residue scalar actions, assemble local free
modules into a free module over the appropriate profinite scalar
ring, and verify rationalization against the specified adelic actions.
Neither a compatible basis nor any geometric comparison is assumed
as input to this target.

## Scope and boundary cases

The full assertion applies in particular over a characteristic-zero
field. The away assertion permits characteristic dividing `m`,
provided all selected orders are invertible on the base.
The theorem includes `g = 0`. For `m = 1` all positive levels are
retained. For `m = 0` only level `1` is retained, and the away scalar
rings and Tate modules are zero; the stated equivalences remain
meaningful. No uniqueness of a numerical rank over the zero ring is
claimed.

This is an algebraic existence target. It chooses no basis and
asserts no continuity or monodromy compatibility of an equivalence,
no relative scheme trivialization, and no trivialization of a Weil
pairing or of a Tate twist. Finite étaleness of the actual torsion
schemes, finite-level geometric rank, and the canonical
restricted-product comparison are not additional conclusions of
this target.
