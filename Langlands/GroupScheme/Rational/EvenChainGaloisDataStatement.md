# Statement: Galois-stable even-path pattern products

`Langlands.GroupScheme.EvenChainGaloisDataStatement.{u}` is a `Prop`-valued
definition, not a proof. Provenance: derived. Worker 175 wrote the interface
in the shared draft for Task 5324 (`dae9b3ff-3319-4226-a421-ef1462af985a`);
Worker 162 checked the originals and completed this documentation.

## Exact statement

In one arbitrary universe `u`, the proposition quantifies over fields
`k,K : Type u` with `[Algebra k K]`, `[FiniteDimensional k K]` and
`[IsGalois k K]`, and an actual group scheme `G` over `Spec k` with affine
structure morphism. Affineness of its actual base change `G_K` is inferred
from the pullback.

For every supplied `D : PairingCompatiblePinningData k K G`, it asserts
existence of `J : Type u`, a `Fintype J` instance,
`C : D.pinning.EvenChainData J`, `r,q : ℕ`, `o : Fin r ≃ J` and
`e : Fin q ≃ C.Rest`, such that `C.IsMiddleOut e` and for every
`σ : K ≃ₐ[k] K` and
`g : rationalPoints (GaloisPointComparison.baseChanged k K G)`, membership

`g ∈ C.patternSet D.rootMaps (canonicalSimpleReflectionRepresentatives D.rootMaps) o e`

implies membership of `GaloisPointComparison.rationalConjugate k K G σ g`
in the same set. Lean uses the fully qualified
`SplitPinning.canonicalSimpleReflectionRepresentatives`.

The published `PairingCompatiblePinningData` includes a split pinning of
`G_K`, a descended torus and inclusion, compatible ordinary Galois actions
on simple roots and pinning vectors, and normalized whole root maps
`D.rootMaps` transported by the action. Pairing compatibility extends the
simple-root action to permutations of all roots preserving the integral
pairing. These data are supplied, not constructed by the statement.

The existential `C` includes even path components, middle-pair merged-root
data and the rational root-generated condition on each merged
representative. Both patterns contribute to one image set. The conclusion
uses the published semilinear coefficient action on actual rational points
of the base change. It asserts setwise stability, not fixedness of every
point, and makes no separate claim about individual patterns, coordinate
families or a scheme structure on the set.

No perfectness, infinitude, characteristic or simple-connectedness premise
is imposed. Connected reductivity and the split pinning over `K` are
included in the supplied data.

## Sources and derived provenance

Robert Steinberg, *Regular elements of semi-simple algebraic groups*,
Publ. Math. IHÉS 25 (1965), 49–80, source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
PDF page numbers are printed page numbers minus 47.

The cocycle conditions and Hilbert 90 argument in 9.3, printed p.72
(PDF p.25), produce rational rank-one reflection choices. The proof of 9.4,
pp.72–73 (PDF pp.25–26), puts Galois orbits together, constructs factors
over orbit-stabilizer fields and uses commutation in orthogonal orbits.
The notation before 9.11 and Theorem 9.11, p.74 (PDF p.27), specify the
middle pair, merged root, modified products and several-component product.
Lemmas 9.12–9.19, pp.75–77 (PDF pp.28–30), study those products. For
stability, the final paragraph on p.77 proves 9.7(e): reduce to one
component, choose the merged factor using 9.3, and use Hilbert 90 to choose
nonidentity simple-root points with rational class modulo the merged root
subgroup.

This is a derived finite-Galois rational-point formulation: a geometric
set defined over `k` is replaced by stability of its product set of
`K`-rational points under the explicit `rationalConjugate` action. It
handles several components together. The middle-out order expresses the
intended Galois-orbit ordering by distance from the middle pair. It alone
does not imply orbit compatibility; constructing witnesses and proving
stability remain obligations. Existence of suitable choices is asserted,
not stability for arbitrary choices.

Steinberg's Section 9 assumes perfectness and simple connectedness. This
statement isolates root-group choices and orbit ordering from the quotient
comparison. Its arbitrary-field and supplied-data scope, including the
absence of a simple-connectedness premise, are proof obligations of the
derived target, not additional theorems proved here.

For splitting fields, A. Borel and T. A. Springer, *Rationality properties
of linear algebraic groups II*, Tôhoku Math. J. (2) 20 (1968), 443–497,
source `borel-springer-1968-rationality-properties-ii`, SHA-256
`e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`,
Theorem 8.2 and Corollary 8.3, printed pp.481–482 (PDF pp.39–40), give
splitness from a split maximal torus and a finite separable splitting
extension for a connected reductive group over an arbitrary field.
A finite Galois closure supplies the Galois extension used in applications.
This statement already takes `K/k` and `D` as inputs and constructs neither.

## Scope

No cross-section, quotient property, unique fiber representative,
fixed-point descent, global rational section, regularity or stratum
isomorphism is asserted. The ordinary cross-section 7.9, p.68 (PDF p.21),
is background for the separate split statement, not a premise here.
Neither `QuasiSplitRegularClassRationalStatement` nor
`QuasiSplitSteinbergQuotientStatement` is assumed. Borel–Springer 8.6 is
not used; the splitting-field citation is limited to 8.2–8.3.
