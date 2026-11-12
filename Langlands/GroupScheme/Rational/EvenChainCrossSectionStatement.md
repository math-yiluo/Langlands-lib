# Statement: the split even-path cross-section of the canonical class quotient

`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement.{u}` is a
`Prop`-valued definition, not a proof. Provenance: derived. Worker 175 wrote
the Lean interface in the shared draft for Task 5324
(`dae9b3ff-3319-4226-a421-ef1462af985a`); Worker 162 checked the originals
and completed this documentation.

## Exact statement

In one arbitrary universe `u`, the proposition quantifies over every field
`k : Type u`, actual group scheme `G` over `Spec k` with affine structure
morphism, and supplied `p : SplitPinning G`. It assumes
`IsSimplyConnected G`, the Library's algebraic simple connectedness for
semisimple field groups. The pinning supplies the actual split maximal
torus and finite reduced root datum. No perfectness, infinitude,
characteristic restriction or algebraic closedness is assumed.

For every normalized whole simple-root family
`x : p.NormalizedSimpleRootParametrizations`, `J : Type u` with `Fintype J`,
`C : p.EvenChainData J`, `r,q : ℕ`, and orderings `o : Fin r ≃ J` and
`e : Fin q ≃ C.Rest`, it assumes `C.IsMiddleOut e`. For each rational point

`w : Over.mk (𝟙 (Spec k)) ⟶ ClassFunctions.quotient G`

it asserts that there exists exactly one `g : rationalPoints G` satisfying:

- `g ∈ C.patternSet x (SplitPinning.canonicalSimpleReflectionRepresentatives x) o e`;
- `g ≫ ClassFunctions.rho G = w`.

Uniqueness concerns this conjunction, not coordinates or the full fiber.
Merged representatives and nonzero root points are supplied by `C`; other
representatives are the published canonical family constructed from `x`.
The selected paths are disjoint whole type `A_(2m)` components, and `Rest`
includes all remaining simple roots.

The target is the actual canonical class-function quotient:
`ClassFunctions.quotient G` is the spectrum of the regular
conjugation-invariant subalgebra of the coordinate algebra of `G`;
`ClassFunctions.rho G` is induced by its inclusion. No arbitrary quotient
or affine-space identification is a premise.

## Sources and derived provenance

Robert Steinberg, *Regular elements of semi-simple algebraic groups*,
Publ. Math. IHÉS 25 (1965), 49–80, source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
PDF page numbers are printed page numbers minus 47.

Theorem 7.9, printed p.68 (PDF p.21), gives the ordinary cross-section
isomorphism for the fundamental-character map of 6.10. The notation before
9.11 and Theorem 9.11, p.74 (PDF p.27), give the middle-pair replacement
and products across several components. Lemmas 9.12–9.14, p.75
(PDF p.28), give the smaller type `A` comparison, coordinates and conjugacy
when the nonidentity root points change. The calculations in 9.15–9.18,
pp.75–77 (PDF pp.28–30), yield 9.19(a), p.77 (PDF p.30): the two products
map isomorphically to complementary strata `f=0` and `f≠0`. The source's
`f` is the alternating sum of fundamental-character coordinates with
endpoints `χ_0=χ_(2m+1)=1`. Its auxiliary normalization in 9.16 serves the
calculation; 9.14 handles the arbitrary choices allowed by 9.11.

This is a derived rational-point target combining a stratum per selected
path and ordinary factors on other components. It uses supplied root data
and coroot images and asserts the property over every split field.
Steinberg works over an algebraically closed universal field and assumes
perfectness at the start of Section 9; those hypotheses are not imported
into this definition. The split-field, rank-one and canonical-quotient
comparisons remain proof obligations, not results proved here.

The middle-out order is the derived interface needed by the Galois
consumer: remaining vertices on a path occur by increasing distance from
the middle pair, in either order at equal distances. Distinct components
may interleave. The orbit ordering in 9.4, pp.72–73 (PDF pp.25–26), and
the final paragraph proving 9.7(e) after 9.19 on p.77 motivate the interface.
The assertion for every ordering satisfying the predicate is part of the
proof obligation.

## Scope

Only rational-point existence and uniqueness for a group with a supplied
split pinning is stated. No scheme-theoretic stratum isomorphism,
regularity of every point, formula for `f`, existence or Galois
compatibility of data, or rational section over a non-split field is
asserted. There is no premise asserting
`QuasiSplitRegularClassRationalStatement`,
`QuasiSplitSteinbergQuotientStatement` or Borel–Springer 8.6. A finite
splitting extension belongs to the separate Galois-data setting.
