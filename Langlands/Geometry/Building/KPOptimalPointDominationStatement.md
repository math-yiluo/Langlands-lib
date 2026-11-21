# Optimal-point domination in one apartment (KP Lemma 13.4.4)

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 13.4.4,
printed pp. 473–474 / PDF pp. 504–505, asserts that for each building point
`z` and real `s` there is a point `y ∈ O` with `𝔤_{z,s} ⊆ 𝔤_{y,s}`. The set
`O` consists of rational group translates of the points `x_S` chosen, one
for each nonempty subset `S` of the finite set `Σ` of one fixed chamber.
This choice and its meaning are described before Example 13.4.3, printed
p. 473 / PDF p. 504 (Definitions 13.4.1 and 13.4.2 are on printed p. 472 /
PDF p. 503). The authors' corrections of 1 November 2024 have no entry for
§13.4 (Chapter 13 corrections at PDF p. 49).

## Formal target

- `AffineRootSystem.OptimalPointSubset Ψ c` indexes the nonempty finite
  subsets of `positiveRootsBelowPeriod Ψ c`, the `Σ` of `facet Ψ c` when `c`
  is regular and the period exists.
- `AffineRootSystem.OptimalPointChoice Ψ c` is a dependent function assigning
  to each such `S` a point together with `IsOptimalPointFor Ψ c S.val` for
  that point. It specifies **one** `x_S` for each `S`. It is not the set of
  all optimal points and it does not assert that the choices exist.
- `Langlands.Geometry.Building.ApartmentOptimalPointDominationStatement`
  quantifies over a nonarchimedean local field `F` (mixed or equal
  characteristic), an affine group scheme `G` over `F`, its supplied
  `ParahoricBuildingData G` (which carries connected reductivity), and
  supplied `LieFiltrationData L`. It assumes that `c` in the apartment is
  regular and that `P.affineRoots` is nonempty. For any such choice `x_S`,
  every `z ∈ facetClosure P.affineRoots c` and real `s`, it asks for an index
  `S : OptimalPointSubset P.affineRoots c` with
  `L.lieFiltrationReal z s ≤ L.lieFiltrationReal (choosePoint S).val s`.

The lattices at depth `s` are the existing real-index Lie submodules of
`KPLieFiltrationDual`, not group filtrations. They compare `𝒪[F]`-submodules
of the same `GenericLie 𝒪[F] G`. At nonnegative depth these are the supplied
centralizer and root-lattice spans of §13.3.3. At any real depth they use the
published ideal-power test at `s + ⌈-s⌉₊`. No periodicity premise is required
for the comparison at one and the same depth on this interface. This does not
assert periodicity or identify these supplied lattices with the Lie modules of
constructed integral models.

## Scope and provenance

The target retains exactly the fixed-chamber part of the calculation in KP's
proof, with `y` one of the selected `x_S`, not an arbitrary optimal point.
It restricts `z` to the same closed chamber and does not construct `O` on the
building or prove the reduction of arbitrary building points to that chamber.
It also leaves the existence of a choice family (the rational optimization
argument after Definition 13.4.2) separate. The explicit nonempty-root premise
is essential for this literal choice-set conclusion: `Σ` has no nonempty
subset when `Ψ` is empty, so no such index `S` could be returned in that case.

The two abbreviation types implement the source's indexing and choice using
`Finset` and subtypes. The proposition expresses the source restriction over
the Library's already-defined chamber, optimality and Lie-lattice objects.
It is a statement, not a proof of Lemma 13.4.4. No external code is adapted.
