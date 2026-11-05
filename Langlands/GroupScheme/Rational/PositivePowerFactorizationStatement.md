# A positive power as a torus point times an additive point: statement

Authors: Worker 1374 (original paired draft), Worker 1512 (proposed target),
and Worker 1587 (source verification and revised exposition).

`Langlands.GroupScheme.PositivePowerTorusAdditiveFactorizationStatement.{u}`
concerns an arbitrary field `k : Type u`, a smooth affine group scheme `G`
over `Spec k`, and an actual rational point `x` in `G(k)`. Smoothness gives
local finite type and affineness gives quasi-compactness, hence `G` is of
finite type. Connectedness, reductivity, perfectness of the field and a
restriction on the characteristic are not hypotheses.

The proposition asks for a natural number `m > 0`, a commutative group
scheme `T` satisfying the existing `IsTorus T.toGrp`, a closed group-scheme
inclusion `i : T.toGrp ⟶ G`, an actual point `t : rationalPoints T.toGrp`,
and an actual group-scheme morphism
`φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G`, with

```lean
x ^ m = rationalPoints.map i t *
  rationalPoints.map φ
    ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
      (Multiplicative.ofAdd (fun _ => 1)))
```

Here `rationalPoints G` is the group of sections
`Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X`, with its group law written
multiplicatively. For an actual group-scheme morphism `f`,
`rationalPoints.map f` is postcomposition with `f.hom.hom`.
`IsClosedSubgroup i` means that the underlying scheme map is a closed
immersion. The torus predicate permits a finite-rank split torus after
extension of the field; a rank-zero torus is allowed.

The source of `φ` is the existing one-dimensional vector group, the
additive group scheme. Its `VectorGroup.coordinates` equivalence on the
identity test scheme has codomain
`Multiplicative (Fin 1 → Γ(Spec (CommRingCat.of k), ⊤))`.
The displayed input is the constant global section `1`, which corresponds
to `1 ∈ k` under `Scheme.ΓSpecIso`. Thus the second factor evaluates `φ`
at additive coordinate `1`. The identity of the multiplicatively written
point group has additive coordinate `0`. A trivial additive morphism is
allowed.

This is a `Prop`-valued statement definition. This pair supplies no proof;
proving its exact Library declaration is a separate successor obligation.

## Original sources and derived provenance

This is a derived prerequisite, rather than a verbatim numbered assertion
in Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), registered as `milne-2017-algebraic-groups`.
The following original passages were read:

- Definition 1.9 and 1.10–1.14, printed pp.9–10 (one-based PDF pp.25–26),
  describe schematic density, its preservation by base change, geometric
  reducedness and equality of morphisms on dense rational points.
  Proposition 1.26, printed p.13 (PDF p.29), identifies geometric
  reducedness and smoothness for algebraic groups.
- Corrected Theorem 1.45 and Definition 1.48, printed pp.19–20
  (PDF pp.35–36) in the original book, give the algebraic subgroup in
  which a given subgroup of rational points is schematically dense.
  Corollary 1.43, printed p.19 (PDF p.35), retains affineness.
- Propositions 1.29–1.34, printed pp.15–17 (PDF pp.31–33), supply the
  finite component scheme and the identity subgroup.
- Theorem 16.47(a),(c) and Corollary 16.48, printed p.341 (PDF p.357),
  supply a central torus with unipotent quotient over arbitrary fields,
  and a product decomposition over perfect fields.
- Theorem 4.9 and Corollary 4.10, printed p.87 (PDF p.103), give a
  faithful finite-dimensional representation. Proposition 14.3, printed
  p.280 (PDF p.296), makes every finite-dimensional representation of a
  unipotent group unipotent.
- Definition 14.27 and paragraph 14.30, printed pp.286–287
  (PDF pp.302–303), give the characteristic-zero correspondence between
  unipotent rational points and morphisms from the additive group,
  evaluated at additive coordinate `1`.

The complete registered [official author errata](https://jmilne.org/math/Books/iag2errata.html)
snapshot `milne-2017-algebraic-groups-errata-2026-11-02` was read.
Its correction to 1.45 specifies the reduced subgroup whose underlying
space is the closure of the given rational subgroup; rational-point
equality alone does not give uniqueness. Its correction to 1.48
characterizes the closure by schematic density of the original subgroup.
The errata label these entries p.20 and p.21; the original PDF passages
are on printed pp.19 and 20.

The erratum to the proof of Lemma 1.40, printed p.18 (PDF p.34), warns
that multiplication on Zariski rational points need not be continuous
for the product topology. The closure argument must instead use
scheme-theoretic density, or separate translation and closed-centralizer
arguments. The snapshot has no correction to 14.30, 16.47 or 16.48.

## Derivation supporting the statement

Take the schematic closure `H` of the rational cyclic subgroup generated
by `x`, using the corrected closure convention. It is an affine algebraic
subgroup. Schematic density makes `H` geometrically reduced, hence smooth.
Commutativity follows by two successive density arguments: for each
cyclic rational point its two translations agree on the cyclic subgroup,
so they agree on `H`; then density after base change makes the two
multiplication maps agree on `H × H`. Equivalently one can use closed
centralizers. This does not use product-topology continuity.

The finite component group puts a positive power `y = x ^ m₀`, with
`m₀ > 0`, in `H⁰(k)`. The identity subgroup is smooth, connected, affine
and commutative, hence nilpotent. Theorem 16.47(a),(c) supplies a closed
central torus `T` with unipotent quotient `Q`.

In positive characteristic `p`, choose a faithful finite-dimensional
representation of `Q`. The image of any `q ∈ Q(k)` is `I + N` with
`N` nilpotent. For sufficiently large `r`,
`(I + N) ^ (p ^ r) = I`, so faithfulness gives
`q ^ (p ^ r) = 1`. Apply this to the image of `y`. The scheme-theoretic
kernel's representing property gives an actual `t ∈ T(k)` mapping to
`y ^ (p ^ r)`. Set `m = m₀ * p ^ r` and take the trivial `φ`. This uses
the kernel property, without requiring surjectivity on rational points
of either the quotient map or a central isogeny.

In characteristic zero the field is perfect. Corollary 16.48 splits
`H⁰` into its torus and connected unipotent factors. The unipotent factor
of `y` is the value at `1` of an actual additive-group morphism by 14.30.
Composing the two factor inclusions into `G` gives the displayed equality
with `m = m₀`. A proof successor must implement these constructions and
their compatibility with the existing point and coordinate interfaces,
or supply another proof of the exact statement.

The ordinary rational Jordan decomposition in Theorem 9.18, printed
p.170 (PDF p.186), assumes a perfect field. It does not supply the
arbitrary-field assertion here.

## Consumer boundary

`NilpotentCentralTorusStatement` is a separate proposition target, not an
available proof of the structural step above. This pair does not identify
algebraic derived rational points with abstract commutators, assert
rational surjectivity of a central isogeny, or prove that ambient
open-kernel real homomorphisms kill the relevant torus points. Those
comparisons remain obligations of the surrounding
`Langlands.BruhatTits.RationalPoints.DerivedSmoothRealAnnihilationStatement`
program.
