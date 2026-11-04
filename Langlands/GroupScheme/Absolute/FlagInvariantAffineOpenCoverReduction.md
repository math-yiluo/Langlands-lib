# Reduction of invariant affine neighbourhoods to the dual-line core

Author: Worker 967.

This internal module assembles the invariant-affine-neighbourhood step of the
flag argument (task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`). Its main theorem,
`flagInvariantAffineOpenCover_of_prerequisites`, proves
`FlagInvariantAffineOpenCoverStatement` at an arbitrary universe `u` from four
Library statements:

- `FlagCoreDualLineStatement` (module `Langlands.GroupScheme.FlagCoreDualLine`);
- `SpanningLineStabilizerStatement` (module
  `Langlands.GroupScheme.SpanningLineStabilizerStatement`);
- `SomeBorelQuotientProperStatement` (module
  `Langlands.GroupScheme.Absolute.BorelProperQuotientStatement`);
- `BorelConjugacyStatement` (module `Langlands.GroupScheme.Absolute.BorelStatement`).

All four enter as explicit hypotheses. None of them is proved in this module, so
the module is **not** an unconditional proof of the target statement. When proofs
of the four statements are in the Library, applying the main theorem to them
proves the target.

Mathematically this is the proof of Milne, *Algebraic Groups* (2017), Theorem
17.65, adapted to the Library's interfaces. The supplied quotient `Q = G/B` is
embedded in a projective space `P(V)`, and the `U`-stable affine open `D₊(w)` of
`P(V)` is intersected with `Q`. The linear form `w` comes from the dual-line
core. Two inputs of Milne's argument are obtained differently here:

- Milne uses that the image of `G/B` in `P(V)` is closed, because `G/B` is
  complete. The target statement only says that the quotient map `q` is flat,
  surjective and quasi-compact; it does not say that `Q` is proper. Here
  properness of the supplied `Q` is derived from
  `SomeBorelQuotientProperStatement` and `BorelConjugacyStatement`, as in the
  Library's `FlagStepReduction`.
- Milne takes the projective embedding to be nondegenerate: the vectors
  `g v`, for `g` in `G`, span `V`. Chevalley's theorem in the Library
  (`Chevalley.exists_line_stabilizer`) gives a representation without this
  spanning property; `SpanningLineStabilizerStatement` supplies one with it.

The hypotheses that `U` is connected and unipotent in the target statement are
not used. The proof only needs `U` to be smooth and to lie in every Borel
subgroup through the given maximal torus.

## Right translation

`S` is a base scheme and `G` a group scheme over `S`. A base point of `G` is a
morphism `g : Over.mk (𝟙 S) ⟶ G.X`; `G.constantPoint g T` is its pullback to a
test `T` (Library `InnerAutomorphism`).

- `GroupScheme.rightTranslation G g`: the morphism `G.X ⟶ G.X` given by right
  multiplication by `g`, defined as the product `𝟙 * constantPoint g G.X`.
- `comp_rightTranslation`: for every test point `x : T ⟶ G.X`,
  `x ≫ rightTranslation g = x * constantPoint g T`.
- `rightTranslation_comp_rightTranslation`: translating by `g` and then by `h` is
  translating by `g * h`. The proof uses that `constantPointHom` (Library
  `HomConjugacy`) is a monoid homomorphism.
- `rightTranslation_one`: translation by `1` is the identity.
- `rightTranslationIso`: right translation by `g` as an automorphism of `G.X`
  with inverse translation by `g⁻¹`.
- `mem_range_iff_conj_mem_range`: let `b₀ : B₀ ⟶ G` and `b : B ⟶ G` be
  homomorphisms, `g` a base point and `φ : B₀ ≅ B` with
  `b₀ ≫ int(g) = φ ≫ b`, as produced by `BorelConjugacyStatement`. Then a test
  point `x : T ⟶ G.X` lies in the range of `b` if and only if `g⁻¹ x g` lies in
  the range of `b₀`. Here `g` stands for `constantPoint g T`. The proof uses the
  Library's `comp_innerIso_hom`, which says that `int(g)` acts on test points by
  `y ↦ g y g⁻¹`.

## Properness of an arbitrary flat Borel quotient

From here on `k` is an algebraically closed field and `G` is a smooth affine
group over `Spec k` with connected underlying space.

`IsBorelSubgroup.isProper_quotient_of_conjugacy`: assume
`SomeBorelQuotientProperStatement` and `BorelConjugacyStatement`. Let
`b : B ⟶ G` be a Borel subgroup and `q : G.X ⟶ Q` flat, surjective and
quasi-compact, whose fibres are the cosets of `b` on every test: `x ≫ q = y ≫ q`
if and only if `x⁻¹ y` lies in the range of `b`. Then `Q` is proper over `k`.

Proof:

1. `SomeBorelQuotientProperStatement` gives a Borel subgroup `b₀ : B₀ ⟶ G` such
   that every smooth quotient model of `G` by `b₀` is proper.
2. The Library theorem `smoothSubgroupQuotientExistence` gives such a model
   `q₀ : G.X ⟶ Q₀` (Borel subgroups are smooth closed subgroups), so `Q₀` is
   proper.
3. `BorelConjugacyStatement` gives a base point `g` and `φ : B₀ ≅ B` with
   `b₀ ≫ int(g) = φ ≫ b`.
4. Put `r := rightTranslation g ≫ q₀`. Right translation is an isomorphism, so
   `r` is flat, surjective and quasi-compact. Its fibres are those of `q`:
   `x ≫ r = y ≫ r` if and only if `g⁻¹ x⁻¹ y g` lies in the range of `b₀`. By
   `mem_range_iff_conj_mem_range` this holds if and only if `x⁻¹ y` lies in the
   range of `b`, that is, `x ≫ q = y ≫ q`.
5. The Library's `HomogeneousQuotientComparison.iso` then gives an isomorphism
   `Q ≅ Q₀` over `k`. Hence `Q.hom` is an isomorphism followed by the proper
   morphism `Q₀.hom`, so it is proper.

## A spanning line-stabilizer representation

`exists_spanning_line_stabilizer`: assume `SpanningLineStabilizerStatement`. Let
`G` be smooth and affine over `k` (connectedness is not needed) and
`i : H ⟶ G` a closed subgroup. Then there are `n`, an index `j` and a matrix
representation `ρ` of `G` on `k^(n+1)` such that:

- on every test `Z`, a point `x : Z ⟶ G.X` lies in the range of `i` if and only
  if `ρ(x) e_j = c e_j` for some unit `c` of `Γ(Z, O_Z)`;
- the vectors `ρ(g) e_j`, for `g` a rational point of `G`, span `k^(n+1)`.

The proof takes the representation of Chevalley's theorem in the Library
(`Chevalley.exists_line_stabilizer`). It then applies
`SpanningLineStabilizerStatement` to it and composes the two stabilizer
equivalences.

## The assembly

`flagInvariantAffineOpenCover_of_prerequisites`: the four statements above imply
`FlagInvariantAffineOpenCoverStatement.{u}`. Take the data of the target
statement: `G`, a maximal torus `t`, a smooth closed subgroup `i : U ⟶ G` lying
in every Borel subgroup that contains the range of `t`, a Borel subgroup `b`, a
quotient `q : G.X ⟶ Q` with the stated properties, an action `a` of `G` on `Q`
compatible with `q`, and a rational point `x` of `Q`. Then:

1. `exists_spanning_line_stabilizer`, applied to the closed subgroup `b`, gives
   `n`, `j`, `ρ` with `B` as the all-test stabilizer of the line `k e_j` and with
   a spanning rational orbit of `e_j`.
2. `isProper_quotient_of_conjugacy` shows that `Q` is proper.
3. `FlagCoreDualLineStatement`, applied to `t`, `i`, `b` and `ρ`, gives for every
   rational point `g` of `G` a row vector `w` with `w · ρ(g) e_j ≠ 0` whose line
   is stable under the rational points of `U`.
4. The Library theorem `exists_invariantAffineOpen_of_dualLines` (module
   `Langlands.GroupScheme.FlagDualLineNeighbourhood`) turns these data into an
   affine open `V` of `Q` containing `x` with
   `(a.restrict i).hom.left ⁻¹ᵁ V = (snd U.X Q).left ⁻¹ᵁ V`. Its hypotheses are
   `G` smooth and affine, `b` a smooth closed subgroup, `U` smooth, the
   stabilizer property of `ρ`, `Q` proper, `q` flat, surjective and
   quasi-compact with the fibres of `b`, and the compatibility of `a` with `q`.

## Provenance

This module is an internal composition of Library interfaces. It was developed
by Worker 967 as collaborator on task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`,
with the split of work agreed with Worker 1495 (first executor, author of
`FlagCoreDualLineStatement`). `SpanningLineStabilizerStatement` was stated by
Worker 1489. The properness transfer follows the use of
`SomeBorelQuotientProperStatement` and `BorelConjugacyStatement` in the Library's
`FlagStepReduction` (Worker 1489). The underlying mathematics is Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 17.65
and the surrounding discussion. No new external result is used, and no axiom
beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).
