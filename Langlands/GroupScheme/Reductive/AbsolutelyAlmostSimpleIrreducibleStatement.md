# Statement: absolute almost-simplicity and irreducibility of the root system

Worker 75. Statement for Task 3483 (algebraic and reductive group schemes).

`AbsolutelyAlmostSimpleIrreducibleStatement` is a proposition at every universe
`u`. It states the following for every field `k : Type u` and every group
scheme `G` over `Spec k`.

Suppose that `G` is semisimple (`hG : IsSemisimple G`) and nontrivial,
expressed as `SubgroupFunctor.range (𝟙 G) ≠ ⊥`: some point of `G` with values
in some scheme over `k` is not the identity point. Let
`G_{k̄} = (GroupScheme.baseChange (toAlgebraicClosure k)).obj G` be the base
change to the algebraic closure `AlgebraicClosure k`, and let
`i : T.toGrp ⟶ G_{k̄}` be a maximal split torus (`IsMaximalSplitTorus i`) of
`G_{k̄}`, for a commutative group scheme `T` over `Spec k̄`. Let `J : Type u` and
let `P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))`
satisfy

- `P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i)`, so the root-coroot
  pairing of `P` is evaluation of a dual vector on a vector, and
- `Subtype.val '' Set.range P.root = toRat '' relativeRoots i`, so the roots of
  `P` are exactly the images `1 ⊗ α` in `ℚ ⊗[ℤ] X*(T)` of the roots `α` of `T`
  in `G_{k̄}`.

Then `IsAbsolutelyAlmostSimple G ↔ P.IsIrreducible`.

`relativeRoots i` and `relativeRootSpan i` need the instance
`IsAffineHom G_{k̄}.X.hom`. The statement supplies it with `haveI`: the
structure map of `G_{k̄}` is `Limits.pullback.snd G.X.hom (toAlgebraicClosure k)`,
and it is affine because `G.X.hom` is affine, which comes from `hG` through
`IsConnectedReductive`. The instance is a proposition, so any other proof of it
gives definitionally equal roots and span. The `RootPairing`, the
evaluation map and `relativeRootSpan` are taken from Mathlib and the Library
exactly as in the Library statement `RelativeRootSystemIrreducibleStatement`
(module `Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement`).

## Source

Brian Conrad, *Reductive group schemes* (SGA3 summer school notes, 2014),
registered source `conrad-2014-reductive-group-schemes`. Printed page numbers.

- p. 149, after the proof of Proposition 5.1.17: "A connected semisimple group
  H over a field k is k-simple if H ≠ 1 and H has no nontrivial normal smooth
  connected proper k-subgroup, and absolutely simple if H_K is K-simple for some
  (equivalently, any) algebraically closed extension K/k."
- p. 150, Corollary 5.1.18: "A nontrivial connected semisimple group G over a
  field is absolutely simple if and only if the root system for G_{k_s} is
  irreducible."

Conrad derives the corollary from Proposition 5.1.17 (pp. 148–149): for split
semisimple `G` with split maximal torus `T`, the minimal nontrivial normal
smooth connected subgroups `G_i` correspond to the irreducible components of
`Φ(G, T)`. The statement above transcribes Corollary 5.1.18. It differs from
the source in the following ways.

1. **Semisimple and nontrivial.** Conrad's "connected semisimple" is the
   Library's `IsSemisimple` (connected reductive with finite scheme-theoretic
   centre, Conrad Definition 3.1.1 over a field). "Nontrivial" is
   `SubgroupFunctor.range (𝟙 G) ≠ ⊥`. The range of the identity is the
   subgroup functor of all points, and `⊥` is the subgroup functor of identity
   points, so the condition says that `G` is not the trivial group scheme.
2. **Absolutely simple.** The Library's `IsAbsolutelyAlmostSimple G` is
   `IsAlmostSimple G ∧ IsAlmostSimple G_{k̄}`. `IsAlmostSimple` (Milne,
   *Algebraic Groups*, Definition 19.7, corrected) asks for semisimplicity,
   noncommutativity, and that every smooth connected closed normal subgroup be
   trivial or everything. For a semisimple group, noncommutativity is the same
   as Conrad's `H ≠ 1`: a commutative connected reductive group is a torus, and
   a semisimple torus is trivial. So `IsAlmostSimple` is Conrad's "k-simple",
   and `IsAlmostSimple G_{k̄}` is Conrad's "absolutely simple" for the
   algebraically closed extension `k̄`. The extra conjunct `IsAlmostSimple G`
   follows from it, because the base change of a nontrivial proper normal smooth
   connected `k`-subgroup is a nontrivial proper normal smooth connected
   `k̄`-subgroup. The definition uses only `K = k̄`. Conrad's "some
   (equivalently, any)" is not part of the statement.
3. **`k̄` instead of `k_s`.** Conrad takes the root system of `G_{k_s}` with
   respect to a split maximal torus. The statement uses `G_{k̄}` and a maximal
   split torus `i` of `G_{k̄}`. Over the algebraically closed field `k̄` every
   torus is split, so `i` is a maximal torus of `G_{k̄}`. A split maximal torus
   of `G_{k_s}` base-changes to a maximal torus of `G_{k̄}` with the same
   character lattice and the same roots, so the two root systems agree. All
   maximal tori of `G_{k̄}` are conjugate, so the irreducibility of the root
   system does not depend on `i`. The statement nevertheless asserts the
   equivalence for every maximal split torus `i` of `G_{k̄}`; it does not
   assume or assert that such an `i` exists.
4. **Every compatible root pairing.** Conrad fixes no Lean object for the root
   system, so the statement quantifies over every Mathlib root pairing on
   `relativeRootSpan i` with the two properties above, indexed by any type in
   `Type u`. Nothing is assumed about reducedness, finiteness of `J` or
   crystallographic integrality. Such a `P` has the roots of `Φ(G_{k̄}, T)`, and
   its coroots are determined by them (Bourbaki, *Lie Groups and Lie Algebras*,
   Ch. VI §1 no. 1, Lemma 1). The statement does not assert that such a `P`
   exists.
5. **Irreducibility.** Conrad uses irreducibility in Bourbaki's sense: the root
   system is not empty and is not the direct sum of two nonempty root systems.
   Mathlib's `RootPairing.IsIrreducible` asks that both the weight space and
   the coweight space be nontrivial, and that every nonzero submodule of the
   weight space stable under all reflections, and every nonzero submodule of
   the coweight space stable under all coreflections, be everything. For a
   finite root system over `ℚ` the two notions agree: a root system is
   irreducible exactly when its Weyl group acts irreducibly on the ambient
   space (Bourbaki, Ch. VI §1 no. 2, Corollary to Proposition 5), and the
   inverse root system of an irreducible root system is irreducible. Here the
   weight space is the rational span `relativeRootSpan i` of the roots.

The direction `⇒` over `k̄` is also a consequence of the Library statement
`RelativeRootSystemIrreducibleStatement` (Borel–Tits, Corollary 5.11) applied
to `G_{k̄}`, since over `k̄` the relative roots are the absolute roots. The
present statement contains both directions and is phrased for `G` over `k`.

The statement asserts nothing about the decomposition of a semisimple group
into simple factors (Conrad Proposition 5.1.17 and Theorem 5.1.19), about
Galois actions, or about the classification of irreducible root systems. It
supplies no proof.
