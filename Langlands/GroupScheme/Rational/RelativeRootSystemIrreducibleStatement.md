# Statement: the relative root system of an almost-simple group is irreducible

Worker 161, with Worker 227. Support statement for Task 6205.

`RelativeRootSystemIrreducibleStatement` is a proposition at every universe
`u`. It states the following for every field `k : Type u`, every group scheme
`G` over `Spec k` and every maximal split torus `i : T.toGrp ⟶ G`
(`IsMaximalSplitTorus i`). Suppose that `G` is almost simple (`IsAlmostSimple G`)
and that `relativeRoots i` is nonempty. Let `J : Type u` and let
`P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))`.
Assume that

- `P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i)`, so the root-coroot
  pairing of `P` is evaluation of a dual vector on a vector, and
- `Subtype.val '' Set.range P.root = toRat '' relativeRoots i`, so the roots of
  `P` are exactly the images `1 ⊗ α` in `ℚ ⊗[ℤ] X*(T)` of all relative roots `α`.

Then `P.IsIrreducible`, in the sense of Mathlib's `RootPairing.IsIrreducible`.

The instance `IsAffineHom G.X.hom`, which `relativeRoots` and `relativeRootSpan`
need, is the one obtained from `IsAlmostSimple G` through `IsSemisimple` and
`IsConnectedReductive`. The instance is a proposition, so any other proof of it
gives definitionally equal relative roots and span.

## Source

Armand Borel and Jacques Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
registered source `borel-tits-1965-groupes-reductifs`. In §5 (printed p. 95,
PDF p. 42) `G` is connected reductive and `S` is a maximal `k`-split torus.
Corollary 5.8 (printed p. 98, PDF p. 45) shows that the `k`-roots `kΦ` form a
root system. Corollary 5.11 (printed p. 99, PDF p. 46) adds: "En
particulier, si G est presque simple sur k, kΦ est un système de racines
irréductible." The statement above transcribes this sentence. It differs from
the source in the following ways.

1. **Nonempty premise.** If `G` is anisotropic over `k`, then `kΦ` is empty and
   the source sentence holds at most by convention. Corollary 5.11 itself is
   about subgroups that are not anisotropic. The statement therefore assumes
   `(relativeRoots i).Nonempty`. The anisotropic case has no content here.
2. **Every compatible root pairing.** The source fixes no Lean object for `kΦ`,
   so the statement quantifies over every Mathlib root pairing on
   `relativeRootSpan i` with the two properties above, indexed by any type in
   `Type u`. Nothing is assumed about reducedness, crystallographic integrality,
   finiteness of `J` or the Weyl group. Such a `P` has the same roots as `kΦ`.
   Its coroots are also those of `kΦ`, because in characteristic zero the
   coroot of a root in a finite spanning root set is determined by that root
   (Bourbaki, *Lie Groups and Lie Algebras*, Ch. VI §1 no. 1, Lemma 1, source
   `bourbaki-lie-iv-vi-2002-scribd-original-text`). The relative roots are
   finite, since `kΦ` is a root system (Borel–Tits 5.8). The Library proposition
   `HasRelativeRootSystem` asserts that such a pairing exists. It is part of
   the separately stated `RelativeRootSystemStatement`. The present statement
   does not assume existence.
3. **Irreducibility.** Borel–Tits use irreducibility in Bourbaki's sense: the
   root system is not empty and is not the direct sum of two nonempty root
   systems. Mathlib's `IsIrreducible` instead asks that both `M` and `N` be
   nontrivial and that every nonzero submodule of `M` (respectively `N`) that is
   stable under all reflections (respectively coreflections) be everything. For
   a finite root system over `ℚ` the two notions agree. A root system is
   irreducible exactly when its Weyl-group module `V` is simple (Bourbaki,
   Ch. VI §1 no. 2, Corollary to Proposition 5), and the inverse root system of
   an irreducible root system is irreducible.
4. **Almost simple.** `IsAlmostSimple` is the Library's version of Milne,
   *Algebraic Groups* (2017), Definition 19.7, with the author's correction:
   semisimple and noncommutative, and every smooth connected closed normal
   subgroup is trivial or everything. Every such subgroup in Borel–Tits is a
   smooth `k`-subgroup, so this matches the source's "presque simple sur k".
   Only almost simplicity over `k` is assumed, not absolute almost simplicity.

The statement asserts nothing about the Weyl group, the classification of
irreducible root systems or the anisotropic kernel. It supplies no proof.
