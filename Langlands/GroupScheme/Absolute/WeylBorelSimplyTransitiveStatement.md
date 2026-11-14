# Statement: the Weyl group acts simply transitively on the Borel subgroups through a maximal torus

Worker 75.

`Langlands.GroupScheme.WeylBorelSimplyTransitiveStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup`, `IsMaximalTorus`, `normalizerPoints`,
  `centralizerPoints` and the group-scheme vocabulary over a field.
- [`InnerAutomorphism`](../InnerAutomorphism.md), for the inner automorphism `G.innerIso n`.

## Lean statement

```lean
def WeylBorelSimplyTransitiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G), IsBorelSubgroup b →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range b →
      (∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G), IsBorelSubgroup b' →
        SubgroupFunctor.range j ≤ SubgroupFunctor.range b' →
          ∃ n ∈ normalizerPoints j,
            SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b') ∧
      (∀ n ∈ centralizerPoints j,
        SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b) ∧
      (∀ n ∈ normalizerPoints j,
        SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b →
          n ∈ centralizerPoints j)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism. A morphism
  `n : Over.mk (𝟙 (Spec k)) ⟶ G.X` is a `k`-point of `G`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger closed torus of `G`.
- `IsBorelSubgroup b` ([`Absolute.Borel`](Borel.md)): `b` is a closed immersion, `B` is smooth,
  connected and solvable, and `b` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`, on every scheme over
  `Spec k`; subgroup functors are ordered by inclusion of points.
- `G.innerIso n` ([`InnerAutomorphism`](../InnerAutomorphism.md)): the inner automorphism
  `x ↦ n x n⁻¹` of `G`. So `range (b ≫ (G.innerIso n).hom)` is the conjugate Borel subgroup
  `n B n⁻¹`.
- `normalizerPoints j` and `centralizerPoints j` ([`Torus.Maximal`](../Torus/Maximal.md)): the
  subgroups of `k`-points `n` of `G` with `j ≫ int(n) = σ ≫ j` for some automorphism `σ` of
  `T`, respectively with `j ≫ int(n) = j`. These are `N_G(T)(k)` and `C_G(T)(k)`.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k`, every maximal torus `j : T ⟶ G` and every Borel subgroup `b : B ⟶ G`
containing `T`:

1. **transitivity:** for every Borel subgroup `B'` containing `T` there is
   `n ∈ N_G(T)(k)` with `n B n⁻¹ = B'`;
2. **the action factors through `W`:** every `n ∈ C_G(T)(k)` satisfies `n B n⁻¹ = B`;
3. **freeness:** every `n ∈ N_G(T)(k)` with `n B n⁻¹ = B` lies in `C_G(T)(k)`.

`N_G(T)(k)` acts on the set of Borel subgroups containing `T` by conjugation. By (2) this
action factors through `W(G,T)(k) = N_G(T)(k)/C_G(T)(k)`; by (1) the action is transitive;
by (3) the stabilizer of `B` in `W(G,T)(k)` is trivial. The stabilizer of every other Borel
subgroup `B'` containing `T` is then trivial too, because `B` and `B'` are conjugate under
`N_G(T)(k)` and `C_G(T)(k)` is normal in `N_G(T)(k)`. So the three clauses together say that
`W(G,T)(k)` acts simply transitively.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.11, last sentence, p.355: "In particular, N_G(T) acts transitively on the set
  of Borel subgroups of G containing T." The proof shows that `N_G(T)(k)` acts transitively.
- Proposition 17.53, p.369: "Let T be a maximal torus of G. The Weyl group W(G,T) acts simply
  transitively on the set 𝓑^T of Borel subgroups of G containing T." Its proof shows that
  `C_G(T)` acts trivially and that an element `x ∈ N_G(T)` with `xBx⁻¹ = B` lies in
  `C_G(T)`.
- Definition 17.41, p.364: `W(G,T) = π₀(N_G(T)) = N_G(T)/N_G(T)° = N_G(T)/C_G(T)`, using
  17.39(a).
- Section 17b, opening, p.353, and Section 17f, opening, p.368: "G is a connected group
  variety over an algebraically closed field k."
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.364 entry concerns Example 17.42 ("take I = {1, 2, …, n}"), not
Definition 17.41; none concerns Corollary 17.11 or Proposition 17.53.

Milne's proofs: for 17.11, a conjugate `gBg⁻¹ ⊇ T` contains the maximal tori `T` and `gTg⁻¹`,
which are conjugate by some `h ∈ (gBg⁻¹)(k)` (17.10), and `hg ∈ N_G(T)(k)` conjugates `B` to
`gBg⁻¹`. For 17.53, `C_G(T)` is connected (17.38), so it acts trivially on the finite set
`(G/B)^T`; if `x ∈ N_G(T)` and `xBx⁻¹ = B`, then `x ∈ B` (17.48), and
`xtx⁻¹t⁻¹ ∈ T ∩ B_u = e` for `t ∈ T`, so `x ∈ C_G(T)`. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Sections 17b and 17f: `[IsAlgClosed k]`,
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **The Weyl group.** Over an algebraically closed field, `W(G,T)` is a finite constant group
  and `W(G,T)(k) = N_G(T)(k)/C_G(T)(k)` (`C_G(T)` is smooth). The Library has no quotient
  group scheme `N_G(T)/C_G(T)`, so the action of `W(G,T)` is stated through the conjugation
  action of `N_G(T)(k)` on Borel subgroups containing `T`, as explained above.
- **The set `𝓑^T`.** Borel subgroups are compared through their ranges in `G`, so two closed
  subgroups with the same range count as the same Borel subgroup. "`B` contains `T`" is
  `range j ≤ range b`.
- **Corollary 17.11, last sentence.** Clause (1); Milne's proof gives a conjugating element in
  `N_G(T)(k)`.

## Related Library results

- [`Absolute.BorelStatement`](BorelStatement.md) states existence and conjugacy of Borel
  subgroups (17.9) and the normalizer theorem for `k`-points.
- The finiteness of the set of Borel subgroups containing a maximal torus (Milne 17.26(a)) is
  stated separately as `MaximalTorusBorelFinitenessStatement` in the module
  `Langlands.GroupScheme.Absolute.MaximalTorusBorelFinitenessStatement`.
