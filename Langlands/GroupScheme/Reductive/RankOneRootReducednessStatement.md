# Statement: reducedness of the roots in semisimple rank one

`Langlands.GroupScheme.RankOneRootReducednessStatement` is an unproved
proposition at arbitrary universe `u`. Nothing is proved in this module.

## The statement

Let `k : Type u` be a field and `G` a group scheme over `Spec k` satisfying the
published `IsConnectedReductive G`. Let `T` be a commutative group scheme with
`IsSplitTorus T.toGrp`, and let `i : T.toGrp ⟶ G` satisfy `IsMaximalTorus i`.
These are the hypotheses of `RootReducednessStatement`. The instance
`IsAffineHom G.X.hom`, which `roots i` needs, comes from `hG.isAffineHom`.

The additional hypothesis: for all `α β ∈ roots i`, the pair `![α, β]` is not
linearly independent over `ℤ` in `characterLattice T`. The conclusion: for all
`α β ∈ roots i`, `α = β` or `α = -β`. Here `roots i` is the published set of
nonzero characters of `T` with a nonzero weight space in the actual Lie algebra
`Lie(G)(k)`.

## Relation to the source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- Theorem 21.11(a),(b), printed p.428 (PDF 444), proof printed p.429
  (PDF 445): for a split reductive group `(G, T)` and a root `α`, put
  `T_α = Ker(α)°_red` and `G_α = C_G(T_α)`. Then `(G_α, T)` is split reductive
  of semisimple rank 1, and the only rational multiples of `α` in `Φ(G, T)`
  are `±α`.
- Proposition 20.32, printed p.418 (PDF 434), with Theorem 20.22, printed
  p.415 (PDF 431): the rank-one structure (`G/B ≅ P¹`, and a central isogeny
  from `SL₂` onto the derived group) used in that proof.

This proposition is the special case of Theorem 21.11(b) in which all roots
are rational multiples of one root. The hypothesis is a root-theoretic form of
"semisimple rank at most one": when every root is a rational multiple of `α`,
every root is trivial on `T_α`, so `T_α` centralizes `Lie(G)` and `G_α = G`.
Milne's proof of 21.11(b) then applies 20.32 to `G` itself. This formulation
is derived, not quoted. It avoids derived groups and the semisimple rank, which
the Library does not define, and the Library does not prove the comparison with
Milne's semisimple rank. With the hypothesis of this proposition, its
conclusion says exactly that the only rational multiples of a root in the root
set are `±α`. The reason is the one recorded for `RootReducednessStatement`:
the character lattice of a split torus is torsion-free and roots are nonzero.

## Intended use

The general statement `RootReducednessStatement` reduces to this case. For roots
`α` and `β` linearly dependent over `ℤ`, one chooses a cocharacter `μ` of `T`
that pairs to zero with `α` and to a nonzero value with every root that is not
a rational multiple of `α`. A closed representative of the dynamic centralizer
of `μ` is connected reductive by `DynamicCentralizerReductiveStatement`. It
contains `T` as a split maximal torus, and its roots are the roots of `G` that
pair to zero with `μ`. These roots are pairwise dependent, and they include `α`
and `β`.

## Scope

The proposition asserts only reducedness of the actual roots under the stated
hypothesis. It does not assert that roots exist, that `-α` is a root, that
`dim g_α = 1`, or anything about coroots, reflections, Borel subgroups or the
classification of rank-one groups. The field and its characteristic are
arbitrary.
