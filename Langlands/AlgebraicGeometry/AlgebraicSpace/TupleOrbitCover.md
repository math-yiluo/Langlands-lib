# Tuple covers whose fibres are permutation orbits away from a proper closed set

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitCover`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

This is the orbit step (O) of the Noetherian case of task 13a3a0fd, "AF representability
from a finite surjection with quasi-affine source". Let `f : h_U ⟶ Y` be a finite surjective
map from a Noetherian scheme `U` to a quasi-compact algebraic space `Y`. The construction
produces a closed, permutation-stable set `Wset` of tuples of points of `U` with the same
image, and a proper closed saturated set `C ⊂ U`. Away from `C`, two tuples in `Wset` with
the same image in `Y` differ by a permutation of coordinates. The Noetherian induction then
treats `C` by induction. Off `C`, the published `OrbitSaturatedAffineOpen` turns orbits into
saturated affine opens.

Points with the same image are compared by the published `SameImage`. `saturation f A` is the
set of points with the same image as a point of `A` (point toolkit `SameImageClasses`).

## Declarations

- `isNoetherian_of_isFinite g`: a scheme finite over a Noetherian scheme is Noetherian.
  Local Noetherianity is `LocallyOfFiniteType.isLocallyNoetherian`, and compactness is
  `QuasiCompact.compactSpace_of_compactSpace`.
- `exists_generic_sameImage hf hfs hY hne`: for `f` finite surjective, `Y` quasi-compact and
  `U` nonempty, quasi-compact, quasi-separated and topologically Noetherian, there is a point
  `γ` whose class is closed under generization. That is, `a ⤳ b` and `SameImage f b γ` imply
  `SameImage f a γ`. The generic points of the finitely many irreducible components
  generalize every point. The toolkit's `exists_generic_class` applies with the relation
  `SameImage f`, its equivalence property, the absence of specializations inside a class
  (`SameImage.eq_of_specializes`) and transport of specializations along the relation
  (`SameImage.exists_specializes`).
- `ChartFibrePower.exists_isDistinct_transfer Q Q' γ hq hi`: a point of `Q` with pairwise
  distinct coordinates and `i`-th coordinate `γ` maps, under the identity index map, to such
  a point of any other fibre power `Q'` with the same index type.
- `exists_max_isDistinct hf γ`: there is a maximal `k` such that some fibre power indexed by
  `Fin (k + 1)` has a point with pairwise distinct coordinates through `γ`. No fibre power
  indexed by `Fin (k + 2)` has one. The proof takes `Nat.findGreatest` below the bound of
  `exists_bound_isDistinct`; length `1` is realized by `γ` itself in `ChartFibrePower.one`.
- `TupleOrbitCover f` (structure). The output of the construction:
  - a length `k + 1` and a fibre power `P` of `f` indexed by `Fin (k + 1)` whose
    projections are finite;
  - a closed set `Wset` of points of `P`, stable under the permutation action `perm`;
  - `surj`: every point `u` of `U` has the same image as `pr 0 w` for some `w ∈ Wset`;
  - a closed set `C` of points of `U`, saturated for `SameImage f` and not the whole
    space (`exists_notMem`);
  - `orbit`: if `w, w' ∈ Wset`, `pr 0 w ∉ C`, and `w, w'` have the same image under
    `h_{pr 0} ≫ f`, then `perm σ w = w'` for some permutation `σ`.
- `exists_tupleOrbitCover hf hfs hY hne`: for `f` finite surjective, `Y` quasi-compact,
  and `U` a nonempty Noetherian scheme (Mathlib's `IsNoetherian`) with quasi-separated
  underlying space, a `TupleOrbitCover f` exists.

## Proof of `exists_tupleOrbitCover`

Let `γ` be as in `exists_generic_sameImage` and `k` as in `exists_max_isDistinct`. Let `P` be
the standard fibre power `fin ha k`. Let `P2` be the `(2k + 2)`-fold standard power,
reindexed by `Fin (k + 1) ⊕ Fin (k + 1)`, with index maps `inl, inr : P2 ⟶ P`. All their
projections are finite, so both are Noetherian schemes by `isNoetherian_of_isFinite`. This
is where `IsNoetherian U` (rather than a topological hypothesis) is used: the
closure arguments below need `P` and `P2` to be Noetherian spaces.

1. Let `H` be the closed set of points of `P` with some coordinate in the closure of `γ`, and
   `D = H ∩ {distinct}`. Here `{distinct}` is open by `isOpen_isDistinct`. `D` contains the
   transferred maximal tuple `d₀` through `γ`.
2. Let `A = pr 0 (closure D)` and `O` the complement of its saturation. Both are closed or
   open as stated, since `pr 0` is finite and saturations of closed sets are closed
   (`isClosed_saturation`). Let `C₂ = saturation (closure O)`. Then `γ ∉ C₂`: a point of
   `closure O` specializes from a point `o ∈ O` (`exists_mem_specializes_of_mem_closure`).
   Genericity of the class of `γ` would put `o` in the class of `γ`, but `γ` is in the
   saturated set `saturation A`, which misses `O`.
3. `Wset = closure D ∪ diag (C₂)`. It is closed, since the diagonal is a closed immersion.
   It is permutation-stable: `D` is, and `diag ≫ perm σ = diag`. `surj` holds because a point
   outside `saturation A` lies in `C₂` and `pr 0 (diag u) = u`.
4. Key fact `keyW`: a point `w ∈ Wset` whose `pr 0` image has the class of `γ` has pairwise
   distinct coordinates, one of them equal to `γ`. The diagonal part is excluded by `γ ∉ C₂`.
   For `w ∈ closure D`, `w` specializes from some `d ∈ D`. Since `d ∈ H`, some coordinate
   `pr i d` lies in the closure of `γ`, that is, `γ ⤳ pr i d`. Also `pr i d ⤳ pr i w`, since
   `d ⤳ w`, so `γ ⤳ pr i w`. The coordinate `pr i w` has the class of `γ`, because all
   coordinates of `w` have the same image as `pr 0 w`. By `SameImage.eq_of_specializes`,
   `pr i w = γ`. Antisymmetry of the two specializations `γ ⤳ pr i d ⤳ γ` then gives
   `pr i d = γ`. Finally `d = w` by `eq_of_specializes_of_locallyQuasiFinite` for the finite
   projection `pr i`, since `d ⤳ w` and both lie over `γ`.
5. Pigeonhole `keyP`. Let `q ∈ P2` have distinct `inl`- and `inr`-halves, with `γ` among the
   `inl` coordinates. Then the `inr` coordinates are a permutation `π` of the `inl` ones.
   Otherwise `exists_perm_of_not_injective_snoc` would give a distinct `(k + 2)`-tuple through
   `γ` in `fin ha (k + 1)`, contradicting maximality of `k`.
6. Let `Hset = inl⁻¹ Wset ∩ inr⁻¹ Wset` (closed) and `Graph` the union over permutations `π`
   of the closed loci `coord (inr i) = coord (inl (π i))` (`isClosed_coord_eq`). Let
   `Q = Hset ∖ Graph` and `Bad = saturation (pr (inr 0) (closure Q))`, which is closed. Then
   `γ ∉ Bad`. A point of `closure Q` specializes from some `q ∈ Q`. Genericity of the class
   of `γ` puts both halves of `q` over the class of `γ`. Steps 4 and 5 then place `q` on
   `Graph`, a contradiction.
7. Take `C = Bad ∪ C₂`. It is closed and saturated, and `γ ∉ C`. For `orbit`, let `w, w'` be
   as there. `exists_pair` gives `p ∈ P2` with halves `w` and `w'`. If `p ∈ Graph`,
   `inr_eq_perm_inl` gives the permutation. Otherwise `p ∈ Q`, and `pr 0 w'` lies in `Bad`.
   Since `w, w'` have the same image, `pr 0 w` is in the saturated set `Bad ⊆ C`, a
   contradiction.

## Provenance

Internal. The construction replaces the normalization and conductor induction of Gross,
*Tensor generators on schemes and stacks* (2017), proof of Proposition 3.5, Steps 2–3
(source `gross-tensor-generators-schemes-stacks-2017`), by tuples of distinct points of
maximal length over a generic class. The pigeonhole step gives that any two such tuples are
permutations of each other. It uses only the finiteness of `f` and the point-level toolkit.
No source proof is transcribed.
