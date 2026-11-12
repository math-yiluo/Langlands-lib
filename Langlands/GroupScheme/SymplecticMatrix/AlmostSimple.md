# Almost simplicity of groups of type C and of the symplectic group

This internal module proves that the standard symplectic group `Sp_{2n}`, `n ≥ 2`, is
absolutely almost simple over every field. It first reduces almost simplicity to data about a
split maximal torus (type C root combinatorics), then verifies that data for the diagonal torus
of the split symplectic group over an algebraically closed field, and finally descends to every
field.

Throughout, `k` is a field and `G` an affine group scheme over `Spec k`. `t : T ⟶ G` is a
homomorphism from a commutative group scheme `T`. `relativeRoots t` (the same set as `roots t`)
is the Library's set of roots of `t`, and `latticePairing T` is the Library's pairing of
characters with cocharacters. `RootsLinked t α β` is from `Reductive.LinkedRootsAlmostSimple`:
`α` and `β` are roots whose root subgroups fail to commute on some test scheme.

## Root combinatorics of type C

`reflTransGen_rootsLinked_of_typeC`: let `e : l → X(T)` be characters. Assume every root of `t`
is `±2e_a` or one of `e_b - e_a`, `-e_a - e_b`, `e_a + e_b` with `a ≠ b`. Assume that for all
`a ≠ b` the following pairs are linked:

* `e_b - e_a` and `2e_a`;
* `-e_a - e_b` and `2e_a`;
* `e_b - e_a` and `-2e_b`;
* `e_b + e_a` and `-2e_b`.

If `l` has two distinct elements, any two roots are joined by a chain of linked roots
(`Relation.ReflTransGen (RootsLinked t)`).

Proof. Chains are reversible because linking is symmetric. Fix `a₀`; every root is joined to
`2e_{a₀}`.

* For `a ≠ a₀`, `2e_a` is joined to `-e_a - e_{a₀}`, which is joined to `2e_{a₀}`.
* For `b ≠ a`, `-2e_a` is joined to `e_a - e_b`, which is joined to `2e_b`.
* Each short root is linked to one of these long roots by hypothesis.

## Almost simplicity from a type C root datum

`isAlmostSimple_of_typeC`: let `k` be algebraically closed and `G` semisimple and nontrivial
(the range of `𝟙 G` is not `⊥`). Let `t` be a split maximal torus (`IsSplitTorus`,
`IsSplitSubtorus`, `IsMaximalTorus`). Let `e : l → X(T)` and `ν : l → X_*(T)` be dual
families: `⟨e_a, ν_c⟩ = 1` if `a = c` and `0` otherwise. Assume:

* every root of `t` has one of the forms above;
* `2e_a`, `e_b - e_a` and `-e_a - e_b` are roots (`a ≠ b`);
* a root datum `P` realizes `t` (`IsRootDatumOf t P`) and has coroot `ν_a` at the root `2e_a`;
* `l` has two distinct elements.

Then `G` is almost simple (`IsAlmostSimple`).

Proof.

* Roots are closed under negation, because they are the roots of `P` (Mathlib's
  `neg_mem_range_root_iff`). So `-2e_a` and `e_a + e_b` are roots too.
* The coroot at `-2e_a` is `-ν_a`. The index of `-2e_a` is the reflection of the index of `2e_a`
  in itself (Mathlib's `root_eq_neg_iff`). Mathlib's `coroot_eq_neg_iff` then gives the negated
  coroot.
* The pairing `P.pairing r r'` is `⟨P.root r, P.coroot r'⟩`, because the pairing of `P` is
  `latticePairing T`.
* Let `f_c(χ) = ⟨χ, ν_c⟩` be the `c`-th coordinate. By the description of the roots,
  `-2 ≤ f_c ≤ 2` on every root.
* Each of the four kinds of pairs above has pairing `-1` with the coroot of its long root:
  `⟨e_b - e_a, ν_a⟩`, `⟨-e_a - e_b, ν_a⟩`, `⟨e_b - e_a, -ν_b⟩` and `⟨e_b + e_a, -ν_b⟩` all
  equal `-1`.
* The coordinate `f_a` (first two kinds) or `-f_b` (last two) takes the value `-1` on the short
  root and `2` on the long root, and is at least `-2` on all roots. By
  `strict_combinations_of_coordinate`, no strict combination is zero or a root.
* `rootsLinked_of_pairing_eq_neg_one` (algebraically closed fields are infinite) shows that the
  pairs are linked. `reflTransGen_rootsLinked_of_typeC` and `isAlmostSimple_of_rootsLinked`
  finish the proof.

This argument uses no hypothesis on the characteristic. The long–short pairs used here have
noncommuting root groups also in characteristic two. (Short–short pairs with sum a long root
are not used.)

## The symplectic group

* `SymplecticMatrix.range_id_ne_bot l K`: for nonempty `l`, the split symplectic group over a
  field is nontrivial. The rational point `upper 1` has entry `1 ≠ 0` at
  `(inl i, inr i)`, so it is not the identity.
* `SymplecticMatrix.isAlmostSimple hl`: over an algebraically closed field `k`, the split
  symplectic group `SymplecticMatrix.groupScheme l (CommRingCat.of k)` is almost simple when
  `l` has two distinct elements. This instantiates `isAlmostSimple_of_typeC` with the diagonal
  torus `diagonalTorus l (CommRingCat.of k)` from `SymplecticMatrix.Torus`.
  * Semisimplicity is the `isSemisimple` field of `SymplecticMatrix.isSimplyConnected l k`.
    The torus is split and maximal (`isSplitTorus_diagonalTorus`,
    `isSplitSubtorus_diagonalTorus`, `isMaximalTorus_diagonalTorus`), and `P` is a root datum
    from `exists_rootDatum l k`.
  * `e_a` and `ν_a` are the characters and cocharacters with coordinates `Pi.single a 1` under
    the Library's `GeneralLinear.characterCoordEquiv l k` and
    `GeneralLinear.cocharacterCoordEquiv l k`. They are dual because the pairing is the dot
    product of coordinates (`GeneralLinear.latticePairing_coord`).
  * `longRoot l k a` (coordinates `Pi.single a 2`) is `2 • e_a`.
  * Description of the roots: by `mem_roots_iff`, a root has coordinates `w(x) - w(y)` with
    `x ≠ y` in `l ⊕ l`, where `w(inl a) = e_a` and `w(inr a) = -e_a`. The four cases for
    `(x, y)` give `e_a - e_b` (`a ≠ b`), `2e_a` or `e_a + e_b`, `-2e_a` or `-e_a - e_b`, and
    `e_b - e_a` (`a ≠ b`).
  * Required roots: `longRoot_mem_roots` gives `2e_a`. For `a ≠ b`, `diffRoot_mem_roots` gives
    `e_b - e_a`, and `neg_mem_roots` with `sumRoot_mem_roots` gives `-e_a - e_b`.
  * Long coroots: `cocharacterCoordEquiv_coroot_of_root_eq_longRoot` says the coroot at
    `2e_a` has coordinates `Pi.single a 1`, so it is `ν_a`.
  * Nontriviality is `range_id_ne_bot`.
* `Symplectic.isAbsolutelyAlmostSimple_of_isAlgClosed n h K`: suppose the coordinate model
  `SymplecticMatrix.groupScheme (Fin n) (CommRingCat.of k)` is almost simple over every
  algebraically closed field `k`. Then the standard model `Symplectic.groupScheme K n` is
  absolutely almost simple over every field `K`.
  * The base change to `AlgebraicClosure K` is isomorphic to the coordinate model over the
    algebraic closure. Use the base change of `comparisonIso K n` and `baseChangeModelIso`. So
    the base change is almost simple (`IsAlmostSimple.of_iso`).
  * Almost simplicity descends to `K` by the Library's `IsAlmostSimple.of_fieldExtension`.
  * The two facts together are the Library's `IsAbsolutelyAlmostSimple`.
* `Symplectic.isAbsolutelyAlmostSimple_groupScheme K n hn`: for `2 ≤ n` the standard symplectic
  group `Symplectic.groupScheme K n` over every field `K` is absolutely almost simple. Apply
  the previous item to `SymplecticMatrix.isAlmostSimple` with the distinct indices `0, 1` of
  `Fin n`. There is no hypothesis on the characteristic of `K`.

## Provenance

This is an internal module. Its proofs combine the cited Library and Mathlib results with
elementary computations. That the symplectic group `Sp_{2n}` is geometrically almost simple with
root system of type `C_n` is standard. See J. S. Milne, *Algebraic Groups* (2017), registered
source `milne-2017-algebraic-groups`: the type C example on printed p.459 (PDF p.475) and
Summary 21.98 on printed p.460 (PDF p.476). The argument here differs from the source: it uses
noncommuting long–short root pairs and the Library's normal-root dichotomy.
