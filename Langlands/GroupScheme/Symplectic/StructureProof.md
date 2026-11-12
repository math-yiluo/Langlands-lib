# Proof that the standard symplectic group is simply connected and absolutely almost simple

`Symplectic.structureStatement` proves the Library statement `Symplectic.StructureStatement` at
an arbitrary universe `u`: for every field `K` and every `n ≥ 2`, the standard symplectic group
`Symplectic.groupScheme K n` is simply connected (`IsSimplyConnected`) and absolutely almost
simple (`IsAbsolutelyAlmostSimple`). There is no hypothesis on the characteristic of `K`.

## Proof

The two conjuncts come from two modules.

* Simple connectedness is `Symplectic.isSimplyConnected_groupScheme K n` from
  `SymplecticMatrix.SimplyConnected`. That module works with the split symplectic group
  `SymplecticMatrix.groupScheme (Fin n) (CommRingCat.of K)` and its diagonal maximal torus
  `diag(t, t⁻¹)`. The long coroots at the roots `2e_a` are the coordinate cocharacters `e_a^∨`.
  So the coroots span the cocharacter lattice. This gives semisimplicity (by the Library's
  `splitSemisimpleRootDatum`) and simple connectedness (by `splitCorootSpanSimplyConnected`).
  The result is transported to the standard model along `SymplecticMatrix.comparisonIso`. This
  conjunct holds for every `n`.
* Absolute almost simplicity is `Symplectic.isAbsolutelyAlmostSimple_groupScheme K n hn` from
  `SymplecticMatrix.AlmostSimple`, which uses `2 ≤ n`. Over an algebraically closed field, the
  roots of the diagonal torus are `±2e_a` and `±e_a ± e_b` (`a ≠ b`). Linked long–short root
  pairs (pairing `-1`, root subgroups that do not commute) join every root to every other. The
  Library's normal-root dichotomy then shows that a smooth connected normal subgroup is trivial
  or everything (`Reductive.LinkedRootsAlmostSimple`). Almost simplicity over the algebraic
  closure of `K` descends to `K` by `IsAlmostSimple.of_fieldExtension`.

## Provenance

This is an internal assembly of the two results above. That `Sp_{2n}` is simply connected and
geometrically almost simple of type `C_n` is standard; see J. S. Milne, *Algebraic Groups*
(2017), Summary 21.98 (printed p.460). The proofs in the cited modules follow their own routes,
described in their Markdown files.
