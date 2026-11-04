# One-dimensional unipotent groups over perfect fields are vector groups

Worker 716. This module proves the published statement
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement.{u}`
(module `Langlands.GroupScheme.Unipotent.OneDimensionalStatement`) as
`Langlands.GroupScheme.perfectFieldOneDimensionalUnipotent`, at an arbitrary
universe `u`. The statement and its source are documented in that module: the
converse assertion of J. S. Milne, *Algebraic Groups* (2017), 14.58, printed
p.298, with the classification of Corollary 14.53. The Lean proof does not
follow Milne's route. It uses the direct Hopf-algebraic argument of the
modules `Cocycle`, `Additive`, `Hopf`, `Invariant`, `Relation`, `Core`,
`Dimension` and `Geometry` in this directory, summarized below.

## Results

- `nonempty_iso_of_primitive_bijective`: let `y` be a primitive element of the
  coordinate algebra `B` of a corepresented group with `aeval y : k[X] → B`
  bijective. Then the corepresented group is isomorphic, as a group scheme, to
  `VectorGroup.groupScheme (CommRingCat.of k) 1`.
- `perfectFieldOneDimensionalUnipotent`: the target statement.

## Implemented argument

**The isomorphism.** The Library lemma `isPrimitiveFamily_of_isPrimitiveElem`
turns `y` into a one-element primitive family. `VectorGroup.quotientMap` then
gives a group-scheme homomorphism `q` to the one-dimensional vector group. Its
underlying scheme map is the spectrum of
`MvPolynomial.aeval (fun _ : Fin 1 => y)` (`VectorGroup.quotientMap_left`).
That evaluation factors as `aeval y ∘ MvPolynomial.uniqueAlgEquiv`, so it is
bijective. Its spectrum is therefore an isomorphism of schemes. Since
`Over.forget` reflects isomorphisms, `q.hom.hom` is an isomorphism in the
over category. `Grp.mkIso` turns it into an isomorphism of group objects,
using the monoid-homomorphism laws `IsMonHom.one_hom` and `IsMonHom.mul_hom`
of `q`.

**The theorem.** Let `k` be perfect and `U` a group scheme over `Spec k` with
`SmoothOfRelativeDimension 1 U.X.hom`, `IsAffineHom U.X.hom`, connected
underlying space, and `IsUnipotent U`.

1. `U.X.left` is affine (`isAffine_of_isAffineHom` over the affine base).
   `AffineCoordinates.groupSchemeIso U` gives an isomorphism `eU` from the
   corepresented group of `U`'s chosen coordinate algebra to `U`.
2. The hypotheses are transported along `eU`:
   - The structure map of the corepresented group is `eU.hom.left ≫ U.X.hom`
     (`Over.w`). An isomorphism is smooth of relative dimension `0`, so
     Mathlib's composition instance gives relative dimension `0 + 1`.
   - Connectedness transfers through the homeomorphism
     `Scheme.homeoOfIso`.
   - Unipotence transfers by `IsUnipotent.of_iso`.
3. `exists_primitive_bijective_of_smooth` (module `Geometry`) gives a
   primitive `y` with `aeval y` bijective. `nonempty_iso_of_primitive_bijective`
   gives an isomorphism from the corepresented group to the vector group.
   Composing with `eU.symm` gives `U ≅ VectorGroup.groupScheme (CommRingCat.of k) 1`.
4. The Library equivalence
   `RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso` converts this
   isomorphism into `RelativeRoot.IsVectorGroupOfDimension U 1`.

## Outline of the algebraic core

For the corepresented group with coordinate algebra `B`:

- `Geometry` and `Dimension` show that `B` and `B ⊗ B` are domains, and that
  `B` is finitely generated of Krull dimension at most one. Hence `B/(z)` is
  finite-dimensional for `z ≠ 0`, and any two elements are algebraically
  dependent. Nonconstant polynomials in a nonzero primitive element are not
  units, and `B` is not `k`.
- `Hopf` proves rigidity in a domain. It follows that the group is commutative
  (the comultiplication is cocommutative) and, in characteristic `p`, killed
  by `p`.
- `Invariant` uses unipotence (the Library fixed-vector theorem) and the
  cocycle lemma of `Cocycle`. It shows that if `B ≠ k[y]` for a primitive `y`,
  there is a primitive element outside `k[y]`.
- `Relation` shows that two dependent primitive elements satisfy an additive
  relation. `Additive` runs Euclid's algorithm for additive polynomials over
  the perfect field.
- `Core` chooses a nonzero primitive `y` minimizing `dim B/(y)` and concludes
  that `B = k[y]`.
