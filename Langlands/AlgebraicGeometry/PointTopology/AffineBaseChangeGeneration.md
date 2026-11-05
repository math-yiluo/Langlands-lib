# Generation of the actual affine base-change coordinate algebra

Let `R` and `D` be commutative rings in an arbitrary common universe `u`,
with a specified `R`-algebra structure on `D`. Let `X` be an actual affine
scheme over `Spec R`. Write `B = AffineCoordinateRing R X` for its global
sections with the published structure algebra, and write `X_D` for the
actual pullback `ringBaseChange R D X`.

`ringBaseChangeCoordinateAlgEquiv` identifies `D ⊗[R] B` with
`AffineCoordinateRing D X_D` as `D`-algebras. It composes the inverse of
the canonical coordinate comparison for the tensor spectrum with the
coordinate pullback of `ringBaseChangeAffineOverIso`. Thus the codomain
is the global sections of the original pullback, with its specified base
structure.

`ringBaseChangeCoordinateAlgEquiv_one_tmul` proves that the image of
`1 ⊗ b` is pullback of `b` along the first projection `X_D → X`.
The proof applies the faithful spectrum functor to the two ring maps.
Naturality of the canonical affine isomorphisms and the published
first-projection formula for `ringBaseChangeAffineOverIso` give the
required equality of scheme morphisms.

`adjoin_range_baseChange_fst_eq_top` states that these first-projection
pullbacks generate the entire global-section algebra of `X_D` over `D`.
Mathlib's tensor-algebra generation lemma gives generation by all
`1 ⊗ b`; mapping that equality through the constructed algebra
equivalence and using the preceding projection formula proves the claim.
No finite-type or injectivity hypothesis is needed.

This is an internal derivation from the published affine base-change
presentation, its projection formula, the global-section comparison for
affine schemes, and tensor-algebra generation. It supplies coordinate
generation for a later arithmetic model comparison. It does not assert
existence of integral models, eventual integrality, maximal compactness,
or parabolic covering, and does not prove the host Iwasawa existence
statement.
