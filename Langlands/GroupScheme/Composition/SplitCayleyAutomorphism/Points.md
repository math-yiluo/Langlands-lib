# Points and Lie algebra of the split Cayley automorphism group scheme

Here `Aut = (CayleyDatum.split K).automorphismGroup` is the automorphism group scheme of Zorn's
split Cayley algebra over a field `K`, cut out of `GL₈` by the automorphism ideal.

- `isAutomorphismMatrix_split_iff`, `mem_automorphismSubgroup_split_iff`: for the split datum, a
  matrix in `GL₈(A)` is an automorphism matrix exactly when (as a linear map) it satisfies
  `SplitCayley.IsAutomorphism`, i.e. fixes Zorn's unit and preserves Zorn's product over `A`.
- `pointsEquiv K T`: the group of `T`-points of `Aut`, for every test scheme `T` over `K`, is the
  group of automorphism matrices over the global sections of `T`. `pointsEquiv_naturality`
  states that restricting along `T' ⟶ T` applies the pullback map on global sections to every
  matrix entry, and `pointsEquiv_inclusion` states that the inclusion into `GL₈` is the inclusion
  of matrices.
- `mono_automorphismInclusion`: the inclusion of `Aut` into `GL₈` is a monomorphism.
- `affinePointsEquiv K S`, `affinePointsEquiv_inclusion`: the same description on affine test
  schemes `Spec S`, with matrices over the `K`-algebra `S`.
- `lieMatrix`: the `A`-linear coordinate map from the Lie algebra of `Aut` (its Lie kernel over
  `A`) to `8 × 8` matrices over `A`. It is built from the inclusion into `GL₈` and the published
  coordinates of the Lie algebra of `GL₈`. `lieMatrix_injective` states that it is injective.
- `affinePointsEquiv_lieKernel`: the dual-number point of a Lie kernel element `X` has matrix
  `1 + ε · lieMatrix X`.
- `lieMatrix_mulVec_unit_and_isDerivation` and `exists_lieMatrix_eq`: the image of `lieMatrix` is
  exactly the set of matrices `Y` that kill Zorn's unit and are derivations of Zorn's product.
  Both directions are proved with `isAutomorphism_one_add_epsilonMatrix_iff` from
  `Derivations.lean`.

All statements are internal to this development and are proved by unfolding the published
corepresentation and Lie-algebra infrastructure.
