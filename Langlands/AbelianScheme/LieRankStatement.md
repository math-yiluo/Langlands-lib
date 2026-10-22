# Local freeness and rank targets for relative Lie modules

For an arbitrary scheme `S` and actual abelian scheme
`A : Langlands.AbelianScheme S`, this module states two properties of the
constructed module `A.Lie = dual(e* Omega_(A/S))`.

`LieFiniteLocallyFreeStatement A` asserts both Mathlib local freeness and
finite type of this actual sheaf of `O_S`-modules. These predicates express
the finite locally free condition without selecting a single rank on the
whole base. A locally free sheaf which is locally finitely generated has
finite local bases: near a point, finitely many generators involve only
finitely many coordinates of a local free presentation, so after shrinking
the remaining coordinates vanish. No quasi-compactness or connectedness of
`S` is assumed.

`LieRankStatement A g` asserts that `A.HasRelativeDimension g` implies
`Langlands.Scheme.Modules.IsLocallyFreeOfRank A.Lie g`. The conclusion uses
the accepted predicate of covering local bases whose index sets are each
equivalent to `Fin g`. The hypothesis is the accepted abbreviation for
Mathlib `SmoothOfRelativeDimension g A.X.hom`, defined using affine
neighborhoods on which the morphism is standard smooth of relative
dimension `g`. Thus the statement does not define relative dimension by
the desired rank of the Lie module. It also does not assume that every
abelian scheme on a disconnected base has a single global relative
dimension. On the empty base it makes no rank uniqueness claim.

`LieLocalFreenessRankStatement A` is the conjunction of the finite local
freeness target and the rank target for every natural number `g`. It is
the combined target for a later proof task. All three declarations are
proposition definitions; this module proves none of them.

## Derivation from the sources

The Stacks Project, retained Section 29.35, Lemma 29.35.12 (tag 02G1),
states that the relative differential sheaf of a smooth morphism is finite
locally free and that its rank at a point equals the dimension of the fibre
there. Definition 29.35.13 (tag 02G2) gives the constant relative-dimension
convention. Mathlib's standard-smooth affine-neighborhood condition is its
algebraic presentation of that convention. The formal bridge from this
condition to the constructed differential sheaf is part of the later proof
obligation, not a theorem supplied here.

The accepted abelian-scheme bundle supplies smoothness. Pulling a local
finite basis of the relative differential sheaf back along the identity
section gives a basis of the cotangent sheaf at the identity, with the
same number of elements. Stacks Definition 17.14.1 (tag 01C6) gives this
local-basis meaning of finite local freeness, and Lemma 17.14.3 (tag 01C8)
states preservation of local freeness by pullback. Dualizing a finite
free module sheaf gives the dual basis and preserves its size. This last
step uses the internal Hom defined in Stacks Section 17.22, whose sections
are morphisms of restricted module sheaves. These elementary local-basis
arguments explain the derived Lie targets; no assumption that dualization
commutes with arbitrary pullback for arbitrary modules is needed.

Registered source locations:

- `stacks-smooth-differential-rank-2026-10-22`, SHA256
  `a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`,
  `01V4.html`, Lemma 29.35.12 (02G1) and Definition 29.35.13 (02G2).
- `stacks-local-freeness-invertibility-sections-2026-10-21`, SHA256
  `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
  `01C5.html`, Definition 17.14.1 (01C6) and Lemma 17.14.3 (01C8).
- `stacks-relative-differentials-internal-hom-2026-10-21`, SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
  `01CM.html`, opening internal-Hom definition.

Functoriality, endomorphism actions and a base-change comparison are outside
these rank targets. This statement unit neither supplies an assumed tangent
module nor replaces the existing concrete Lie construction.
