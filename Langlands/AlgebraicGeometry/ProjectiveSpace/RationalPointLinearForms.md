# Linear forms through a rational point of projective space

This module works over a field `K` and a natural number `m`. It uses the
coordinate ring `ProjectiveCoordinateRing K m = MvPolynomial (Fin (m + 1)) K`
of `ProjectiveSpace K m`, graded by total degree (`projectiveSpaceGrading K m`).
It proves that a `K`-point of `ProjectiveSpace K m` is determined by the linear
forms that vanish there. Here "vanish at a point" means "lie in the point's
homogeneous prime".

## Pure algebra

- `lineRestriction c` is the `K`-algebra map
  `ProjectiveCoordinateRing K m → K[t]` sending `X j` to `c j • t`. It restricts
  polynomials to the line through the vector `c`.
- `sub_aeval_lineRestriction_mem`: suppose an ideal `I` contains every relation
  `X j - C (c j) * X k`. Then each polynomial `h` is congruent modulo `I` to its
  line restriction evaluated at `X k`. The proof compares two `K`-algebra maps
  into `ProjectiveCoordinateRing K m ⧸ I` on the variables
  (`MvPolynomial.algHom_ext`).
- `eq_zero_of_aeval_X_mem`: let `Q` be a homogeneous prime with `X k ∉ Q`. If a
  univariate polynomial `p` satisfies `p(X k) ∈ Q`, then `p = 0`. Indeed, if
  `p ≠ 0`, the top homogeneous component of `p(X k)` is
  `leadingCoeff p • X k ^ natDegree p`. That component lies in `Q` because `Q`
  is homogeneous. Then `X k ^ natDegree p ∈ Q`, so `X k ∈ Q` because `Q` is
  prime, a contradiction.
- `mem_iff_lineRestriction_eq_zero`: let a homogeneous prime `Q` contain the
  relations `X j - C (c j) * X k` but not `X k`. Then `Q` is exactly the kernel
  of `lineRestriction c`. This combines the two previous lemmas.
- `linearRelation_mem`: `X j - C a * X k` has degree one.

## Points

- `eq_of_forall_linear_mem`: let a point `P` satisfy `X k ∉ P` and
  `X j - C (c j) * X k ∈ P` for all `j`. Let `Q` be a point whose homogeneous
  prime contains every degree-one element of `P`. Then `Q = P`. Proof: `Q`
  contains the same relations. It cannot contain `X k`: otherwise it would
  contain every `X j` and hence the irrelevant ideal, which is impossible for a
  point of `Proj`. By `mem_iff_lineRestriction_eq_zero`, both primes are then
  the kernel of `lineRestriction c`.
- `exists_linearCoordinates_of_section`: let
  `σ : Spec K ⟶ ProjectiveSpace K m` be a section of the structure morphism.
  Then there are `k` and `c : Fin (m + 1) → K` such that `X k` is not in the
  homogeneous prime of `σ(pt)`, and every `X j - C (c j) * X k` is in it. The
  proof works as follows.
  - Some coordinate chart `D₊(X k)` contains `σ(pt)`.
  - `σ` lifts through the chart's open immersion
    `Proj.awayι … (X k)`, which is
    `Spec (HomogeneousLocalization.Away … (X k)) ⟶ ProjectiveSpace K m`. The lift
    is `Spec.map ψ` for a ring map `ψ`. Because `σ` is a section over `K`, `ψ`
    is `K`-linear on `algebraMap K`.
  - Take `c j = ψ (X j / X k)`. The chart preimage of `D₊(X j - c j X k)` is the
    basic open of the element `X j / X k - c j`, which `ψ` kills. So the
    relation lies in the prime of `σ(pt)`.

  To avoid mismatches between `Proj` and `ProjectiveSpace`, the chart inclusion
  is introduced as a variable `ι` with an equation `hι`. Each chart fact is
  then proved after `subst hι` from the Library lemmas
  `isOpenImmersion_affineOpenCover_f`, `affineOpenCover_opensRange`,
  `affineOpenCover_comp_toSpec` and Mathlib's `Proj.awayι_preimage_basicOpen`.

## Provenance

These are standard facts about rational points of projective space over a
field. No single source statement corresponds to them. They are internal helper
lemmas for the reduction of the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 7.7) to a
Bezout count. In that reduction they identify the base locus of the linear forms
through the image of the origin. The module only proves these algebraic and
pointwise facts; it does not prove the target.
