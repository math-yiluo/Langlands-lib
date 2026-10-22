# The unramified normalization of a full correspondence

Author: Worker 7. This module states the unramified normalization of the full
local Langlands correspondence for `GL_n(F)`. Unramified Weil–Deligne
parameters (inertia acts trivially and the monodromy is zero) correspond to
the irreducible representations with a nonzero `GL_n(O_F)`-fixed vector. The
parameter `⊕_i (χ_i ∘ τ_F, 0)`, for unramified quasi-characters `χ_i`,
corresponds to the spherical constituent of the normalized principal series
induced from `χ_1 ⊗ ⋯ ⊗ χ_n`. These are conditions on a given full map; no
family is constructed and nothing is proved.

## Definitions

`F : PadicField p` carries its canonical topological data and canonical
valuation. Ranks are written `r + 1`, with `r : ℕ`, so that the published
integral subgroup and block shapes apply without casts.

- `sphericalSubgroup F r` is `GL_(r+1)(O_F)`, the published
  `Conductor.integralSubgroup` of the canonical valuation ring: the image of
  the integral invertible matrices in `GL_(r+1)(F)`. It is hyperspecial.
- `IsSphericalClass F π`: some representative of the class `π` (an
  irreducible admissible representation, `AutomorphicRelations`) has a
  nonzero vector fixed by `GL_(r+1)(O_F)`, using the published `fixedVectors`.
- `IsUnramifiedParameterClass F D`: the parameter class `D` is the class of
  `(A, 0)` for a Weil representation `A` that is unramified in the published
  sense (`FiniteRepresentation.IsUnramified`: every inertia element acts as
  the identity). So `D` has zero monodromy and trivial inertia action.
- `borelShape r` is the block shape of `GL_(r+1)` with `r + 1` blocks of size
  one; its standard parabolic is the upper Borel subgroup.
- `principalSeries F r χ`, for `χ : Fin (r + 1) → QuasiCharacter F`, is
  Worker 23's published `normalizedProductInduced` for `borelShape r` of the
  characters `χ_i ∘ det` of `GL_1(F)`: Henniart's `i(χ_1, …, χ_(r+1))`,
  normalized parabolic induction from the upper Borel subgroup.
- `IsSubquotientOf ρ π`: some subrepresentation of `ρ` maps onto `π` by an
  intertwining map (Mathlib's `Subrepresentation` and
  `Representation.IntertwiningMap`). The carriers may lie in different
  universes. The published `SmoothRep.IsSubquotient` requires one carrier
  universe, which the induced representation and `π` need not share.
- `IsCharacterSumParameter F e χ D`: `D` is the class of the direct sum
  `⊕_i (χ_i ∘ τ_F, 0)`, where `χ_i ∘ τ_F` is `weilCharacter F e (χ i)` of
  `OperationCompatibility` and the sum is the published
  `WeilDeligneRepresentation.directSum`.

## Conditions

For a full map `c : FullMap F` and a reciprocity candidate `e`:

- `SphericalCompatibility F c`: for every `r` and every parameter class `D`
  of rank `r + 1`, `D` is unramified if and only if `c D` is spherical.
- `PrincipalSeriesCompatibility F e c`: for every `r` and all quasi-characters
  `χ_1, …, χ_(r+1)` that are unramified (published
  `IsUnramifiedCharacter`: trivial on `O_F^×`), there is a parameter class `D`
  with `IsCharacterSumParameter F e χ D`, and some representative of `c D`
  has a nonzero `GL_(r+1)(O_F)`-fixed vector and is a subquotient of
  `principalSeries F r χ`.
- `UnramifiedCompatibility F e c` is the conjunction.

The parameter class `D` is asserted to exist, so the condition does not hold
vacuously. The spherical constituent is not selected: the condition says that
`c D` is one. Uniqueness of the spherical constituent up to isomorphism, its
independence of the order of the `χ_i`, and its multiplicity one are theorems
(Borel 1979, §10.4) that are not proved in the Library and are not used here.

## Normalization

- The characters enter through `e`, the same reciprocity candidate as in the
  rank-one, determinant and twist conditions. With the geometric
  normalization of `IsGeometricReciprocity`, a geometric Frobenius `Φ` maps to
  a uniformizer `ϖ`, so `D(Φ)` has eigenvalues `χ_i(ϖ)`. Then
  `L(s, c D) = ∏_i (1 - χ_i(ϖ) q^(-s))⁻¹`; no extra power `q^((n-1)/2)`
  appears, because the induction is normalized.
- Diagnostic consequences (not stated in Lean): the trivial representation of
  `GL_2(F)` has parameter `ν^(-1/2) ⊕ ν^(1/2)` with zero monodromy.

## Sources and provenance

- Borel 1979, §10.4, printed pp.44–45 (PDF pp.53–54): a parameter is
  unramified if it is trivial on the additive group `G_a` (zero monodromy) and
  on inertia. For unramified `φ` with `φ(Fr) = (t, Fr)`, `Π_φ` consists of the
  constituents of the unramified normalized principal series `PS(χ)`, `t`
  representing `χ`, that have a nonzero vector fixed under a hyperspecial
  maximal compact subgroup; conversely an irreducible admissible
  representation with such a vector is a constituent of some `PS(χ)` and lies
  in `Π_φ` for the corresponding unramified `φ`. `PS(χ)` has at most one
  irreducible constituent with nonzero fixed vectors. For `GL_n`, `Π_φ` has
  one element, which is the correspondence here.
- Borel 1979, §7.2, printed p.39 (PDF p.48): for a class-one representation
  of a hyperspecial maximal compact subgroup the fixed space is
  one-dimensional and the local factor is `det(1 - r(g ⋊ σ) q^(-s))⁻¹` for
  the Satake class.
- Borel's own orientation of "Frobenius" is not used. The orientation is the
  geometric one of Henniart 2000, §1.1, printed p.439, imposed through `e`.
- Henniart 2002, §2.5, printed p.594 (PDF p.8): `i(π_1, …, π_r)` is
  normalized parabolic induction from the parabolic subgroup of upper block
  triangular matrices with successive diagonal block sizes `n_1, …, n_r`.
  The published `normalizedProductInduced` implements it and records its
  sources.

Source files:

- `borel-1979-automorphic-l-functions`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`
  (the retained Corvallis Part II volume, which also contains Tate 1979).
- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Scope

These are conditions on a family. The full correspondence predicate of this
task does not include them, because Henniart's characterization does not;
that a full correspondence satisfies them is a separate statement. The
module imports, and does not copy: `Conductor.integralSubgroup`,
`fixedVectors`, `normalizedProductInduced`, `IsUnramifiedCharacter`,
`FiniteRepresentation.IsUnramified`, `WeilDeligneRepresentation.directSum`
and `zeroMonodromy`, and this task's `Domains`, `AutomorphicRelations` and
`OperationCompatibility`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every condition returns `Prop`.
