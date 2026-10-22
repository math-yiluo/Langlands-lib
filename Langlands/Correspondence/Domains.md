# Actual domains and structural conditions for correspondence families

Author: Worker 7. This module fixes the parameter-side domains of the local
Langlands correspondence for `GL_n(F)` and the structural conditions on
families of maps between the class spaces. It states no part of LLC: the
normalized correspondence predicate and its existence and uniqueness are
separate modules of this task.

## Parameter class spaces

All parameter classes live over the published local Weil group
`Weil.Local.localWeilGroup F`, which is constructed from the field `F`. Its
inertia subgroup, geometric degree and norm character
`Weil.Local.localNormCharacter F` are also constructed from `F`; the norm
character has value `q⁻¹` at geometric degree one, where `q` is the actual
residue cardinality. No group, degree, norm character or Frobenius element is
an input to the declarations here.

- `WeilDeligneClass F n` is the published
  `Weil.Local.LocalFrobeniusSemisimpleParameterClassesOfRank F n`. Its members
  are isomorphism classes of complex Weil–Deligne pairs `(ρ, N)` of dimension
  `n` whose representation has an open kernel on inertia and in which every
  element of nonzero degree acts semisimply. The monodromy `N` is any
  nilpotent endomorphism satisfying the covariance rule, so nonzero monodromy
  is allowed. This is the full parameter domain.
- `IrreducibleWeilClass F n` is the published
  `Weil.Local.LocalContinuousIrreducibleWeilClasses F n`: isomorphism classes
  of `n`-dimensional complex representations of the local Weil group that are
  continuous for the usual topology of `ℂ` and irreducible. It is the domain of
  the supercuspidal part of the correspondence and is kept separate from the
  full domain.

`parameterForget` is the published `WeilDeligneRepresentation.ParameterRelations.forget`
at this local data: it sends a parameter class to the isomorphism class of the
underlying pair, forgetting the rank and parameter conditions.
`weilClassForget` is the published `FiniteRepresentation.forgetPropertyClass`
for the property "continuous and irreducible": it sends an irreducible Weil
class to the isomorphism class of the underlying representation.

## Maps and families

`FullMap F` is the type of rank-indexed maps
`WeilDeligneClass F n → AutomorphicClass F n` for every positive rank
`n : ℕ+`. Its codomain is the full class space of `AutomorphicRelations`, so
it includes nongeneric representations on carriers of any dimension.
`SupercuspidalMap F` is the type of rank-indexed maps
`IrreducibleWeilClass F n → SupercuspidalAutomorphicClass F n`, with the
supercuspidal class space of `SupercuspidalRelations` as codomain.
`FullFamily` and `SupercuspidalFamily` give one such map for every prime `p`
and every `PadicField F` over `p`. The field universe, the parameter carrier
universe and the automorphic carrier universe are independent. The four
aliases `FullMap`, `SupercuspidalMap`, `FullFamily` and `SupercuspidalFamily`
switch off the universe-occurrence linter locally, because their result
sorts join levels that remain separate in their bodies.

`TotalParameterClass F` and `TotalAutomorphicClass F` are the disjoint
unions over all positive ranks, and `fullTotalMap F c` is the map between
them given by the components of `c`. `parameterDimension F D` is the
dimension of the underlying pair class, computed by the published
`WeilDeligneRepresentation.classRank`. `parameterDimension_eq_rank` proves
that it equals the rank index, using the rank certificate carried by the
class.

`PreservesRank F c` says that the matrix rank of the image equals the
parameter dimension. `fullMap_preservesRank` proves it for every `c`: the
rank-indexed types already enforce it. It does not compare the matrix rank
with the dimension of an automorphic representation, which is in general
infinite.

`RankwiseBijective F c` and `SupercuspidalRankwiseBijective F c` say that
the map at each positive rank is a bijection. `fullMap_ext` says that two
full maps are equal when they agree at every rank and every class. These are
components of the statements, not the normalized correspondence: a
bijection by itself carries none of the compatibilities that characterize
LLC.

## Zero monodromy and extension

`IsZeroMonodromyOf F σ D` says that some representation `A` of the local
Weil group represents the class `weilClassForget F σ`, and the pair
`(A, 0)` given by the published `WeilDeligneRepresentation.zeroMonodromy`
represents `parameterForget F D`. Both equalities are equalities of actual
isomorphism classes, and no representative is chosen. The relation does not
assume that continuity is equivalent to an open kernel on inertia, nor that
the pair is Frobenius semisimple: membership of `D` in the parameter domain
is part of its type.

`ExtendsSupercuspidal F c0 c` says that for every positive rank and every
irreducible Weil class `σ` there exists a full parameter class `D` with
`IsZeroMonodromyOf F σ D` and `c n D` equal to the image of `c0 n σ` under
the inclusion `supercuspidalToAutomorphic`. The output `D` is asserted to
exist, so the condition cannot hold vacuously.

## Sources and provenance

Henniart 2000, section 1.1, printed p.439 (PDF p.1), defines the set
`G_F^0(n)` of isomorphism classes of continuous irreducible
`n`-dimensional complex representations of the Weil group and the
supercuspidal class set `A_F^0(n)`; section 1.2, printed p.440 (PDF p.2),
constructs a family of bijections between them, one for every `n ≥ 1`.

Henniart 2002, section 1.1, printed p.588 (PDF p.2), defines `G(n)`, the
isomorphism classes of `n`-dimensional Frobenius-semisimple representations of
the Weil–Deligne group, with the subset `G^0(n)` of irreducible
representations of the Weil group, and `A(n)` with the supercuspidal subset
`A^0(n)`. Section 1.3, printed p.589 (PDF p.3), states the theorem for
`G^0(n) → A^0(n)`. Section 1.5, printed p.590 (PDF p.4), states that the
family `π_n : G(n) → A(n)` satisfies `π_n(σ) = π_n^0(σ)` for `σ ∈ G^0(n)`;
`ExtendsSupercuspidal` formalizes this condition, using the zero-monodromy
pair to view `σ` as an element of the full domain. Sections 1.8, printed
pp.591–592 (PDF pp.5–6), and 2.7–2.9, printed pp.595–596 (PDF pp.9–10),
give the characterization and the extension to all classes; they are not
asserted here.

Tate 1979, section 4.1.2, printed p.20 (PDF p.29), defines a representation
`(ρ, N)` of the Weil–Deligne group: `ρ` has kernel containing an open
subgroup of inertia, and `N` is nilpotent with `ρ(w) N ρ(w)⁻¹ = ‖w‖ N`.
Section 4.1.3, same page, defines Frobenius semisimplicity, and section
4.1.5 states that `(ρ, N)` is irreducible exactly when `N = 0` and `ρ` is
irreducible. Section 4.1.7, printed p.21 (PDF p.30), states the expected
bijection between Frobenius-semisimple `n`-dimensional representations and
irreducible admissible representations of `GL(n, F)`, with irreducible
parameters corresponding to cuspidal representations. Section 1.4.1, printed
p.6 (PDF p.15), fixes the convention that uniformizers correspond to
geometric Frobenius, and section 1.4.6, printed p.7 (PDF p.16), defines the
norm `‖w‖`; the published local norm character follows these conventions.

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The parameter spaces, the forgetful maps and the zero-monodromy pair are
published Library declarations, imported and not copied:
`Langlands.Weil.Local.Parameters` and `Langlands.Weil.Local.Assembly` (the
local Weil group, its inertia, degree and norm character, and the class
spaces), `Langlands.WeilDeligne.Parameters` and `Langlands.WeilDeligne.Basic`
(Frobenius-semisimple parameter classes, `classRank`, `zeroMonodromy`),
`Langlands.WeilDeligne.ParameterRelations` (Worker 1's `forget`) and
`Langlands.Weil.Representation.Basic` (`forgetPropertyClass`). The automorphic
class spaces come from this task's `AutomorphicRelations` and
`SupercuspidalRelations`.

## Validation

The module compiles in the project Lean service without errors or warnings,
together with `SupercuspidalRelations` and `OperationCompatibility`.
