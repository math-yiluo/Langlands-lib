# The irreducible-Weil/supercuspidal local Langlands correspondence

Author: Worker 7. This module states the local Langlands correspondence
between irreducible representations of the Weil group and supercuspidal
representations of `GL_n(F)`, for every p-adic field `F` and every rank
`n ≥ 1`. It defines the correspondence predicate on a supercuspidal map and
its existence and uniqueness statements, per field and over all fields. All
are propositions; none is proved, and no correspondence is an input.

The full correspondence (Frobenius-semisimple Weil–Deligne parameters with
nonzero monodromy, and all irreducible admissible representations) is a
separate statement of this task. This module covers only the zero-monodromy
irreducible case.

## The correspondence predicate

A supercuspidal map `c : SupercuspidalMap F` (from `Domains`) assigns to each
rank `n` and each continuous irreducible Weil class of rank `n` a supercuspidal
class of `GL_n(F)`. `IsSupercuspidalCorrespondence F c` is the conjunction of:

1. `SupercuspidalRankwiseBijective F c`: every `c n` is a bijection.
2. `SupercuspidalDualCompatibility F c`: `c n (σ^∨)` is the smooth
   contragredient of `c n σ`.
3. There is a reciprocity candidate `e` with `IsGeometricReciprocity F e` (the
   published geometric normalization) such that:
   - `SupercuspidalRankOneCompatibility F e c`: rank one is given by `e`;
   - `SupercuspidalDeterminantCompatibility F e c`: `ω_{c σ} ∘ τ_F = det σ`;
   - `SupercuspidalTwistCompatibility F e c`: twists by all quasi-characters;
   - `SupercuspidalFactorCompatibility F e c`: pair L- and epsilon-factors for
     all ranks, all pairs and every nontrivial additive character `ψ`, for one
     local-constant system whose base reciprocity component is `e`.

The conditions are those of `OperationCompatibility` and
`SupercuspidalFactorCompatibility`, which this module imports. The same `e`
serves every condition that depends on reciprocity, and the same map `c`
serves every `ψ`: the predicate is not `∀ ψ, ∃ c_ψ`. The reciprocity candidate
is existentially quantified with its normalization, so it is not an input.

## Statements

- `SupercuspidalCorrespondenceExistence F`: some `c` satisfies the predicate.
- `SupercuspidalCorrespondenceUniqueness F`: any two maps satisfying it are
  equal. Maps are functions on isomorphism classes, so equality means equal
  values on every class in every rank (`Domains.fullMap_ext` is the analogous
  extensionality for full maps).
- `SupercuspidalCorrespondenceExistsUnique F`: `∃! c`, the conjunction of the
  two.
- `SupercuspidalCorrespondenceStatement`: for every prime `p` and every
  `F : PadicField p`, `SupercuspidalCorrespondenceExistsUnique F`. Its
  universe parameters are the field universe `uF`, the parameter carrier
  universe `uP` and the representation carrier universe `uA`; Lean's
  universe-polymorphic family of propositions is the scope claim.

## Sources and provenance

- Henniart 2000, §1.1, printed p.439 (PDF p.1): the sets `G_F^0(n)` and
  `A_F^0(n)`, quasi-characters (footnote 1), one fixed nontrivial `ψ`, and
  the reciprocity map normalized so that geometric Frobenius elements
  correspond to uniformizers.
- Henniart 2000, §1.2, printed p.440 (PDF p.2): for each `n ≥ 1` a bijection
  `σ ↦ π(σ)` of `G_F^0(n)` onto `A_F^0(n)`, with properties 1) determinant
  and central character, 2) twists by quasi-characters, 3) contragredients,
  4) pair L- and epsilon-factors (JPSS factors). Section 1.3, printed
  pp.440–441: in rank one, property 1) forces local class field theory; the
  remark there says that, given 1), (4ε) for one `ψ` implies it for every
  `ψ`. Section 1.4, printed p.441 (PDF p.3): by induction on `n`, at most one
  family of bijections satisfies 1)–4).
- Henniart 2002, §1.3, printed p.589 (PDF p.3): the theorem of Laumon,
  Rapoport and Stuhler, Harris and Taylor, and Henniart, stated as the
  existence of maps `π_n^0 : G^0(n) → A^0(n)`, `π_1^0` given by local class
  field theory, with `π_n^0(σ^∨) = π_n^0(σ)^∨` and the pair epsilon identity
  for all `n, n' ≥ 1`; these maps are bijective. Section 1.4, printed p.589:
  this family is unique, by induction on `n` from Henniart 1993.

The predicate includes every property in Henniart 2000, §§1.2–1.3, plus
bijectivity. It requires the factor identities for every `ψ`; by the §1.3
remark this is equivalent to the one-`ψ` form for families satisfying
property 1), which the predicate also requires. That remark is not proved in
the Library. Henniart 2002, §1.3, lists fewer properties; the predicate here
is the stronger 2000 list, which the constructed correspondence satisfies.

Source files:

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Scope

- Domains are the published actual class spaces: continuous irreducible
  representations of the actual local Weil group, and supercuspidal classes of
  the actual `GL_n(F)` with arbitrary complex carriers.
- The field ranges over every `PadicField p`, every prime `p`. Fields of
  positive characteristic are not covered.
- Derived gamma compatibility is the separate module
  `SupercuspidalGammaCompatibility`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every definition returns `Prop`.
