# The full local Langlands correspondence for GL_n

Author: Worker 7. This module states the local Langlands correspondence for
`GL_n(F)`, for every p-adic field `F` and every rank `n ≥ 1`. It runs between
Frobenius-semisimple Weil–Deligne parameter classes, nonzero monodromy
allowed, and all irreducible admissible representations of `GL_n(F)`,
nongeneric ones included. It defines the correspondence predicate on a full
map and its existence and uniqueness statements, per field and over all
fields. It also states that a full correspondence restricts to the
supercuspidal correspondence and satisfies the unramified normalization. All
are propositions; none is proved, and no correspondence is an input.

## The correspondence predicate

A full map `c : FullMap F` (from `Domains`) assigns to each rank `n` and each
Frobenius-semisimple Weil–Deligne class of rank `n` an automorphic class of
rank `n`, so it preserves rank by its type. `IsFullCorrespondence F c` is the
conjunction of:

1. `RankwiseBijective F c`: every `c n` is a bijection.
2. `DualCompatibility F c`: the image of the dual parameter class is the smooth
   contragredient of the image.
3. There is a reciprocity candidate `e` with `IsGeometricReciprocity F e`
   (the published geometric normalization) such that:
   - `RankOneCompatibility F e c`: in rank one, the class of the character
     `χ ∘ e` is sent to `χ`, for every quasi-character `χ` of `F^×`;
   - `DeterminantCompatibility F e c`: the central character of `c D` at
     `e(w)` is `det D(w)`;
   - `TwistCompatibility F e c`: twists by all quasi-characters;
   - `FullFactorCompatibility F e c`: pair L- and epsilon-factors for all
     ranks, all pairs of parameter classes and every nontrivial additive
     character `ψ`, the epsilon factors for one local-constant system whose
     base reciprocity component is `e`.

The conditions are those of `OperationCompatibility` and
`FullFactorCompatibility`. The same `e` serves every condition that depends on
reciprocity, and the same map `c` serves every `ψ`. The reciprocity candidate
is existentially quantified with its normalization, so it is not an input.

## Statements

- `FullCorrespondenceExistence F`: some full map satisfies the predicate.
- `FullCorrespondenceUniqueness F`: any two full maps satisfying it are equal.
  Maps are functions on isomorphism classes, so equality means equal values on
  every class in every rank (`Domains.fullMap_ext`).
- `FullCorrespondenceExistsUnique F`: `∃! c`, the conjunction of the two.
- `FullCorrespondenceStatement`: for every prime `p` and every
  `F : PadicField p`, `FullCorrespondenceExistsUnique F`. This is the final
  unconditional statement: no correspondence, supercuspidal or full, is an
  input. Its universe parameters are the field universe `uF`, the parameter
  carrier universe `uP` and the representation carrier universe `uA`.
- `FullCorrespondenceRestrictionStatement F`: for every full map `c` with
  `IsFullCorrespondence F c`, there is a supercuspidal map `c0` with
  `IsSupercuspidalCorrespondence F c0` (`SupercuspidalSpecification`) and
  `ExtendsSupercuspidal F c0 c` (`Domains`): `c` sends the zero-monodromy
  class of every irreducible Weil class `σ` to the supercuspidal class
  `c0 σ`.
- `FullCorrespondenceUnramifiedStatement F`: for every full map `c` and every
  reciprocity candidate `e`, if `IsFullCorrespondence F c` and
  `IsGeometricReciprocity F e`, then `UnramifiedCompatibility F e c`
  (`UnramifiedNormalization`). That is, a parameter class is unramified
  exactly when its image is spherical, and the parameter `⊕ (χ_i ∘ e, 0)` of
  unramified quasi-characters `χ_1, …, χ_n` is sent to the spherical
  subquotient of the normalized principal series `i(χ_1, …, χ_n)`.

## Sources and provenance

- Harris–Taylor 2001, Introduction, printed pp.1–2 (PDF pp.9–10): with
  `Art_K` normalized so that geometric Frobenius elements correspond to
  uniformizers and a fixed nontrivial `ψ`, a local Langlands correspondence is
  a family of bijections between `Irr(GL_n(K))` and the `n`-dimensional
  Frobenius-semisimple Weil–Deligne representations, for every `n ≥ 1`, with
  properties 1 (rank one is class field theory), 2 (pair L- and epsilon
  factors), 3 (twists), 4 (determinant and central character) and 5
  (contragredients). "Henniart showed that there is at most one set of
  bijections with these properties", and Theorem A states existence for every
  finite extension `K` of `Q_p`. `IsFullCorrespondence` contains all five
  properties and bijectivity. `FullCorrespondenceStatement` is existence and
  uniqueness together.
- Henniart 2002, §1.1, printed p.588 (PDF p.2): `G(n)`, the classes of
  `n`-dimensional Φ-semisimple representations of `W'_F`, and `A(n)`, the
  classes of smooth irreducible representations of `GL_n(F)`, with the same
  reciprocity normalization. §1.5, printed p.590 (PDF p.4), Theorem: the
  bijections `π_n : G(n) → A(n)` extend the supercuspidal bijections `π^0_n`
  ((i)), are compatible with contragredients on `G_0(n)` ((ii)), and with
  pair L- and epsilon factors for all `n, n' ≥ 1` ((iii)).
  `FullCorrespondenceRestrictionStatement` is (i) for an arbitrary full
  correspondence. §1.8, printed p.592 (PDF p.6), Corollary: the family is
  characterized by rank one and the pair L- and epsilon identities
  (`FullCharacterizationStatement`), which gives uniqueness.
- Henniart 2002, §2.9, printed p.596 (PDF p.10): the full bijection satisfies
  `π(σ^∨) = π(σ)^∨` for all `σ ∈ G`.
- Borel 1979, §10.4, printed pp.44–45, and Henniart 2002, §2.5, printed p.594:
  the unramified correspondence and the principal series `i(χ_1, …, χ_n)`, as
  recorded in the published `UnramifiedNormalization`.

Source files:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `borel-1979-automorphic-l-functions`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`
  (the retained Corvallis Part II volume).
- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Interpretation

- **Every `ψ`.** Harris–Taylor and Henniart fix one nontrivial `ψ`. The
  predicate requires the factor identities for every `ψ`, with one map. For
  families with the central-character property, which the predicate also
  requires, the one-`ψ` and every-`ψ` forms agree (Henniart 2000, §1.3,
  remark, printed p.441); that remark is not proved in the Library. The
  correspondence of Theorem A satisfies the every-`ψ` form.
- **Direction.** Harris–Taylor state the properties for `rec_K`, from
  representations to parameters. The predicate states the same identities for
  the inverse direction, from parameters to representations, as Henniart
  2002 does; the maps are required to be bijective.
- **Dual compatibility on all of `G(n)`.** Henniart 2002, §1.5 (ii) states it
  on `G_0(n)`, and §2.9 for all `σ ∈ G`; Harris–Taylor property 5 is for all
  classes. The predicate requires it for all parameter classes.
- **Unramified normalization is derived.** Harris–Taylor's properties 1–5 do
  not list it, so it is not a conjunct of `IsFullCorrespondence`. It is the
  separate statement `FullCorrespondenceUnramifiedStatement`. It quantifies
  over every geometrically normalized `e`. The published, unproved
  `LocalClassField.WeilReciprocityExistenceUniqueness` says there is exactly
  one, so this agrees with using the `e` of the predicate.
- **Gamma is derived.** Gamma compatibility is not part of the predicate; it
  is `FullGammaFromFactorsStatement` of `FullGammaCompatibility`.
- **Restriction.** `FullCorrespondenceRestrictionStatement` asks for some
  supercuspidal correspondence `c0`. With
  `SupercuspidalCorrespondenceUniqueness` this `c0` is the supercuspidal
  correspondence. The statement includes that `c` maps irreducible Weil
  parameters onto supercuspidal classes, which Henniart 2002 derives in
  Corollary 1.6 (`FullCharacterizationExtendsStatement`).

## Scope

- Domains are the published actual class spaces: Frobenius-semisimple
  Weil–Deligne classes of the actual local Weil group, nonzero monodromy
  allowed, and isomorphism classes of irreducible admissible smooth complex
  representations of the actual `GL_n(F)`, nongeneric ones included.
- The field ranges over every `PadicField p`, every prime `p`. Fields of
  positive characteristic are not covered.
- The irreducible-Weil/supercuspidal correspondence is the separate
  `SupercuspidalSpecification`. The conditional assembly theorem, from a
  supercuspidal correspondence to a full one, is `ConditionalAssemblyStatement`
  of `AssemblyTheorems`.
- The module imports, and does not copy: this task's
  `FullFactorCompatibility`, `SupercuspidalSpecification`,
  `UnramifiedNormalization`, `OperationCompatibility` and `Domains`.
- This candidate also changes `UnramifiedNormalization.lean`. Its three local
  instances now have explicit names (`unramifiedFieldTopology`,
  `unramifiedGeneralLinearTopology`, `unramifiedGeneralLinearTopologicalGroup`).
  Before, `UnramifiedNormalization` and `ArithmeticFactors` both received the
  automatic name `instTopologicalSpaceCarrier_4`, so no module could import
  both. No other declaration changes; its only importer,
  `RankinSelberg/UnramifiedPairStatement`, uses `letI` and does not refer to
  the instance names.

## Validation

The module compiles in the project Lean service, together with the edited
`UnramifiedNormalization`, with no errors or warnings. There is no `sorry` and
no new axiom. Every definition returns `Prop`.
