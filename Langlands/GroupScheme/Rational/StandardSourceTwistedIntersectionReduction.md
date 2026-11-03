# Standard source intersections from standard-face comparison

Worker 1493. This is an internal reduction for the published proposition
`StandardSourceTwistedIntersectionStatement`. It works over an arbitrary
field in universe `u`, and its subgroup-functor statements hold on every
test scheme. It proves one inclusion of each source identity
unconditionally. The reverse inclusions follow once, on one face, the
standard parabolic and unipotent subgroups are the dynamic subgroups of each
standard cocharacter. A comparison of standard cocharacters on that face
gives this. The unconditional
`StandardSourceTwistedIntersectionStatement` is not proved here.

## Definition

`StandardFaceDynamicComparison i ν` says that for every finite set `K` of
simple relative roots, the published
`StandardCocharacterDynamicComparison i ν (rootSet i ν K)` holds. That is,
any two standard cocharacters for the face `rootSet i ν K` give equal
dynamic parabolic, centralizer and unipotent subgroup functors. Like the
published single-face property, it does not assert that a standard
cocharacter exists. It packages the hypothesis of
`IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection`.

## Helper results

Four helpers are `private`: the three `Dynamic` orbit lemmas and the face
shift lemma. Worker 1107's candidate `6ce4961e`, module
`Langlands.GroupScheme.Rational.StandardRestrictedConjugation`, has been
approved but is not yet published. It contains lemmas with the same content,
and its face shift lemma has the same full name. The helpers here stay
private so that the two modules can be imported together.

- `Dynamic.orbit_groupHom_add_of_mem_centralizer`: let a point `g` be
  centralized by the cocharacter `lam`. Then `xi + lam` and `xi` give the
  same conjugation orbit of `g`. The two cocharacter values commute
  (`commute_cocharacter_of_mem_centralizer`), and `comp_groupHom_add` writes
  the value of the sum as a product. The corresponding iff statements,
  `Dynamic.mem_parabolic_groupHom_add_iff_of_mem_centralizer` and
  `Dynamic.mem_unipotent_groupHom_add_iff_of_mem_centralizer`, give dynamic
  parabolic and unipotent membership. They follow by rewriting
  `IsOrbitExtension` and `HasLimit`.
- `dynamicParabolic_comap_innerIso` and `dynamicUnipotent_comap_innerIso`:
  for a normalizer point `n`, take the preimage under conjugation by `n`, so
  a point `g` lies in it when `n g n⁻¹` lies in the original subgroup. This
  preimage of the dynamic parabolic, or unipotent subgroup, of `zeta` is the
  dynamic subgroup of `(cocharacterAut (normalizingAut i n)).symm zeta`. The
  proofs use `Dynamic.parabolic_eq_comap_of_iso`,
  `Dynamic.unipotent_eq_comap_of_iso` and `groupHom_cocharacterAut_comp`.
- `latticePairing_cocharacterAut_symm`: this inversely transported
  cocharacter pairs with `α` as `zeta` pairs with
  `schemeWeylCharacterAction i (mk n) α`. It follows from
  `latticePairing_characterAut_cocharacterAut` and
  `schemeWeylCharacterAction_mk`.
- `IsStandardCocharacter.exists_add_zsmul_of_face`: suppose there are
  finitely many simple relative roots and `K ⊆ J`. Let `mu` be standard for
  `J`, and let `xi` be zero on `K` and positive on `J \ K`. Then
  `xi + m • mu` is standard for `K` for some integer `m`. Choose `m` larger
  than every value `-⟨α, xi⟩` on the simple roots.
- `standard_eq_dynamic_of_signInclusions`: assume `ν` is generic and the
  relative roots are closed under negation. Assume also the two inclusion
  criteria in the form of `RelativeRootSignInclusionsStatement` for this
  torus. The first criterion says that `P(zeta) ≤ P(eta)` holds exactly when
  every root nonnegative on `zeta` is nonnegative on `eta`. The second says
  that `U(zeta) ≤ U(eta)` holds when every root positive on `zeta` is
  positive on `eta`. Then for every `eta` standard for `J`, the published
  `standardParabolic i ν J` equals `Dynamic.parabolic (eta)` and
  `standardUnipotent i ν J` equals `Dynamic.unipotent (eta)`. The parabolic
  equality is the published
  `dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter`, which
  uses only the sufficient direction of the first criterion. For the
  unipotent equality, `standardUnipotent_le_dynamicUnipotent` gives one
  inclusion. For the other, a point of `U(eta)` lies in `U(eta')` for every
  standard `eta'` for `J`. Indeed `eta` and `eta'` have the same root signs by
  `IsStandardCocharacter.haveSameRelativeRootSigns`, so the second criterion
  applies.

## The source comparison

`IsRelativeWeylCoxeterRealization.exists_standardCocharacter_intersectionSubset`
assumes a Coxeter realization, a generic `ν`, a minimum representative `w`
of `W_I w W_J`, `zeta` standard for `I` and `mu` standard for `J`. Let `xi`
pair with each `α` as `zeta` pairs with `w α`. Then some `xi + m • mu` is
standard for `K = intersectionSubset cs I J w`. On `J`, the published
`mem_intersectionSubset_iff_pairing_eq_zero` gives vanishing exactly on `K`.
The published `pairing_weyl_nonneg_of_mem_closure` gives nonnegativity, hence
positivity on `J \ K`.

`IsRelativeWeylCoxeterRealization.exists_source_comparison` assumes finitely
many simple roots. Let `n` lift `w`, and let `zeta` be standard for `I`. It
gives an `eta` standard for `K` with the following property. On every point
of the standard Levi `standardLevi i ν (rootSet i ν J)` over any test
scheme, membership in the preimage of `Dynamic.parabolic (zeta)` under
conjugation by `n` is equivalent to membership in `Dynamic.parabolic (eta)`.
The same holds for `Dynamic.unipotent`. The proof takes `mu` from
`exists_standardCocharacter_finset` and `xi` as the inverse transport of
`zeta`. It sets `eta = xi + m • mu`. A point of `L_J` is centralized by
`mu`, hence by `m • mu` (`Dynamic.centralizingCocharacters`), so the orbit
lemma above removes `m • mu`.

## Source identities

- `IsRelativeWeylCoxeterRealization.standardLevi_inf_standardParabolic_le`
  and `...standardLevi_inf_standardUnipotent_le` prove
  `L_J ⊓ P_K ≤ L_J ⊓ comap(Int(n), P_I)` and
  `L_J ⊓ U_K ≤ L_J ⊓ comap(Int(n), U_I)`. Here `P`, `L` and `U` are the
  published standard parabolic, Levi and unipotent functors of the root
  sets. They assume only the Coxeter realization, genericity of `ν` and
  finitely many simple roots. They hold for every minimum representative
  `w`, every lift `n` and every test scheme. Each standard `zeta` for `I` is
  checked through its `eta` from the source comparison.
- `IsRelativeWeylCoxeterRealization.standardSource_eq_of_standard_eq` proves
  both equalities for one `w` and `n`. It assumes that for every `eta`
  standard for the face of `K`, `P_K` equals `Dynamic.parabolic (eta)` and
  `U_K` equals `Dynamic.unipotent (eta)`. One standard `zeta` for `I` comes
  from `exists_standardCocharacter_finset`. Its `eta` from the source
  comparison gives the reverse inclusions, through this identification.
- `IsRelativeWeylCoxeterRealization.standardSource_eq_of_comparison` proves
  the same two equalities, assuming instead
  `StandardCocharacterDynamicComparison` for the face of `K`. Then
  `StandardCocharacterDynamicComparison.standard_eq_dynamic` supplies the
  hypothesis of the previous theorem.
- `IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection_of_standard_eq`
  derives the published `IsStandardSourceTwistedIntersection i ν cs`. It
  assumes the identification of the previous two items on every finite face.
- `IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection`
  derives the same property from `StandardFaceDynamicComparison i ν`.

## Conditional assemblies

The conclusion of each of the three theorems is exactly
`StandardSourceTwistedIntersectionStatement.{u}`. They prove none of their
hypotheses. In each, connected reductivity gives the affine and smoothness
instances, and maximal splitness gives the monomorphism. The published
`IsSplitTorus.finite_simpleRelativeRoots` gives finiteness of the simple
roots.

- `standardSourceTwistedIntersectionStatement_of_standardCocharacterStatement`
  assumes the published `StandardCocharacterStatement.{u}`. For every finite
  `K`, its equality conclusion gives the face comparison through
  `standardCocharacterDynamicComparison_iff`.
- `standardSourceTwistedIntersectionStatement_of_negation_of_signs` assumes
  the published `RelativeRootNegationStatement.{u}` and
  `RelativeRootSignsDetermineDynamicStatement.{u}`. Any two standard
  cocharacters for a face have the same relative-root signs, by
  `IsStandardCocharacter.haveSameRelativeRootSigns` together with negation
  closure. The sign statement then identifies their dynamic subgroups.
- `standardSourceTwistedIntersectionStatement_of_negation_of_signInclusions`
  assumes the published `RelativeRootNegationStatement.{u}` and
  `RelativeRootSignInclusionsStatement.{u}`. On every finite face,
  `standard_eq_dynamic_of_signInclusions` identifies the standard parabolic
  and unipotent subgroups with the dynamic subgroups of each standard
  cocharacter. `isStandardSourceTwistedIntersection_of_standard_eq` then
  applies.

## Scope

No axioms are introduced. The genuinely structural input is the
identification of `P_K` and `U_K` with the dynamic subgroups of the
standard cocharacters for the face `K`. This comes from the statements named
in the assemblies, which are open here. The half inclusions
and the comparison lemma are unconditional. They cover the empty simple-root
type, nonreduced relative root systems and nonreduced test schemes. No lift
is preferred.
