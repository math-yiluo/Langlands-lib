# Opposite Jacquet transport from actual point-root comparisons

This derived supporting construction uses the original point-root comparisons
of the rational rank-one self-association target. It does not prove that target.
The field universe and the smooth representation carrier universe are independent.

The field-level theorem
`associatedOpposite_standardGroups_of_pointRootSigns` uses a connected reductive
group scheme, its actual maximal split torus, the displayed generic cocharacter,
a relative root system, and `StandardCocharacterStatement`. It retains the actual
point-normalizer and full-centralizer comparisons, the actual finite point Coxeter
system, its root-length and positive-simple-reflection comparisons, and the
minimality and associated-subset laws. For every finite simple-root subset `J`,
every point-normalizer lift `n` of `longestRep cs J`, and every standard
cocharacter `ζ` for `J`, it identifies the associated standard parabolic and
radical with the pullbacks of the opposite dynamic parabolic and radical under
the inner automorphism of the scheme-normalizer lift of `n`. It also identifies
the associated standard Levi with the pullback of the original standard Levi.
The identities are subgroup-functor identities on every test scheme.

The proof applies the published
`isStandardCocharacter_associatedOpposite_of_pointRootSigns` to
`ξ = associatedOppositeCocharacter i ((normalizerEquiv i hN).symm n) ζ`.
The standard-cocharacter premise identifies the three associated standard
subgroups with the dynamics of `ξ`. The published opposite-cocharacter
pullback identities give the parabolic and radical equalities. For the Levi,
`Dynamic.centralizer_eq_comap_of_iso` gives the corresponding pullback identity;
`Dynamic.centralizer_inverseCocharacter` and the standard comparison for `ζ`
identify its target with the original standard Levi. No scheme Coxeter
realization or separate associated-opposite transport assertion is assumed.

`associatedOpposite_mem_of_pointRootSigns` evaluates these identities at the
identity test object. The scheme-normalizer comparison preserves the underlying
rational point. The resulting membership identities therefore use the same
specified actual point `n`:

* the associated parabolic contains `x` if and only if the opposite parabolic
  contains `n * x * n⁻¹`;
* the associated Levi contains `x` if and only if the original Levi contains
  `n * x * n⁻¹`;
* the associated radical contains `x` if and only if the opposite radical
  contains `n * x * n⁻¹`.

Over a nonarchimedean local field, the ambient group has exactly `pointTopology`,
with the displayed locally compact and nonarchimedean instances.
Closedness of each standard radical remains explicit; closedness of the opposite
radical comes from the published affine dynamic representability result.
The standard and opposite semidirect decompositions are the published
constructions from `StandardCocharacterStatement`, with the exact original and
associated Levi subgroups.

`associatedOppositeJacquetLinearEquiv` is an actual complex linear equivalence
from the carrier of normalized opposite Jacquet restriction to the carrier of
associated standard Jacquet restriction, for every smooth representation.
Normalized Jacquet restriction has the same carrier as the actual radical
coinvariants. The construction applies `coinvariantsTranslateEquiv` with
`g = n⁻¹` and the proved radical membership identity. Its inverse is translation
by `n`. The theorem `associatedOppositeJacquetLinearEquiv_mk` records the exact
formula `[v] ↦ [A(n⁻¹)v]`. `associatedOppositeJacquet_subsingleton_iff` transfers
vanishing in both directions by the injectivity of this equivalence and its
inverse.

The linear equivalence concerns carriers; it makes no claim of equivariance
between actions of two different Levi groups without pullback. It requires
neither irreducibility, admissibility nor unitarity. No maximal-proper-subset or
nonempty-root assumption is added.

All content is derived from the named published cocharacter, subgroup-functor
and coinvariant transport constructions. It supplies no scalar character,
compact-coefficient theorem, admissibility, square integrability, reciprocal
Haar character identity or reducibility-to-self-association proof. It introduces
no use of classification, character independence, the geometric lemma,
adjointness or a cuspidal-support theorem.

The 1 local instance has module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
