# Split-source lifts from a recovered pair to a recovered reference facet

This internal composition compares two supplied recovered component models:
one realizes the exact full and neutral fixers of a pair of building points
`p, q`, and the other realizes the neutral zero fixer of a full reference facet
containing `p`. A supplied valid reductive quotient of the reference model has
no proper rational parabolic inclusions. One supplied integral split torus has
both a maximal split generic map to the original group and a maximal split
residue map to that reference quotient.

Under these hypotheses `UnramifiedPairFacetSplitSourceStatement` asserts an
actual generic-identity homomorphism between the lower neutral models and a
closed lift of that same integral split source into the pair model. Its
composite residue map to the reference quotient is exactly the supplied map.
The lift is maximal split on the residue fibre and on the generic fibre, and
its maximal-unramified units fix the original point `q`. The original group is
connected reductive over a nonarchimedean local field; its actual building and
zero datum remain supplied. The statement is in arbitrary universe and both
characteristics. Recovery and both neutral fixer formulas are explicit
hypotheses; no full-facet equality of full point fixers is asserted.

The implemented proof uses these published inputs:

* `UnramifiedZeroDatum.zeroFixer_eq_of_nonempty_subset_buildingFacet` and
  `MaximalUnramified.zeroFacetNoInversions` identify the zero fixer of `{p}`
  with that of the reference facet. The pair zero fixer is contained in it.
* `UnramifiedComponentModelRecovery.nonempty_neutralHom_iff`, applied with
  `IntegralModel.unramifiedSmoothHomExtension`, constructs the actual lower
  neutral-model homomorphism from this inclusion.
* `isMaximalTorus_specialFibreMap_of_unramified_full_pair` preserves every
  maximal torus through that homomorphism over the original residue field.
  Composition with the reference quotient preserves maximality by
  `IsMaximalTorus.comp_of_perfect_field_unipotent_kernel`, using its actual
  smooth connected unipotent radical and represented quotient.
* `IntegralModel.exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits`
  lifts the prescribed split residue source through this composite. Generic
  maximality uses the other maximal generic map from the identical source.
  The recovered neutral pair formula shows that its integral points fix `q`,
  which gives the asserted fixation of every maximal-unramified torus unit.

This derives a model comparison and a torus lift from explicit reference
inputs. Construction of those reference inputs and the final host theorem
remain separate obligations; this contribution makes no new independent
literature assertion.

The local arithmetic instances use explicit names, and the companion
`UnramifiedPairTorusImages` module now gives its eight local instances
unique names. This repairs generated declaration-name collisions when the
pair and recovered-apartment source modules are imported together. Their
instance definitions and all mathematical declarations and proof bodies
remain unchanged.
