# Field fibres after inverting an arithmetic coefficient

This internal comparison module constructs an actual finite enlargement of a
number-field S-integer ring that makes a supplied nonzero element invertible.
It then transfers a supplied principal-open connected-reductivity premise to
all actual field-valued fibres over the enlarged ring. It does not prove the
principal-open premise or construct integral models.

## Arithmetic construction

For a number field `F : Type u`, finite set `S` of its finite places, and nonzero
`r` in the actual subalgebra `(S : Set (FinitePlace F)).integer F`,
`Langlands.Global.exists_numberFieldSIntegers_isUnit` produces an index
`T : AdelicLevelIndexAbove S`. Thus `T.val` is finite and contains the original
`S`. Its conclusion is `IsUnit (numberFieldSIntegersMap F T.property r)`,
where the map is the literal subring inclusion from
`Langlands.Global.AdelicLevelModelTransition`, not a chosen isomorphism.

The proof applies the published
`exists_mem_numberFieldSIntegersAbove F S` to `(r : F)⁻¹`.
This places that inverse in the actual enlarged integer subalgebra. It then
proves that multiplication of the included `r` by this element is one.
Subtype extensionality reduces the equality to the field identity
`r * r⁻¹ = 1`; the original `r ≠ 0` implies its image in `F` is nonzero.
`isUnit_iff_exists_inv` gives the unit property in the enlarged ring itself.
The noncomputable definition `numberFieldSIntegersUnitStage` chooses such a
`T` and packages it together with the proved unit property as a subtype.
No assertion of canonicity or minimality is made.

## Exact field and geometric-fibre comparisons

`Langlands.GroupScheme.isReductive_of_fieldReductive` concerns any commutative
ring `R : Type u` and actual group scheme `G` over `Spec R`. It requires
smoothness and affineness of the structural map, as well as connected
reductivity of the pullback for every `k : Type u`, every `Field k` instance
and every `Algebra R k` instance. For each geometric point used in the
Library's `IsReductive` predicate, `Spec.map_surjective` writes its actual
map as `Spec.map φ`. The locally supplied algebra structure is
`φ.hom.toAlgebra`, so its algebra map is exactly the map just obtained.
Unfolding the geometric fibre identifies the required pullback.
`IsConnectedReductive.isPseudoReductive` then supplies exactly the geometric
fibre clause of `IsReductive`; the smooth and affine clauses are the supplied
hypotheses.

For arbitrary commutative rings `R, A : Type u`, a ring homomorphism
`φ : R →+* A` and an element `r : R`,
`fieldReductive_baseChange_of_isUnit` assumes that `φ r` is a unit. Its other
hypothesis is connected reductivity at every field algebra over `R` in which
`r` has nonzero image. It concludes connected reductivity at every field
algebra over `A` for the actual group scheme pulled back along `Spec.map φ`.
There is no injectivity or domain assumption on `φ`, `R` or `A`.

The proof fixes an arbitrary `Algebra A k` and gives `k` the `R`-algebra
structure induced by `(algebraMap A k).comp φ`. The unit hypothesis maps to
a unit of the nontrivial field `k`, so the image of `r` is nonzero.
The supplied principal-open premise therefore applies to this particular
`R`-algebra structure. Contravariance of `Spec` identifies its map with
`Spec.algebraMap A k ≫ Spec.map φ`.
`baseChangeCompIso` identifies the direct pullback along this composite with
the iterated pullback. Connected reductivity transfers along the inverse of
that isomorphism by `IsConnectedReductive.of_iso`. This keeps the supplied
group scheme and both actual pullback maps throughout.

Finally, `exists_numberFieldSIntegers_fieldReductive` combines the arithmetic
unit construction with this comparison. Given the principal-open premise for
an actual group over the original S-integer ring and a nonzero `r`, it produces
a finite enlargement containing `S` and proves connected reductivity at every
field algebra over that enlarged ring, for the actual pullback along the
literal inclusion of integer rings.

## Provenance and limits

This is internal content derived from the published S-integer exhaustion,
the literal coefficient inclusions, the existing pullback-composition
isomorphism and connected-reductivity transport, and elementary field and
unit identities. It asserts no new literature theorem. All quantifiers and
constructions are uniform in the arbitrary universe `u`.
The initial principal-open good-fibre premise remains an explicit hypothesis.
No openness theorem, model existence, subgroup homomorphism, parabolicity or
connectedness of parabolic fibres is proved here. These remain obligations of
the simultaneous spreading target.
