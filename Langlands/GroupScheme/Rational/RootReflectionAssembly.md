# Root-system assembly from integral normalizer reflections

This is a derived construction on the existing relative roots, character and
cocharacter lattices, normalizer points, relative Weyl quotient, and rational
root span. It imports the unchanged `Rational.Statement` through
`Rational.RootFiniteness`. It supplies a conditional assembly step toward
`RelativeRootSystemStatement`; existence of the structural reflection data
is a separate obligation.

The setting is an arbitrary universe `u`, a field `k : Type u`, a commutative
group scheme `T`, an affine group scheme `G`, and a homomorphism
`i : T.toGrp ⟶ G`. The normalizer action and assembly results use the existing
monomorphism hypothesis on `i`. Splitness below is a hypothesis on `T`.

`RelativeRootSystem.rootVector` sends an actual relative root `α` to
`1 ⊗ α` in the existing submodule `relativeRootSpan i`.
`span_range_rootVector` proves that these vectors span that submodule by
unfolding its definition as a rational span. For a split torus,
`rootEmbedding` is the resulting embedding: injectivity uses the published
injectivity of rationalization on the actual character lattice.

`RelativeRootSystem.corootFunctional` extends the integer lattice pairing
with an actual cocharacter to a rational linear functional on
`relativeRootSpan i`. The construction uses base change to `ℚ`, the tensor
unit equivalence, and restriction to the submodule. The theorem
`corootFunctional_rootVector` identifies its value on `1 ⊗ α` with the
integer `latticePairing T α ν`, viewed in `ℚ`.

`RelativeRootReflectionData i` records, for every actual relative root `α`,
an actual cocharacter `ν_α` and an actual rational normalizer point `n_α`.
Its two laws are

* `latticePairing T α ν_α = 2`;
* for every character `χ` of `T`,
  `weylAction i n_α χ = χ - latticePairing T χ ν_α • α`.

These laws are explicit input data. The structure does not assert their
existence for a reductive group, and it does not assert generation or
faithfulness.

For such data `D`, `reflection_rootVector` rationalizes the second law.
The published stability of actual relative roots under normalizer action
then gives `mapsTo_preReflection`: each resulting linear reflection
preserves the actual root-vector set.

Assuming splitness of `T` and finiteness of `relativeRoots i`,
`corootFunctional_injective` proves that the restricted functionals
associated with distinct roots are distinct. If two functionals agreed,
each would take value two on both roots. Mathlib's
`Module.eq_of_mapsTo_reflection_of_mem` would force the roots to be equal:
otherwise iterating the two reflections produces an infinite orbit in a
finite set. The rational vector space is additively torsion free, as needed
by that lemma. Thus injectivity of the coroot functionals is proved rather
than imposed as another input law.

`D.rootPairing` constructs
`RootPairing (relativeRoots i) ℚ (relativeRootSpan i)
(Module.Dual ℚ (relativeRootSpan i))`.
Finiteness gives finite dimension of the actual root span, so its evaluation
pairing with its dual is perfect. Mathlib's `RootPairing.mk''` constructs
the pairing from the root and coroot embeddings, their self-pairing of two,
reflection stability of roots, and the spanning theorem. This constructor
also derives the required covariance of coroots. The pairings are integer
valued by `corootFunctional_rootVector`; Mathlib's
`RootPairing.isRootSystem_mk''` then supplies spanning of the coroots.

The accompanying theorems prove that this is a crystallographic root system,
that its bilinear map is exactly `Module.Dual.eval`, and that the images of
its roots in the ambient rational character space are exactly
`toRat '' relativeRoots i`. No reducedness or nonemptiness hypothesis occurs.

`reflection_eq_relativeWeylAction` identifies each constructed reflection
with the existing action of the quotient class of `n_α`. It checks equality
on the spanning actual root vectors using the published formula for
`relativeWeylAction` on `1 ⊗ α`. Consequently `weylGroup_image` identifies the
image of the constructed root-system Weyl group with the subgroup generated
by these actual normalizer actions.

Finally, `D.hasRelativeRootSystem` proves every clause of the published
`HasRelativeRootSystem i` under two further explicit hypotheses:
the classes of the chosen representatives generate the actual quotient
`relativeWeylGroup i`, and its action on the actual root span is injective.
Mapping the generation equality through the action identifies the generated
reflection subgroup with the entire action range; injectivity is retained
from the second hypothesis. The finite index type is the actual root subtype
itself, in `Type u`.

The provenance is internal: these results are consequences of the explicit
input laws, the published lattice and normalizer constructions, and the
Mathlib constructors and finite-reflection lemma named above. The module
does not prove existence of integral reflection data, generation of the
actual relative Weyl quotient, or faithfulness for arbitrary connected
reductive groups. It therefore does not prove the unrestricted
`RelativeRootSystemStatement`.
