# Relative parabolic quotients with the normalizer inputs discharged

This internal construction reduces the five independent statement inputs of
`RelativeParabolicQuotientAssembly` to three. It uses the published relative
self-normalizer proof and derives the field self-normalizer statement from the
already required parabolic-dynamic input. It does not prove the three remaining
inputs or the unconditional relative quotient-existence target.

`fieldSelfNormalizer_of_parabolicDynamic` proves the exact all-test
`ParabolicSelfNormalizerStatement.{u}` from `ParabolicDynamicStatement.{u}`.
The published `parabolicSelfNormalizerStatement_of_rational_descent` requires
Borel conjugacy, Borel self-normalization, the parabolic-dynamic characterization,
and dynamic connectedness. This theorem supplies the published proofs
`borelConjugacy`, `borelNormalizer`, and `dynamicConnected` and retains only the
parabolic-dynamic premise. The imported reduction uses the opposite open cell
and faithfully flat descent from the algebraic closure. Its equality concerns
the entire subgroup functor on every test scheme.

`normalizer_eq_of_parabolicDynamic` applies the existing relative parabolic
normalizer adapter to the actual original inclusion `i : P ⟶ G` over `Spec R`.
It supplies `relativeSelfNormalizer`, the field self-normalizer theorem just
derived, and the same parabolic-dynamic input. The adapter derives geometric
connectedness of the reductive group and of the parabolic fibres, converts each
actual field-valued point into the target's algebra-valued field test, and
detects all-test self-normalization over the original ring. No additional
relative or field normalizer statement is assumed.

`properQuotientOfDynamicAndAmbient` returns an actual
`RelativeParabolicQuotient.ProperHomogeneousQuotient i`. It supplies these same
two normalizer proofs to `properQuotientOfStatements` while retaining the three
explicit inputs `ParabolicDynamicStatement`,
`SelfNormalizingProperAmbientStatement`, and
`RelativeParabolicQuotient.ProperAmbientCriterion`. The original assembly
constructs the quotient and its monomorphic map to a proper ambient scheme,
checks proper connected actual field pullbacks, and applies the explicit
generic properness input. All quotient properties belong to that same
constructed quotient.

`existenceStatement_of_dynamic_and_ambient` supplies the identical normalizer
proofs to the assembly's extraction theorem. It concludes exactly the unchanged
published `RelativeParabolicQuotient.ExistenceStatement.{u}` from the three
listed statement inputs. The properness criterion remains an explicit premise;
its separate proof task is not treated as a theorem here.

All rings, including zero and non-Noetherian rings, arbitrary universe `u`, all
field algebra structures, all actual subgroup maps, and all test schemes,
including nonreduced tests, are retained. The provenance is internal composition
of published proofs and explicitly conditional constructions. No original
literature assertion is added and no unconditional target proof is claimed.
