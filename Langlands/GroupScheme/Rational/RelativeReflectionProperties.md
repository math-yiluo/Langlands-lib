# Relative reflection properties

This is an internal, derived supporting proof for the relative Tits-system task. It imports the existing actual relative-reflection and relative-root-system constructions. It does not prove `RelativeRootSystemStatement` or `RelativeTitsSystemStatement`.

A relative reflection cannot be the identity: evaluating its action on its reflecting root and then applying its defining linear form would give `2 = -2` over the rational numbers. When `HasRelativeRootSystem i` holds, faithfulness of the actual quotient action also makes every relative reflection an involution.

The realization's exact root range supplies a root index for each actual relative root. The root-pairing reflection lies in the Weyl image, hence lifts to an element of the actual quotient `N(k)/Z(k)` and satisfies `IsRelativeReflection`. Every quotient element preserves the finite spanning root set because its action belongs to that Weyl image. Mathlib's `Module.Dual.eq_of_preReflection_mapsTo` then identifies any two defining linear forms for reflections in the same root. Faithfulness identifies the quotient elements. Thus every actual relative root has exactly one relative reflection under the root-system hypothesis.

The internal definition `relativeReflectionOfRootSystem hroot α` chooses this uniquely determined element of the actual quotient for an actual relative root `α`. Its specification is proved by `isRelativeReflection_relativeReflectionOfRootSystem`. This definition introduces no existence assumption beyond `hroot : HasRelativeRootSystem i`; its existence has just been derived from that predicate.

For simple roots with a common reflection, apply its reflection formula in the first root to the second root. Since the latter goes to its negative, twice its vector is a scalar multiple of the first. The published linear independence of the rationalized simple roots forces the roots to coincide. This argument needs splitness of the torus and genericity of the chamber cocharacter, retains arbitrary base-field characteristic, and uses no reducedness or positive-rank assumption.

The structural root-system predicate remains an explicit hypothesis throughout the existence, uniqueness, involution and simple-root separation results. These lemmas supply consequences of that predicate for later assembly; they supply no proof of the general root-system predicate or of the Bruhat multiplication and nondegeneracy axioms.
