# Geometric connectedness of geometrically integral morphisms

For arbitrary schemes `X Y : Scheme.{u}` and a geometrically integral
morphism `f : X ⟶ Y`, the published lemma
`Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral`
proves that `f` is geometrically connected. After every field base change,
geometric irreducibility supplies an irreducible space, hence a connected
space.

The declaration and proof are moved unchanged from
[TranslationInvarianceOfSmoothFamily](Picard/TranslationInvarianceOfSmoothFamily.md).
Its existing namespace is retained for consumers. This shared module imports
only the geometric integrality and connectedness definitions and supports both
the smooth-family translation argument and the proper flat integral rigidified
Picard comparison. No translation-invariance or Picard-representability result
is used by this lemma.
