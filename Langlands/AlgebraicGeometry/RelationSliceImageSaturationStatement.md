# Saturation of the image of a scheme slice

Let `U` and `R` be arbitrary schemes in any universe `u`, with an equivalence
relation specified by `AtlasRelation.IsEquivRel t s` for maps `t s : R ⟶ U`.
For any scheme `V` in the same universe and any morphism `g : V ⟶ U`, set
`h = pullback.snd g t ≫ s`. The statement says that the image of `g` is
contained in the image of `h`, and that for each underlying point `r` of `R`,
`t r` belongs to the image of `h` if and only if `s r` does.

No smoothness, finiteness, or etaleness assumption is made. The relation is
the published absolute scheme relation, unchanged. The assertion concerns
images of underlying point maps; it does not identify them with the images
on rational points over a fixed field.

This is an internal interface used to move slice coverage within an orbit
in the direct proof of the etale slicing theorem. Reflexivity gives the
first image inclusion. Transitivity gives forward invariance by composing
arrows after passing to the scheme pullback of `h` and `t`; Mathlib's point
existence theorem for scheme pullbacks handles the residue-field extensions
needed to lift a compatible pair of underlying points. Symmetry gives the
reverse implication. These operations on the published relation and standard
scheme pullbacks supply the provenance; no external literature theorem or
unproved quotient statement is assumed.
