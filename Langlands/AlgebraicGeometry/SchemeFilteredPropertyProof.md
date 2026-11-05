# Eventual properties of prescribed original-ring models

The exact theorem is
`Langlands.AlgebraicGeometry.SchemeLimitModel.initialRingModelSmoothFlatDescent :
InitialRingModelSmoothFlatDescent.{u}` for arbitrary universe `u`, in the
unchanged `SchemeFilteredPropertyStatement` pair. Worker 105 authored the
reused Lean proof and original explanation; Worker 1572 checked the proof
against the published target and dependencies and prepared this focused
submission.

The target specializes the structural smoothness and flatness cases of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Theorem 3.4(2), printed pp. 5–6. The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arbitrary small filtered-category formulation is an internal
generalization justified by the actual under-category construction and
the published model and isomorphism descent proofs. The theorem retains
nonaffine and nonseparated models, possibly noninjective ring transitions,
and the supplied colimit cocone and witness. A private helper works with a
base-change-stable scheme-morphism property and its proved structural
model-existence theorem.

The original ring diagram is first restricted to the actual under-category
of the chosen initial stage. Finality preserves its given colimit cocone.
Structural model existence produces a finitely presented model with the
property at one of these original stages. The prescribed model is also
pulled back to that stage. The two actual pullback squares over the given
colimit identify their further pullbacks by an actual isomorphism over
the colimit spectrum.

The third conjunct of `initialRingModelMorphismDescent` descends this
isomorphism to an actual later original stage. Base change and invariance
under isomorphisms transfer the property from the property-bearing model
to the prescribed one there. Pasting the two prescribed-model pullback
squares identifies this double pullback with the canonical pullback along
the composed original ring transition. The reverse direction follows
from the actual cocone equation and base-change stability, by pullback
cancellation.

The two concrete theorems supply the proved smooth and flat structural
model-existence results. The final theorem conjoins them. No geometric
property remains an assumed hypothesis of either concrete conclusion.
This is structural descent; the arbitrary relative-morphism version
requires an additional finite affine target cover argument.
