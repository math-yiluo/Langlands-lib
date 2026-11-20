# Number-field transfer for cocycles on an affine Weil restriction

Let `B/A` be a finite extension of number fields and let `H` be an affine
coefficient group scheme over `Spec B` whose structural morphism is locally of
finite type. The results use the actual affine Weil restriction of `H` along
this extension.

`restrictPlace` restricts an archimedean place or a height-one prime along an
extension of number fields. `placeCompletionExtension` is the corresponding
map of completed fields. The two completion embeddings agree with the global
embedding on elements of the base field.

`locallyTrivial_transferCocycle` starts with a cocycle of the Weil restriction
whose pullback to every completion of `A` is trivial. It uses the commutative
square of schemes from the two global fields and the two completions. At each
place of `B`, it transports the local cochain to the successive pullback and
applies the group morphism provided by Weil evaluation.

For an original cover `Spec L` over `Spec A` with `L/A` finite,
`exists_finiteGalois_transfer` chooses a maximal residue field of `B ⊗[A] L`.
A finite Galois closure `E` of that residue field gives a field cover over `B`
and a refinement map to the pulled-back cover through the chosen component.
The transferred cocycle remains locally trivial. Global triviality on
`Spec E` descends to the pulled-back cover using the fpqc map `Spec E → Spec B`.
The affine Weil comparison then reflects triviality of the original cocycle.
This is an internal reduction for the number-field Hasse kernel.
