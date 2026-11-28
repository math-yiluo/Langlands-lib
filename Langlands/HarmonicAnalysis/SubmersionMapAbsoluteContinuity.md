# Absolute continuity on an open submersion locus

`SubmersionMapAbsoluteContinuityStatement` concerns finite-dimensional normed
spaces `X` and `Y` over a proper nontrivially normed field `F`, with an
ultrametric norm on `X` and additive Haar measures `μ` and `ν`. If a continuous
map `Φ : X → Y` has a surjective strict derivative at every point of an open
set `U`, then the pushforward of `μ` restricted to `U` is absolutely continuous
with respect to `ν`. The field and the two spaces have independent universes.

The proof `submersionMapAbsoluteContinuity` puts a compact open ball `V` around
each point of `U`, with `V ⊆ U`. The indicator of `V` is locally constant and
weights `μ` to `μ.restrict V`. Apply `compactSubmersionPushforward` to this
indicator and to the family `(p, x) ↦ Φ(x)` with a constant parameter over `F`.
The derivative in the `X` direction is the supplied surjective derivative.
At parameter zero the compact pushforward theorem gives a density with respect
to `ν`. The source space is proper and second countable, so a countable
collection of the balls covers `U`. For every measurable `ν`-null set, its
preimage in `U` lies in a countable union of preimages in the selected balls.
Each of those intersections is `μ`-null, which gives the claimed absolute
continuity.

This is a consequence of the compact test-function pushforward principle in
Harish-Chandra, *A submersion principle and its applications*, Proc. Indian
Acad. Sci. (Math. Sci.) 90 (1981), §§2–3, pp. 96–98. In the setting of
Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*,
ULS 16 (1999), §1.4, Lemma 1.13, this supplies the absolute-continuity step in
a proof of local summability by pushing forward Haar measure on the open locus
where the conjugation map is a submersion.
