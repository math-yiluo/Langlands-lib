# Compact-open topology on actual half-twisted adelic sections

Author: Worker 2. Provenance: internal construction from the actual
half-twisted adelic smooth sections and their proved faithful continuous
function realization. This unit makes no new original-literature identification.

The number field `F : Type uF`, rank and ordered positive block shape are
unchanged. Coefficients are arbitrary complex normed spaces, with independent
universes for source, intermediate and target spaces. Completeness,
finite dimension and continuity of the supplied Levi representation are
not required.

`CompactOpenSections` is a dedicated copy of the already constructed
`SmoothSections`. It retains the exact covariant functions, their real-smooth
archimedean slices, and a common open finite stabilizer. `toSmooth` is the
identity on those functions as a complex linear equivalence.
`toContinuousMap` is the existing injective linear realization composed with
this equivalence.

The chosen topology is induced by this injection into actual continuous
vector valued functions on the full adelic matrix group, with Mathlib's
compact-open topology. The injection is a topological embedding. The induced
space is a Hausdorff topological additive group with continuous real and
complex scalar multiplication and a locally convex real topology. These
facts follow by pulling back the corresponding structures along the
injective linear map. `toContinuousMapCLM` bundles this map continuously,
and `evalCLM` gives continuous complex linear point evaluation.

`rightAction` is the existing full adelic right translation on the same
sections: its actual continuous-function value is `f(x * g)`. For each
fixed `g`, compact-open precomposition by the continuous map `x ↦ x * g`
proves continuity. `rightTranslation` bundles the continuous linear
operator. Translation by `g⁻¹` is its inverse, giving
`rightTranslationHomeomorph`; the inverse identities use the actual
representation laws. `tendsto_iff_uniformOn_compact` characterizes convergence
as uniform convergence on every compact subset of the actual full group.

A Levi intertwiner `T` with proved continuity induces actual coefficient
postcomposition through the existing `smoothInducedMap`. The same finite
stabilizer and archimedean slice smoothness are preserved by that
construction. Compact-open postcomposition by `T` proves continuity of
the new `map` and its bundled `mapCLM`. Evaluation, identity, composition
and right-translation intertwining agree with the existing actual section
maps, with the identity and composition laws proved using their established
counterparts.

This topology controls only function values on compact sets. It is not a
topology on all derivatives. This unit proves continuity for fixed right
translations and continuous coefficient maps; it makes no joint action
continuity, completeness, smooth orbit-map, unitary completion, Haar
identification, nonzero section or automorphic existence assertion.
