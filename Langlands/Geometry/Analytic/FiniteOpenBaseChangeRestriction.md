# Restriction and pasting of complete finite-open models

This internal adapter compares the direct finite-open local models on
full source domains with the actual closed-quotient base changes of
the original local algebras.

`baseChangeEquiv` specializes the constructed bounded pushout-pasting
equivalence. It maps the entire iterated base change to the direct
model and preserves both the original domain coefficient map and the
composite original first-source leg. The inverse has the exact reverse
formulas on those entire bounded maps.

`restrictionMap` constructs the actual bounded map between direct
models associated to a further full-domain arrow. Uniqueness of
original domain restrictions gives the entire coefficient equation
needed by the original pushout lift. Its two leg formulas prove
identity and composition on all algebra elements.

`transitionMap_naturality` proves that each complete overlap transition
commutes with every such further domain restriction. The first-leg
proof applies the full coefficient-test chart-change law after that
bounded restriction; complete chart-change uniqueness identifies the
result with the direct chart change. The unchanged right-leg formula
and pushout uniqueness give equality of the entire transition
composites.

The hypotheses are exactly those of the actual finite-open local
models, with independent field, ambient-space and original index
universes. No descended parent, spectral faithfulness, global finite
preimage or etale conclusion is assumed. This is internally derived
from actual full-domain and bounded pushout constructions, with no
external theorem transcription.
