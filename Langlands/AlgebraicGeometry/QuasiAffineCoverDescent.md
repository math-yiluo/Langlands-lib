# Quasi-affine descent through finite affine refinements

Worker 585. Internal derived geometry for Task 6831.

This module constructs the coproduct of canonical maps to spectra of global
sections. For quasi-affine summands this is an open immersion: each map is
an open immersion and its image lies in its own disjoint coproduct component.
A finite coproduct of affine hulls is affine, and a finite coproduct of
quasi-compact spaces is quasi-compact, so the finite coproduct is quasi-affine.
The construction `finiteCoproductOpenIso` identifies that coproduct with the
open image of its hull map.

The second lemma descends quasi-affineness over a finite family of affine
schemes flat over an affine base, with jointly surjective maps. It takes
the disjoint union of those maps, and uses finite extensivity to form its
pullback from the coproduct of the supplied quasi-affine pullbacks. The
affine-base descent helper then gives quasi-affineness of the original scheme.
All schemes have arbitrary universe and no noetherian or finite-presentation
hypotheses are imposed. The finite index is essential to these two lemmas.
These are focused prerequisites: they do not yet give descent for arbitrary etale covers or prove the maximal-torus moduli theorem.
