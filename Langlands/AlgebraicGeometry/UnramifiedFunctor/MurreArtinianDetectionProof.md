# Artinian detection of a representing scheme

`murreArtinianDetection` proves `MurreArtinianDetectionStatement` at arbitrary
universes for schemes and presheaf values. It is the bijective, represented-source
case of Murre's Lemma 1. The source is J. P. Murre, *Representation of
unramified functors. Applications*, Séminaire Bourbaki exp. 294 (1964–65),
printed pp. 247–248, PDF pp. 6–7, registered as
`murre-1965-bourbaki-294-unramified-functors`.

For a complete noetherian local test ring, bijectivity on its positive maximal
ideal thickenings gives uniqueness there and makes the lifts of a section
compatible. `ChartGluing.exists_specMap_adic_lift` assembles the compatible maps
into a scheme morphism. `ChartGluing.specMap_adic_ext` checks that it lies over
the base and gives uniqueness of the lift. The injectivity part of (F3) checks
that the assembled morphism induces the original section. The quotient for
exponent zero also sees equal sections, by restriction from the first positive
thickening.

Let \(B\) be a finite-type algebra over the noetherian base ring, and let
\(\mathfrak m\) be a maximal ideal of \(B\). Each positive thickening of
\(\widehat{B_{\mathfrak m}}\) is local Artinian. The localized-completion
approximation lemma gives a surjection from \(B\) onto each thickening.
Consequently each is of finite type over the base, and its singleton prime
spectrum gives quasi-finiteness. The proof uses this quotient presentation
to compare the induced base map with the one used in the Artinian hypothesis.
The completion map to the spectrum of the stalk at \(\mathfrak m\) is flat,
surjective, and quasi-compact.

For injectivity, equality on a completed stalk implies equality on the stalk
by cancellation along the completion map. The equality spreads to an open
neighbourhood of the maximal point. Every prime of \(B\) lies under a maximal
ideal and belongs to any open containing that maximal point. These opens
therefore cover \(\operatorname{Spec} B\). The filtered affine reduction extends
injectivity to every affine test scheme, and agreement on affine covers gives
injectivity for every test scheme.

For surjectivity, lift the section on each completed maximal stalk. The
injectivity already proved ensures compatibility for faithfully flat descent.
Condition (F1b) detects the section equality after the lift descends. The
stalk factorizations spread to neighbourhoods by finite type and (F2), and
(F1a) glues them to a lift on \(\operatorname{Spec} B\). The affine limit
argument and another application of Zariski gluing extend surjectivity to
arbitrary test schemes. The spreading and affine limit proofs are in the
[paired helper](MurreArtinianDetectionLimits.md).
