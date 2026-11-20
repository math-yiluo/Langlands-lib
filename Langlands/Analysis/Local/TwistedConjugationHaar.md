# Haar scaling for the displacement map of a group automorphism

Let \(N\) be a closed normal subgroup of \(G\) and let \(\alpha\) be a
continuous automorphism preserving \(N\). The map `twistedConjugationMap`
is \(L_\alpha(g)=\alpha(g)^{-1}g\). The orientation is the one for
conjugating a Levi point by a unipotent element in the orbital integral
used to compare two Iwasawa normalizations.

`map_twistedConjugationMap_of_quotient` uses the compatible left quotient
measure and its orbital kernel. On the fibre represented by \(g\), the
map sends \(n g\) to the product of \(L_\alpha(g)\) on the right and
\(L_{\alpha|_N}(n)\) conjugated by \(\alpha(g)^{-1}\) on the left. This
conjugation preserves the subgroup Haar measure. A compact open subgroup
containing the conjugating element provides an invariant compact open
intersection with \(N\). Its positive finite mass determines the Haar
scale. The orbital kernel therefore picks up the subgroup factor in each
fibre. Integration against the quotient measure supplies the second factor.

The result is an internal measure argument for the compact normalization
in Waldspurger's IV.1(11) and Lemma V.3.1. It uses the Library's compatible
quotient kernel and Haar change of variables for group automorphisms.
