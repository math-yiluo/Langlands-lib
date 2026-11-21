# Haar scaling for the displacement map of a group automorphism

Let \(N\) be a closed normal subgroup of \(G\) and let \(\alpha\) be a
continuous automorphism preserving \(N\). The map `twistedConjugationMap`
is \(L_\alpha(g)=\alpha(g)^{-1}g\). The orientation is the one for
conjugating a Levi point by a unipotent element in the orbital integral
used to compare two Iwasawa normalizations.

`map_twistedConjugationMap_of_quotient` assumes that each point of \(G\)
lies in a compact open subgroup. The supplied measures \(\mu_G,\mu_N,\nu\)
satisfy the Weil formula for the left quotient \(N\backslash G\), with
\(\mu_G\) finite on compact sets and \(\mu_N\) a regular, s-finite,
right-invariant Haar measure. The supplied measurable map \(\tau\) on
the quotient descends \(L_\alpha\). Given
\((L_{\alpha|_N})_*\mu_N=c_N\mu_N\) and \(\tau_*\nu=c_Q\nu\), the theorem
gives \((L_\alpha)_*\mu_G=(c_Nc_Q)\mu_G\).

On the fibre represented by \(g\), the displacement of \(n g\) is
\(L_{\alpha|_N}(n)\) conjugated by \(\alpha(g)^{-1}\), followed on the
right by \(L_\alpha(g)\). A compact open subgroup containing
\(\alpha(g)^{-1}\) provides an invariant compact open intersection with
\(N\). Its positive finite mass gives conjugation scale one. The orbital
kernel supplies \(c_N\) on each fibre and integration over the quotient
supplies \(c_Q\).

The result is an internal measure argument for the compact normalization
in Waldspurger's IV.1(11) and Lemma V.3.1. It uses the Library's compatible
quotient kernel and Haar change of variables for group automorphisms.
