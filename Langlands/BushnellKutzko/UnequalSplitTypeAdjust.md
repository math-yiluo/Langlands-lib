# Normalization of the twisting character

`TwistNormalizationStatement` concerns a simple stratum \([\mathfrak A,n,0,\beta]\)
with a chosen defining sequence. For \(m=i+1<n\) below the simple critical depth,
let \(\theta\) be a simple character at index \(i\) and let \(\psi_F\) be a
Bushnell–Kutzko additive character. If \(c,c'\in\mathfrak P^{-m}\) have the
same image under a tame corestriction for \(F[\beta]/F\), a unit normalizing
\(H^m\) conjugates the character \(\theta\psi_c\) to \(\theta\psi_{c'}\). The
conjugation convention in `exists_conj_twist_character` evaluates the old
character at \(ghg^{-1}\) and the new character at \(h\).

For nonscalar \(\beta\), `exists_mem_centralizer_mul_adjoint_of_corestriction_eq_zero`
uses adjoint exactness to express \(c'-c\) as \(\beta u-u\beta\) with
\(u\in\mathfrak Q^{r-m}\mathfrak N_{-r}\), where \(r=-k_0(\beta,\mathfrak A)\).
`exists_conj_twist_character_of_adjoint` makes \(1+u\) a unit and applies simple
character covariance. The difference between the two twisting parameters
after covariance and conjugation lies in \(\mathfrak P^{1-m}\). Pairing it
with \(h-1\in\mathfrak P^m\) gives a trivial trace character. For scalar
\(\beta\), the adjoint map is zero and its image is the kernel of the
surjective corestriction. Injectivity gives \(c=c'\) and the conjugating unit
is the identity.

The normalization follows the use of adjoint exactness and simple character
covariance in Bushnell and Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), (1.4.10), (3.3.9) and (8.2.8), printed pp. 38, 108
and 278. For a split corestricted twisting element, taking the block diagonal
gives the new parameter to which (8.2.8) applies.
