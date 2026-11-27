# Extending a solution when the generic law is total

`Langlands.AlgebraicGeometry.birationalGroupLawGenericGroupSolution` proves
`Langlands.AlgebraicGeometry.BirationalGroupLawGenericGroupSolutionStatement`.
Given a solution of a birational group law over a discrete valuation ring and
the stated coverage of the generic relative square by the domain and both
translations, it constructs a solution with domain `⊤`.

Restrict to the generic open of the base. The partial law becomes total and
both translations become isomorphisms. `Solution.exists_iso_over_open`
compares the two smooth covers obtained by right division on the common
chart product. It gives a generic-fibre isomorphism from `X` to the solution
group agreeing with the original chart embedding. This isomorphism and its
inverse agree on the respective overlaps with the two partial morphisms
from the common chart, so their maximal rational-map domains contain the
entire generic fibres.

The forward rational map has fibre-dense domain. `weilExtensionOverDvr`
extends it to a morphism `τ` on all of `X` using the group-valued difference
near the diagonal and faithfully flat descent. To identify `τ` as an open
immersion, the inverse is tested at the images of the zero and principal
prime points of every stalk of `X`. Those points belong to the original
chart or the generic fibre, so the inverse there has the prescribed value.
`isOpenImmersion_of_inverse_at_stalk_primes` extends the rational inverse
locally around the image and identifies `τ` with the inclusion of its
maximal domain. `Solution.exists_full_of_extension` then proves multiplication
compatibility on the whole law domain by density and produces the desired
solution.

The target is the last assertion of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (1990), §5.1 Theorem 5, printed p. 114 (PDF p. 121), conditional
on the existence of a solution as in the source proof. The generic comparison
uses the descent argument of §5.1 Proposition 3 and Lemma 4, printed pp. 113–114
(PDF pp. 120–121). The extension uses §4.4 Theorem 1 and Lemma 2, printed
pp. 109–110 (PDF pp. 116–117), and §2.5 Proposition 5, printed p. 58 (PDF p. 65).
The affine extension argument also supplies the local inverse in the
open-immersion step. The literature ID is
`bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
