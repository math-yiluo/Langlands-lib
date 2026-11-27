# Descent of morphisms from smooth covers using dense opens

`exists_hom_of_agrees_over_dense_open` considers a smooth, surjective,
quasi-compact morphism `q` over a smooth scheme `X` over a reduced base. A
morphism from its source into a separated scheme descends if it agrees over a
dense open of `X` with a specified map on that open. The two pullbacks of the
morphism to the kernel pair agree over the dense preimage of the open. The
kernel pair is smooth over the reduced base, so equality on the dense open
implies equality everywhere. Faithfully flat descent then gives the morphism,
and the restriction is checked after the surjective base change of `q`.

`exists_iso_of_agrees_over_dense_open` applies this to two covers with a common
source. On the second kernel pair, take the intersection of the two dense opens
where the projections into the first scheme land in its chart. The chart map
into the second scheme is monic, so on that intersection the projections into
the first scheme agree. Reducedness and separatedness give equality on the
second kernel pair. Descent produces an inverse, as both composites can be
checked after their respective covers.

The argument uses the faithfully flat descent step of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §2.5 Proposition 5, printed p. 58 (PDF p. 65),
and applies it to the comparison of solution charts in §5.1 Proposition 3,
printed pp. 113–114 (PDF pp. 120–121). The literature ID is
`bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
