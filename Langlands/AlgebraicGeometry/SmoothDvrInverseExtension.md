# Open immersions from extension of a rational inverse

`isOpenImmersion_of_inverse_at_stalk_primes` considers a morphism `τ` between
smooth separated DVR schemes. It assumes a partial inverse with a common
dense chart and specifies that the inverse takes the right values at the
images of the zero and principal prime points of every source stalk. Given
`x`, choose an affine open in the source containing `x`. The prescribed
inverse values at the test points are generizations of `x`, hence they
belong to that affine open. `rationalMap_mem_domain_of_affineTrace` extends
the inverse at `τ x`.

Consequently `τ` factors through the maximal domain of the inverse. Both
composites with that inverse are identities on the common dense chart.
Reducedness and separatedness extend both identities, so `τ` identifies
its source with that open of the target.

This gives the open-immersion step used in the last assertion of Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1 Theorem 5, printed
p. 114 (PDF p. 121). The proof uses the factorial affine extension
argument derived from §4.4 Lemma 2, printed p. 109 (PDF p. 116). The
literature ID is `bosch-lutkebohmert-raynaud-1990-neron-models`, and the
retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
