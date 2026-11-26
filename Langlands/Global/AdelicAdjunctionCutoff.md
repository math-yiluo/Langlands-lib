# Integration in the positive split-component variable

The adjunction argument in Mœglin–Waldspurger II.1.8 compares pairing integrals on a common quotient. The cutoff weights in the two integrals have equal Haar integrals along the positive split component. The proof uses this equality even when the cutoff functions change sign. Compact support controls the absolute integral and Fubini integrates the signed weight separately.

`integrate_cutoffWeightedKernel` uses the actual Haar decomposition of the full rational Levi quotient into the positive split torus and the norm-one rational quotient. The norm-one quotient maps to the canonical quotient with its specified measure. The positive torus coordinates carry Haar to a fixed scalar multiple of Lebesgue measure. The proof retains that scalar and the scalar relating the supplied Levi Haar to the reference Haar. They are independent of the cutoff and its measurable shift.
