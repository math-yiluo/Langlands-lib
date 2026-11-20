# The split cycle in product coordinates

The homeomorphism `splitCycleChart` keeps the first coordinate of \(x\) and
records \(x_i^{-1}d_i x_{i+1}\) at each nonfinal index. It splits off the first
entry, applies the chart to the tail, and replaces the tail's first coordinate
by its left translate. This construction proves measure preservation by
induction using finite product measures and left invariance.

The coordinate calculation for powers of the shift identifies coordinate zero
of the cyclic norm with the ordered product \(d_0\cdots d_l\).
The element \((\gamma,1,\ldots,1)\) has norm \((\gamma,\ldots,\gamma)\). For
coordinate zero this follows from the ordered product. The norm identity for
the shift propagates it around the cycle since each coordinate commutes with
\(\gamma\).

The chart implements the change of variables in Arthur–Clozel (1989),
Chapter 1, §5, using the nonfinal twisted entries as the integration
variables. The norm calculation uses the split cyclic algebra of
Henniart–Lemaire (2011), II.2.15.

The ordered product lemmas split off the final entry without commuting any
factors. Both the quotient chart and the convolution computation use these
identities.
