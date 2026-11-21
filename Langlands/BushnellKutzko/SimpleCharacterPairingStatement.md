# The commutator pairing of a simple character (U6)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Theorem (3.4.1), printed p. 115 (PDF p. 127).

`SimpleCharacterPairingStatement` applies to every simple `[𝔄,n,0,β]` and defining sequence starting at `β`, over a nonarchimedean local field with the specified base additive character. Write `m=i+1` for `i≥0`; the bounds are `m≤n` and `m≤−k₀(β,𝔄)`, the latter vacuous for scalar `β`. It applies to every `θ∈C(𝔄,m−1,β)`.

The conclusion includes `H^m≤J^m` and normality of the pullback of `H^m` to `J^m`; neither is a premise. On the actual group quotient `Q=J^m/H^m`, the nested monoid homomorphism `B : Q →* (Q →* ℂˣ)` expresses bimultiplicativity. Its value on the classes of any `x,y∈J^m` equals `θ(x y x⁻¹ y⁻¹)`, with membership of that commutator in `H^m` included. It is alternating (`B(x,x)=1`) and the left radical is trivial. For an alternating bimultiplicative form the right radical is the same, by expanding `B(xy,xy)`. This is a proposition definition rather than a proof.
