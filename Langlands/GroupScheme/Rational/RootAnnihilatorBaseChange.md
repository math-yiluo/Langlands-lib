# Real scalar extension of integral character annihilators

Author: Worker 1322.

This derived unit uses the existing integer character/cocharacter pairing of an
actual commutative group scheme over an arbitrary field. The submodule
`RealTorusSpace.rootAnnihilatorInt T J` consists of integral cocharacters whose
pairing with every character in `J` vanishes.

For finite `J`, `rootAnnihilatorInt_baseChange` identifies the image of its
inclusion after extension of scalars to the reals with the published
`rootAnnihilator T J`. The equivalence `rootAnnihilatorBaseChange J` identifies
the real tensor product of the integral annihilator with this real annihilator.
Its compatibility laws state that the underlying map is the scalar extension
of the integral inclusion, and that a pure tensor maps to the same pure tensor
in the ambient real cocharacter space.

The implemented proof forms the integer simultaneous evaluation map to `J → ℤ`.
After extension of scalars, the finite-product tensor equivalence identifies
this map with simultaneous real evaluation. Its kernel is therefore the
published real annihilator. The reals are flat over the integers because they
are torsion free over a Dedekind domain, so Mathlib's tensor-kernel equivalence
identifies this kernel with the tensor product of the integral kernel.

The provenance is internal linear algebra; no external source is used. The
result requires neither splitness nor independence of the selected characters.
It retains the empty selection. It does not construct a subgroup scheme or
prove the standard-Levi structural conclusions.
