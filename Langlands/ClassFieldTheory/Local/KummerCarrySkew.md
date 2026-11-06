# Explicit skew symmetry of Kummer carry classes

Author: Worker 1691.

`KummerCarry.skewCochain` constructs the degree-one cochain
`r_chi(g) beta + r_psi(g) alpha + r_chi(g) r_psi(g) zeta`, where
`r_chi(g)` and `r_psi(g)` are the integer standard representatives of the two
characters into `Multiplicative (ZMod n)`. The coefficients are the actual
additive unit representation of an arbitrary field extension `L/K`. The
universes of the two fields are independent.

The accompanying theorem `KummerCarry.cyclicClass_add_eq_zero` assumes that
`n` is nonzero, that `n • alpha` and `n • beta` are the included base units
`a` and `b`, and that `n • zeta = 0`. It also assumes that the Galois action
fixes `zeta` and acts on `alpha` and `beta` with exponents given by the two
characters. Under these explicit hypotheses it proves
`cyclicClass K L chi b + cyclicClass K L psi a = 0`.
It does not require the characters to be injective, the extension to be
finite or Galois, or `zeta` to be primitive.

The proof expands the actual inhomogeneous coboundary of `skewCochain`.
The integer carry identities give the coefficients of `beta` and `alpha`.
The remaining coefficient of `zeta` is zero modulo `n`; the torsion hypothesis
therefore kills that term. The root-power hypotheses identify the two
remaining terms with the positive carry cocycles.

This is a derived supporting construction for norm separation, based on the
published `cyclicCarry`, `baseUnit`, and `cyclicClass` definitions. Its explicit
cochain proof implements the skew symmetry behind Serre, *Local Fields*,
XIV.2, Proposition 5 and Proposition 7(v), printed pages 207–209. The registered
source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The Lean theorem retains all root-action assumptions rather than constructing
Kummer characters or asserting norm duality. Local Kummer nondegeneracy and
unconditional norm separation remain separate obligations.
