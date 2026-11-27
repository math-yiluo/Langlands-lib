# Trace-character evaluation of filtered unit commutators

These expansions implement the trace-character part of Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (3.2.6) and (3.2.9), printed pp. 100 and 102 (PDF pp. 112 and 114). The registered source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

For units `1+x` and `1+y` at natural steps `k` and `l` of a lattice chain over a valued field, `commutatorElement_sub_one` expresses their commutator minus one as `(xy−yx)` followed by the two inverse factors. This puts the commutator in the unit filtration at step `k+l`.

For the character identities, the field is nonarchimedean local and the base additive character is trivial on `𝔭_F` and nontrivial on `𝒪_F`. Both inverse factors differ from one in their corresponding filtration steps, so replacing both by one introduces an error in step `k+l+min(k,l)`. For a parameter in `𝔓^(−r)` with `r < k+l+min(k,l)`, the product of the parameter and the error belongs to `𝔓¹`. Its trace lies in `𝔭_F`, where the base additive character is trivial. Cyclic invariance of trace identifies the surviving character with the adjoint product.

When the first unit centralizes the parameter, `elementCharacter_commutator_of_depth` applies under the bound `r < k+2l`. It gives the trace twist by the conjugation difference of the parameter under the first unit. That difference is zero, so the evaluated commutator is one.
