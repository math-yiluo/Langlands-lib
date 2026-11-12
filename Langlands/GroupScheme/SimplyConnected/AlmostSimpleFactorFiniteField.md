# Finite fields fixing actual almost-simple factors

Author: Worker 166.

This internal construction assigns a finite intermediate field to every
factor of a supplied actual almost-simple product presentation over an
algebraic extension `L/k`. Every `k`-automorphism of `L` that fixes this
field pointwise fixes the actual factor index.

The group `G` over `k` is quasi-compact and quasi-separated, and is locally
of finite presentation over `k`. For the stabilizer assertion its base
change is smooth and affine, as required by the previously constructed
factor action. These properties hold in the intended semisimple
application. The extension need not have finite degree, and no perfectness
assumption is made.

Compose a factor projection with its inclusion to get an actual
idempotent endomorphism of `G_L`. Its range is exactly the factor range
on every test scheme: the inclusion is a section of the projection.
The published finite-stage homomorphism construction then supplies an
actual model of this endomorphism over a finite intermediate field.

The generic finite-model compatibility theorem in
`LatticeGaloisContinuity.descent_comm_of_model` shows that an automorphism
fixing that field commutes with the endomorphism through the canonical
ambient descent comparison. Taking ranges shows that canonical Galois
transport fixes its range. The exact range formula for the factor action
and uniqueness of factor ranges therefore make the factor index fixed.

`factorHomModel` retains the actual finite-stage homomorphism and its
recovery equation. `factorFieldOfDefinition` is its finite field, and
`galoisFactorIndex_eq_of_fixes` is the precise stabilizer assertion.
The field is a sufficient field of definition; this unit does not assert
its minimality, descend the factor itself, identify a stabilizer fixed
field, or prove a Weil-restriction decomposition. It also does not package
a topological continuity theorem.
