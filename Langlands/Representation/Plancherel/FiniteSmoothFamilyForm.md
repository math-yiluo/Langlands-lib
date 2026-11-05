# Positive integral forms on finite algebraic smooth families

This is a derived prerequisite for Waldspurger's smooth coefficient families,
not the completed spectral Hermitian form. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)* (2003), VI.1, printed
pp.295–296 / PDF pp.61–62, identifies smooth orbit families with the diagonal
invariants in the algebraic tensor of scalar smooth functions and the fixed
compact coefficient module. VI.3, printed pp.301–302 / PDF pp.67–68, introduces
the finite invariant pieces, their topology and the locally measure-preserving
orbit measure. The present construction supplies the generic positive integral
pairing on the already published algebraic finite-family model.

The parameter set is a finite product `J → Circle`, with arbitrary finite index
universe. The coefficient module `V` has only an additive commutative group,
a complex module structure and a supplied positive Hermitian core `b`. It has
no assumed norm, topology, completeness or finite dimension. The scalar
smoothness convention is the existing real-angle lift through `finiteTorusExp`.
The measure `μ` is the explicitly supplied Borel measure on the parameter torus.
It is finite; positive definiteness further requires that every nonempty open
subset have positive measure.

`isSmoothFiniteTorusFunction_core_pairing` proves that the scalar function
`z ↦ b.inner (F z) (H z)` is smooth for two members of
`finiteSmoothFamilies J V`. The proof uses the published range identification
with `smoothTensorEvaluation` and induction in each algebraic tensor argument.
On elementary tensors the function is
`conj(f(z)) * g(z) * b.inner v w`, which is smooth by real smoothness of complex
conjugation and multiplication. Additivity extends this to arbitrary finite
algebraic sums. Smoothness and compactness give continuity and boundedness, and
`integrable_finiteSmoothFamily_core_pairing` proves actual Bochner
integrability against the given finite measure.

`finiteSmoothFamilyCore` is the positive Hermitian core whose inner product is
the actual complex integral

`integral z, b.inner (F z) (H z) dμ`.

Its Hermitian symmetry, additivity and conjugate scalar linearity follow from
the corresponding integral laws. Nonnegativity uses the integral of the real
self-pairing. If a family's self-pairing has zero integral, nonnegativity gives
zero almost everywhere; continuity and positivity of the measure on open sets
give zero everywhere. Positive definiteness of the original coefficient core
then gives zero at every parameter, hence the zero family. No pointwise
continuity of the coefficient vectors is used.

`finiteSmoothFamilyMap` applies a fixed complex linear map to coefficient
vectors. It preserves the existing finite algebraic smoothness condition by
the published `mem_finiteSmoothFamilies_linearMap`.
`finiteSmoothFamilyCore_map` proves preservation of the entire integrated
pairing whenever the coefficient map preserves the supplied coefficient forms.
The two coefficient carriers may lie in independent universes.

`finiteSmoothTensorCore` pulls the same core back through the published
`smoothTensorFamilyEquiv`. Its integral formula holds for every algebraic
tensor. `finiteSmoothTensorCore_inner_tmul` computes an elementary pairing as
the integral of `conj(f) * g` multiplied by `b.inner v w`.
`finiteSmoothEquivariantFamilyCore` restricts the same form to the existing
`finiteSmoothEquivariantFamilies` for any supplied group, torus-translation
homomorphism and coefficient representation. It retains the full covariance
law; it requires neither a trivial coefficient action nor finiteness of that
group.

The construction uses the published generic `coreComap` for the two faithful
pullbacks and the existing finite-family transport API. It does not select an
orbit measure or identify a probability measure with Waldspurger's source
normalization. Actual compact coefficient forms, their invariance under
unitary twists, orbit descent, the density weight, the global finite-support
spectral space and the Plancherel isometry remain separate consumers and proof
obligations. This result asserts no group-action invariance of the integral
core for an arbitrary supplied coefficient action or measure.
