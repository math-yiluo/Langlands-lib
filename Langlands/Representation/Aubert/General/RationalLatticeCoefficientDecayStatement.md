# Actual rational lattice coefficients from a simultaneous standard basis

Author: Worker 19. This is an internal derived statement toward the general
rational strict Jacquet square-integrability criterion.

`RationalLatticeCoefficientDecayStatement.{u,v,w}` retains arbitrary connected
reductive groups over arbitrary nonarchimedean local fields, the canonical
rational-point topology, independent field and representation universes, and
the actual maximal split torus, generic cocharacter and literal simple-root
labels. It assumes admissibility and the target's literal strict normalized
Jacquet exponent premise. No central-character hypothesis is needed for this
coefficient estimate.

The displayed structural input `hStandard : StandardCocharacterStatement.{u}`
is a supplied global proposition: it gives standard-cocharacter existence and
the all-test dynamic subgroup identifications for all groups in its scope.
The statement also retains closedness of every actual unipotent subgroup
through `hU`, together with the displayed local compactness and
nonarchimedean-group instances on the actual rational-point group. These are
already premises of the host criterion. Naming a published statement does not
supply its proof.

The geometric input is `SimultaneousStandardBasisAt i ν K0`. The conclusion
chooses one of its compact-open normal subgroup bases `B` before any finite
lattice is specified. For a finite index type `I`, a ray `x a` is orthogonal
to the selected finite face `J a` and strictly positive on every simple root
outside that face. At least one simple root lies outside each face, so every
ray is noncentral. The statement chooses full-center points `z a` of the
actual Levis, equal in the ambient group to the uniformizer powers of `x a`.

For every `K` in that same basis, every `K`-fixed vector and every algebraic
dual functional fixed by the contragredient action, the actual coefficients
on the nonnegative lattice `uniformizerPowers i (sum a, n a • x a)` have a
product exponential bound with a positive constant. Each radius is positive,
and its square times the reciprocal of the actual conjugation Haar modulus
on the corresponding actual unipotent subgroup is strictly below one. The
center points are chosen before `K`, the vector and the functional; the radii
and constant may depend on those data. Empty `I` is allowed. If there are no
simple roots, the noncentral-ray premise forces `I` to be empty and the
coefficient estimate is a constant bound at the identity.

The derivation uses integral factorization of orthogonal cocharacters through
the compatible split components supplied by the basis, actual character
values on the common uniformizer section, and the basis's literal Iwahori
factorizations and contraction clauses. These realize every geometric
hypothesis of `HaarNormalizedLatticeCoefficientBoundStatement`. The strict
spectral input comes from `RationalLatticeStrictExponentStatement`, applied
to the very same actual full-center points. Both intermediate statements
still require their independent proofs for this derivation to be a proof.

This statement supplies no existence theorem for the simultaneous basis,
no Haar volume estimate, no finite chamber cover and no integrability result.
Those remain obligations of the full criterion. Its intended argument uses
no classification, geometric lemma, adjointness, character independence or
cuspidal support theorem.
