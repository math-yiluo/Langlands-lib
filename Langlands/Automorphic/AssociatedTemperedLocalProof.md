# Local assembly of tempered associated factor equalities

This internal definition and lemma unit assembles the local algebraic step in Henniart's
Corollaire 2.3, as published in
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedTemperedFactorStatement`.
It does not yet prove that global target. Its local theorem explicitly requires
an actual local-constant system, common gamma factors for all systems, and
certified automorphic pole regions.

The entry construction
`Langlands.ClassField.Global.RelativeWeilGroup.localComponentDualEquiv`
is the identity on the algebraic dual of the original carrier. Its intertwining
law is the inverse-preserving law of the supplied local group homomorphism:
`ι(g⁻¹) = ι(g)⁻¹`. No continuity, unramifiedness, irreducibility, or global
unitarity of the finite representation is required. This construction is
derived directly from the published definitions of restriction, algebraic
duality, and local components; it is not a newly asserted result from literature.

`Langlands.Global.FactorSeparation.noReflectedCommonZero_of_isUnitary` applies
`Langlands.LocalFactor.WeilDeligne.eulerPolynomial_eval_ne_zero_of_isUnitary`
to the original parameter and its dual. The original polynomial can vanish only
at norm one; at such a point the reflected argument has norm `q⁻¹ < 1`.
The proof uses `Langlands.FiniteRepresentation.isUnitary_dual` and allows
arbitrary monodromy and arbitrary normal inertia subgroup.

`Langlands.ClassField.Global.RelativeWeilGroup.isPairFactorMatch_of_unitary_gamma`
applies `Langlands.Global.FactorSeparation.certifiedFactorSeparation` to the
tensor of the supplied parameters, whose underlying action is unitary by
`Langlands.WeilDeligneRepresentation.tensor_isUnitary`. One supplied system
provides the original and dual L-polynomials and a self-dual measure. Smooth-dual
class uniqueness follows from
`Langlands.Correspondence.isSmoothDual_iff_eq_contragredient`. The arithmetic dual
pair agrees with the dual tensor through
`Langlands.WeilDeligneRepresentation.tensorDualEquiv` and
`Langlands.LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv`. Repeating
separation for every supplied system gives the required epsilon equalities.

`Langlands.ClassField.Global.RelativeWeilGroup.localPairClass_dual` lifts
`localComponentDualEquiv` through the zero-monodromy functor and composes it with
`Langlands.WeilDeligneRepresentation.dualZeroMonodromyEquiv`. Equality of the
classes follows from this actual pair equivalence.
`Langlands.ClassField.Global.RelativeWeilGroup.isPairFactorMatch_localPairClass_of_unitary_gamma`
then specializes the generic assembly to the local classes of two relative
Weil representations and their global algebraic duals, as used by the target.
The global field, parameter-carrier, and local-system universes remain
independent. The generic local assembly likewise permits independent local-field,
parameter-carrier, and system universes. The unitary noncancellation lemma also
permits the group and parameter-carrier universes to vary independently.

The algebraic separation input is the proved four-polynomial separation theorem
already used by `certifiedFactorSeparation`. No local Langlands correspondence
is used. The global gamma theorem, the passage from temperedness to certified
automorphic pole regions, and unconditional existence of a local-constant system
remain prerequisites for an application proving the global target. This bundle
does not supply proofs of those prerequisites or of the global target.
