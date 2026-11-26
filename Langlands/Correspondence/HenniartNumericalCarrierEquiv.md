# Supercuspidal carrier changes for Henniart's numerical injections

`Langlands.Henniart.Numerical.numericalInjectionCarrierEquiv K k` identifies
the numerical injections in rank \(k+1\) across two supercuspidal carrier
universes. The p-adic field and the Weil carrier universe are fixed. A function
from the irreducible Weil classes changes by postcomposition with
`PadicField.TopologicalData.supercuspidalClassCarrierEquiv`.

Two invariants make this postcomposition respect the numerical conditions.
`supercuspidalClassCarrierEquiv_twist` uses `twistEquiv` to twist an
intertwiner by any open-kernel character of the determinant. Applying the
representative criterion to the twisted intertwiner gives equality of the
twisted classes. `supercuspidalFirstFixedLevel_carrierEquiv` uses
`Conductor.firstFixedLevel_eq_of_equiv` on representatives, including the
infinite value of the first fixed level. The unramified determinant characters
used in `Numerical.supercuspidalUnramifiedTwist` satisfy the kernel
hypotheses of the first lemma.

`isNumericalInjection_comp_carrierEquiv_iff` combines these identities with
injectivity of the class bijection. The equivalence of function spaces then
restricts to the subtypes defined by `IsNumericalInjection`.
`surjective_numericalInjectionCarrierEquiv_iff` uses the class bijection in
both directions to compare surjectivity. Applying this comparison to every
numerical injection gives `Langlands.Henniart.numericalSurjectivity_carrierEquiv_iff`.
A proof of the numerical surjectivity proposition at supercuspidal carrier
universe `0` therefore suffices for every supercuspidal carrier universe.

This is an internal consequence of the
[class equivalence](../Representation/Classification/SupercuspidalCarrierEquiv.md),
the existing [first fixed level](../Representation/Conductor/ClassLevel.md),
and the [numerical injection predicate](HenniartNumericalStatement.md).
The last predicate formalizes the hypotheses of Henniart (1988),
Théorème 1.2, printed p. 498, in `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
