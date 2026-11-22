# Zariski gluing for the affine formal spectrum

The functor `AdicAffineChart.continuousPointFunctor` satisfies `Nilp.IsZariskiLocal`. For each element of the complete algebra, the structure sheaf localization theorem glues its values in a matching family of continuous maps. Joint injectivity of the principal localizations gives the ring and base algebra identities for the glued map. A finite principal subcover suffices to check that the map annihilates a single power of the ideal of definition. Taking the maximum of the local exponents on that finite subcover supplies this power, and joint injectivity on the subcover proves the annihilation. Joint injectivity on the original cover also gives uniqueness.

The natural identification with continuous algebra maps transports this gluing to the colimit of ordinary quotient scheme points. `AdicAffineChart.oneChartPresentation` exhibits that colimit as a formal scheme on affine `Nilp`. The single chart inclusion is the isomorphism removing the universe lift and its inverse image over each affine test is the entire spectrum.

This proves the affine chart case of the Zariski-local formal-scheme description in Rapoport and Zink, *Period Spaces for p-divisible Groups* (1996), §2.1, printed p. 49 (PDF p. 64), using the basis of principal opens of each affine test.
