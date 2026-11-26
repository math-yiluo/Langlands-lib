# Integral monomiality of arithmetic epsilon factors

`LocalFactor.SpectralConductor.mem_monomialSubgroup` shows that for a supplied local-constant system at the bottom field, the value of every continuous exact class \(x\) under spectral twist is its original epsilon value times \((q^{-s})^m\) for an integer \(m\).

The classes with this property form an additive subgroup by the system's additive law. The rank-one formula `value_virtualTwist_characterClass` gives the trivial character, and `value_virtualTwist_induce` gives the classes induced from differences of characters. For the latter, `log_residueCardinality` relates the two spectral parameters by the residue degree. `commonClosureDegreeZeroGeneration` expresses the degree-zero remainder after subtracting copies of the trivial character in terms of these induced differences.

`Correspondence.isArithmeticPairEpsilonFactor_of_monomial` applies this calculation to two continuous local Weil representations with zero monodromy. It restricts to the bottom field, transports to the system's carrier universe and forms their exact tensor class. `IsBaseRestriction.nonempty_equiv` compares the input representations with all admissible restriction data, and `eq_localSelfDualHaar` fixes the transported self-dual measure. `conditionalPairEpsilonValue_eq_of_equiv` transfers the values, while `conditionalEpsilonValue_of_monodromy_zero` removes the Weil–Deligne correction. A geometric Frobenius exists by `baseGeometricFrobenius`.

The monomial form comes from Tate, *Number theoretic background*, (3.4.2)–(3.4.5), printed p. 15, and Deligne, *Les constantes des équations fonctionnelles des fonctions L*, (5.5.2), manuscript p. 48. The implementation computes the existence of the integral exponent by generation.
