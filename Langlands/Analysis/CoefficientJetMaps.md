# Continuous coefficient maps on finite jets

Given a sequence of continuous linear maps \(T_d:E\to F\), `jetMap m T` acts on jets with \(m\) coefficients. In degree \(i\) it takes \((u_j)_{j<m}\) to \(\sum_{j\leq i}T_{i-j}u_j\). Each coordinate is a finite sum of continuous linear maps.

`CoefficientJetCompositionStatement` says that a coefficient convolution identity for two such sequences gives the composition identity of their jet maps at every length. By linearity it suffices to consider an input with one nonzero coefficient, in degree \(j\). The output in degree \(i\) uses exactly the intermediate degrees between \(j\) and \(i\). Subtracting \(j\) reindexes this sum as the assumed convolution identity in degree \(i-j\). The module also computes that a monomial coefficient operator acts by its coefficient shift.

This is the coefficient-coordinate multiplication for finite jets of continuous operator families. It gives the continuous maps used in the higher-jet closed-range argument of Casselman, *Canonical extensions of Harish-Chandra modules to representations of G*, Proposition 9.3, once the coefficient identities of the operator families are supplied.
