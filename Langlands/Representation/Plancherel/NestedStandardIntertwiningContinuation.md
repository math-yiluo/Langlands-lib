# Rational continuation under Levi restriction

This module implements the compact-model step of Waldspurger's induction-in-stages comparison in IV.1(14). It uses the actual ambient and inner normalized stages constructions with the inner compact subgroup given by intersection with the intermediate Levi.

The character parameters are indexed by a supplied norm family on a group continuously isomorphic to the inducing Levi. The upper family on the original region is given in its fixed compact models. Its normalized extensions must represent the weak standard integral over the supplied ambient quotient measure at every parameter in that region. The inner measure is the exact pushforward under the quotient homeomorphism.

`HasNestedCompactContinuation` asks for continuation data on the inner compact carriers with the upper denominator, the weak-integral relation on the original region, and the restriction square there. `hasNestedCompactContinuation` chooses a single linear section of the upper source restriction and transports the polynomial numerator by this section and the fixed target restriction. The conjugate section on each normalized source model produces the inner integral by `RepresentsStandardIntegral.nested_comp`. Weak-integral uniqueness gives the restriction square. Closedness of the inducing Levi and compact-subgroup containment of the target radical supply the uniqueness and outer half-character hypotheses, respectively.

Source is Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*, 2003, IV.1(14), printed page 284 (PDF page 50), registered as `waldspurger-2003-plancherel`.
