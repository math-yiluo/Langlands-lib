# Absolute convergence at characters of equal modulus

The unramified compact extension at each ambient point is a fixed vector multiplied by one character evaluation on the Levi. `norm_unramifiedCompactIntegrand_eq_of_character` applies this formula on representatives of the radical quotient. Characters of equal modulus give equal norms for each scalar test on the original integrand.

`standardCompactFullDomain_of_character_norm_eq` uses the compact restriction equivalence and the smooth-dual twist equivalence to compare scalar integrability for all input vectors. Admissibility of the twisted representation and `scalarDomain_eq_domain` recover weak integrability with values in the original inducing carrier. The quotient measure and squared-modulus compatibility are those of the original integral.

`continuous_standardCompactOperator_scalar_of_character_norm_eq` applies dominated convergence along any continuous family of full parameters of one character modulus. For each compact section, compact evaluation point and smooth functional, the integrable absolute value at a fixed full parameter dominates the entire family. The resulting continuity is scalar and needs no topology on the compact carrier.

These are derived steps from the compact extension formula and the weak integral in the Library. The scalar integrability convention is the one in Waldspurger (2003), IV.1, printed pp. 277–278 (PDF pp. 43–44), `waldspurger-2003-plancherel`, SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`. [Original publication](https://doi.org/10.1017/S1474748003000082)
