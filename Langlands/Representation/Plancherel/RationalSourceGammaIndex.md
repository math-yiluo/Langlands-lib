# Actual source gamma from finite subgroup indices

Author: Worker 200.

This derived adapter follows Waldspurger (2003), I.1, formula (2) and the
proof of Remark (3), printed pp.240–241 / PDF pp.6–7. It works on actual
rational points in the existing general reductive framework, with the
canonical topology, Borel measurable space, and common compact K Haar
normalization. The field universe and arbitrary characteristic are retained.

`sourceTraceIndex K H L` is the relative index of H intersect L in K
intersect L, formed on the actual carrier L. For a closed L, compactness of
K and openness of H prove this index is nonzero. No finite-index hypothesis
is postulated. If H is contained in K, its trace has mass equal to the
inverse of that index under the already prescribed subgroup Haar measure.

`gammaIndex` is [K:H] times the inverse trace indices for M, U and the
opposite radical, in the multiplication order M times (U times opposite U).
It is defined without choosing or changing a Haar measure or gamma.

The volume formula applies the existing actual Levi-first open-cell lower
integral to the indicator of H. The explicit local premise says that
m u v belongs to H if and only if each of m, u and v belongs to H. The
indicator therefore factors; successive lower integrals yield the product
of the three original trace masses. The theorem retains compact-limit
stability for K and connected reductivity, which supply the normalized
semidirect measure and conull open cell. H need only be open in this theorem.

`gamma_eq_gammaIndex` additionally requires H contained in K. The ambient
index is finite by compactness and openness, and all four Haar evaluations
become finite-index expressions. The proof multiplies the volume formula
by [K:H] and cancels the already proved positive finite gamma.

No ambient or Levi right invariance or Iwasawa factorization is an added
premise. The local H factorization and K limit stability are explicit
structural premises, not asserted realizations. This unit does not prove
existence of one H for all parabolics, a root-subgroup product formula,
same-Levi independence, or any Plancherel conclusion. These further steps
in the source's Remark (3) remain separate obligations.
