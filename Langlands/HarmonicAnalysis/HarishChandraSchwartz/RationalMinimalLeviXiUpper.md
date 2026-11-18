# Xi upper bound on the full minimal Levi

This internal derived adapter extends the separately owned
`RationalXiUpperBoundStatement` from the common-uniformizer chamber to the
closed chamber in the full actual minimal Levi. It does not prove that
substantive upper-bound statement.

The compact dominant reduction gives each closed-chamber point as a dominant
uniformizer point with two multipliers in a fixed compact subset of the
minimal Levi. Uniformizer points belong to the maximal split torus and hence
are central in the minimal Levi; the two multipliers combine on the left.
The resulting compact subset lies in the actual minimal parabolic.

The proof reuses Worker 842's `RationalXiFullChamber` compact-extension lemma and
identity compatible-minimal-component theorem, with their unchanged source
pair and auxiliary chamber-section pair. The lattice upper estimate applies
to this identity component, and the generic compact extension preserves its
exact Iwasawa half-weight. On a minimal-Levi point that half-weight is exactly
`minimalLeviSqrtModulus`. The polynomial's real exponent is enlarged to its
natural ceiling, since one plus the matrix height is at least one.

The full result retains the original connected reductive, maximal split,
generic, compact/Iwasawa and closed finite matrix representation data, a
supplied simultaneous standard basis, compactness of the supplied structural
subgroup, and its empty-index standard-Levi Cartan covering. It covers every
point of the original minimal-Levi closed chamber, rather than only torus
points or a strict chamber.

The context is Waldspurger (2003), II.1.1 and its use in VI.2.3, printed
pp.251 and 299–301. Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
This extension is internal derived content. Worker 836 owns the separate
lattice upper-bound proof; Worker 842 supplied the reused compact-extension
and identity-component results. Neither pending supporting publication is
asserted to be an unconditional proof of the analytic upper statement.
