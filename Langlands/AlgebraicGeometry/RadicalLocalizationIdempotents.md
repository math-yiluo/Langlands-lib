# Extending idempotents across a reduced principal divisor

This internal algebraic unit supports the flat discrete valuation ring step in the section-component openness argument. Let \(A\) be a commutative ring, let \(t\) be a nonzerodivisor, and suppose the principal ideal \((t)\) is radical. Let \(S\) be any localization of \(A\) obtained by inverting \(t\).

`existsUnique_idempotent_of_away_radical` proves that every idempotent of \(S\) is the image of a unique idempotent of \(A\). The quotient formulation `existsUnique_idempotent_of_away_quotient_reduced` replaces radicality of \((t)\) by reducedness of \(A/(t)\).

The implemented proof first uses regularity to make \(A\to S\) injective. Write an idempotent as \(e=a/t^n\). The idempotent identity gives \(a^2=t^n a\) in \(A\). If \(n>0\), radicality of \((t)\) implies \(a\in(t)\). Write \(a=tb\), cancel the invertible image of \(t\) in \(S\), and induct on \(n\). The resulting lift is idempotent by injectivity, which also gives uniqueness.

`idempotentEquivOfAwayRadical` constructs the resulting equivalence between the actual sets of idempotents of \(A\) and \(S\). Its forward map is the given localization map, as recorded by `idempotentEquivOfAwayRadical_apply`; surjectivity and injectivity are supplied by the extension argument and the injectivity of localization.

`exists_clopen_of_away_radical` uses Mathlib's correspondence between idempotents and clopen subsets of prime spectra to extend every clopen subset of \(\operatorname{Spec}S\) to one of \(\operatorname{Spec}A\). `preconnectedSpace_away_of_radical` then proves that preconnectedness of \(\operatorname{Spec}A\) implies preconnectedness of \(\operatorname{Spec}S\). It asserts preconnectedness only, so no nonemptiness premise is suppressed.

The arguments are internal derivations from elementary localization, radical ideals, and the existing Mathlib clopen correspondence. They are motivated by the specialization step in EGA IV, third part (1966), Lemma 15.5.6, Proposition 15.6.4 and Corollary 15.6.5. They do not formalize the printed proof of Lemma 15.5.6, which uses a local connectedness result, and do not yet assert connectedness of generic fibres for arbitrary schemes or openness of selected components. No Noetherian hypothesis is needed for the algebraic statements proved here.
