# Extending characters across a subgroup product

`relativeEndUnits_comapEquivInf` identifies the pullback of an ambient endomorphism unit subgroup \(H\) with \(H \cap B^\times\), where \(B\) is the centralizer of the parameter field. Restriction of scalars is injective and its range is the centralizer of the generating element, by `relativeEndUnits_range_eq_centralizer`.

The extension in BK93 (3.2.5) starts with a determinant-factoring character on a deeper subgroup \(D\). Its determinant character extends to the units of the parameter field by divisibility of \(\mathbb C^\times\). Pulling back along the determinant and the equivalence gives a character on \(U = H \cap B^\times\) that agrees with the given character on \(U \cap D\).

When \(H=UD\) and \(U\) normalizes the character of \(D\), `exists_monoidHom_of_compatible_restrictions` glues the two characters. The glued character kills the relative determinant kernel on the pullback of \(H\), which gives the factorization.

Let \(K\) be a subgroup of \(B^\times\) that normalizes \(H\). Conjugation by \(K\) preserves \(U=H\cap B^\times\) and the relative determinant on \(U\). If \(K\) also normalizes the restriction of a determinant-factoring character \(\chi\) on \(H\) to \(D\), the product \(H=UD\) shows that \(K\) normalizes \(\chi\). In the simple-stratum application, BK93 (3.1.15)(ii) supplies the normalization of \(H\) by the relative order normalizer.

`image_fibres_of_relativeDet_extension` uses the extension for surjectivity and takes the ratio of two characters with the same restriction for the fibre formula. The source is Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (3.2.5), printed pp. 99–100.
