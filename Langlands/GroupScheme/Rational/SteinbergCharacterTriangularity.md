# Actual triangular character restriction and quotient assembly

Author: Worker 1284. The restriction predicate and assembly proofs are internal algebraic constructions. The universal triangularity proposition is a derived statement from Steinberg's triangular character calculation and representative comparison.

For every field and supplied pinning, ordering, normalized root family, reflection-representative family and actual fundamental-representation family `F`, `HasTriangularFundamentalRestriction e x n F` says that the actual polynomial restriction of `(F (e j)).character` is

`C (c j) * X j + f j`.

Here each `c j` is a unit of the original field. There must be a well-founded relation on `Fin r` such that every variable in `f j` lies below `j` for that relation. The relation is existentially quantified; it need not agree with the numerical order on the supplied product indices. The coefficients of the remainders lie in `k`; no integral-coefficient assertion is made. The restriction is `SplitPinning.steinbergRestriction`, formed from the actual invariant-coordinate inclusion, and the character is the actual trace of the supplied matrix representation.

`steinbergProduct_rho_isIso_of_fundamental_triangular` proves a conditional result. Its inputs are bijectivity of the fundamental-character map into the actual invariant algebra and the preceding restriction formula. Extensionality on polynomial variables identifies the composite of generation and restriction with `TriangularPolynomial.substitution`. The proved well-founded triangular polynomial automorphism makes that composite bijective. The restriction criterion and polynomial-generation helper then give exactly

`IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G)`.

This helper is available over arbitrary fields whenever its explicit inputs are supplied. It establishes neither input.

`SplitSteinbergCharacterTriangularStatement.{u}` is an unproved `Prop`-valued definition. It asserts the restriction predicate for every algebraically closed field in arbitrary universe `u` and characteristic, actual affine group, supplied split pinning, the Library's `IsSimplyConnected` premise, every ordering, every actual fundamental-representation family and every supplied normalized-root and reflection-representative family. It assumes no canonical representatives, scalar normalization or triangular formula.

The last theorem is also expressly conditional. Given proofs of fundamental-representation existence, free invariant generation and the universal triangularity proposition, it chooses the actual fundamental representations and applies the first helper to obtain the canonical quotient isomorphism over an algebraically closed field. Those three structural propositions are inputs, and this theorem proves none of them. Descent to arbitrary fields remains a separate obligation. Thus this pair does not prove the host `SplitSteinbergQuotientStatement`.

The original source is R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publications Mathématiques de l'IHÉS 25 (1965), 49–80, registered as `steinberg-1965-regular-elements-semisimple-groups`, SHA-256 `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`. Lemma 7.14 and its proof, printed pp.68–69 (PDF pp.21–22), give the formula with diagonal coefficient one for specially normalized root coordinates and representatives in the rank-one subgroups. The order is the strict partial order of 7.10–7.11; its finite indexing set makes it well founded. Lemmas 7.5–7.6, printed p.67 (PDF p.20), compare arbitrary reflection representatives by torus conjugation. These pages were read in full; no project errata note for this source was found.

The current proposition is a derived translation to the supplied actual product and trace coordinates. The proof must relate the supplied normalized root maps to the source normalization, handle arbitrary supplied representatives, identify the supplied fundamental-representation traces with the source characters, and establish the actual coordinate identities over the field. The allowed unit diagonal records coordinate rescaling. The original source works over an algebraically closed field; no descent assertion is included in the triangularity proposition. All source comparisons, the actual triangular calculation and the three structural proofs remain obligations, not hidden premises.
