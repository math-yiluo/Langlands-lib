# Positive torus points killed by simple roots lie in the split component: proof

This module proves the published proposition `Langlands.Global.PositiveTorusSplitComponentStatement` (module `AdelicPositiveTorusSplitComponentStatement`) as the theorem `Langlands.Global.positiveTorusSplitComponent`, at an arbitrary universe. No hypothesis is added. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §7.2, pp. 211–212. There the points \(a_\alpha\in\mathfrak A^G_{P_\alpha}\) and \(z_j\in\mathfrak A_G\) are taken directly in split components. The statement compares this with the description by positive points of the maximal split torus on which certain simple roots are trivial. The argument below is the one in the statement's Markdown ("Why it is true"). It is carried out with logarithms and real cocharacters, not with the identity component of \(\bigcap_{\beta\in J}\ker\beta\).

## The statement

Let \(\mathcal F\) be a `StandardParabolicFamily` of a group \(G\) over a number field \(F\), with maximal split torus \(\iota:T\to G\). Let \(J\) be a standard index and \(t\in T(\mathbb A)\). Assume that \(t\) lies in `PositiveRealTorus.intrinsicSubgroup F 𝓕.T` and that \(\beta(t)=1\) for every \(\beta\in J\). Then some \(a\) in `𝓕.positiveSplitComponent J` has the same image in \(G(\mathbb A)\) as \(t\).

## Auxiliary results (namespace `Langlands.Global.PositiveRealTorus`)

Let \(V(T)=\mathbb R\otimes_{\mathbb Z}X_*(T)\) and \(V^*(T)=\mathbb R\otimes_{\mathbb Z}X^*(T)\) be the real cocharacter and character spaces (`RealTorusSpace.V`, `RealTorusSpace.Vstar`), and let `RealTorusSpace.pair` be the real extension of the pairing \(\langle\chi,\lambda\rangle\). Let \(\mathrm{Dual}(T)=\operatorname{Hom}_{\mathbb Z}(X^*(T),\mathbb R)\) be `AdelicGroupPoints.RealCharacterDual F T.toGrp`.

- `cocharacterFunctional v`, for \(v\in V(T)\), is the element \(\chi\mapsto\langle 1\otimes\chi,v\rangle\) of \(\mathrm{Dual}(T)\). `cocharacterFunctional_apply` gives its value.
- `cocharacterFunctional_cocharacterMapReal`: for \(f:A\to T\) and \(w\in V(A)\), the functional of \(f_*w\) (`cocharacterMapReal f w`) is the functional of \(w\) composed with restriction of characters along \(f\) (`realCharacterDualMap`). This is the published naturality `pair_cocharacterMapReal`.
- `exists_cocharacterFunctional_eq`: if \(T\) is split, every \(\ell\in\mathrm{Dual}(T)\) is `cocharacterFunctional v` for some \(v\). The proof extends \(\ell\) to the real-linear form \(r\otimes\chi\mapsto r\,\ell(\chi)\) on \(V^*(T)\). The published `isPerfPair_of_isSplitTorus` says the real pairing is perfect, so `LinearMap.IsPerfPair.bijective_right` gives \(v\) with \(\langle x,v\rangle\) equal to this form for all \(x\in V^*(T)\). Evaluating at \(x=1\otimes\chi\) gives the claim.
- `eq_of_characterLog_eq` and `exists_characterLog_eq`: on a split torus, the normalized logarithm `characterLog` is injective on the intrinsic positive subgroup and maps it onto \(\mathrm{Dual}(T)\). Both follow from the published topological group isomorphism `positiveLogEquiv` (module `PositiveRealTorusLog`), applied to a splitting \(T\cong\mathbb G_m^I\) supplied by `IsSplitTorus`.
- `exists_intrinsic_map_eq_of_range_eq_rootAnnihilator`: let \(f:A\to T\) be a map of split tori with \(f_*(V(A))=\) `rootAnnihilator T R` for a set \(R\) of characters of \(T\). Let \(t\) be a positive point of \(T\) with \(\beta(t)=1\) for every \(\beta\in R\). Then there is a positive point \(a'\) of \(A\) with \(f(a')=t\) in \(T(\mathbb A)\).

  *Proof.* Write \(\operatorname{characterLog}(t)\) as `cocharacterFunctional v`. For \(\beta\in R\), \(\langle\beta,v\rangle=\log\|\beta(t)\|=\log 1=0\) (`characterLog_eq_log_characterValue`), so \(v\) lies in the annihilator of \(R\). By hypothesis \(v=f_*w\) for some \(w\in V(A)\). Choose a positive \(a'\) with \(\operatorname{characterLog}(a')=\) `cocharacterFunctional w`. By `characterLog_map` and the naturality above, \(\operatorname{characterLog}(f(a'))=\) `cocharacterFunctional (f_* w)` \(=\operatorname{characterLog}(t)\). The point \(f(a')\) is positive (`map_intrinsicSubgroup_le`), so \(f(a')=t\) by injectivity of the logarithm on positive points.

## The proof of `positiveTorusSplitComponent`

Let \(\mathcal F\), \(J\) and \(t\) be as in the statement. The compatibility data `𝓕.isCompatible J` give the following facts:

- \(l_J\circ p_J:M_J\to G\) is a closed subgroup. The Levi and the parabolic are closed subgroups, and closed immersions compose.
- \(l_J\circ p_J\) represents `standardLevi 𝓕.i 𝓕.ν J` (`levi_eq`).
- \(a_J:A_J\to M_J\) is a split component (`splitComponent`).

The published theorem `standardLeviCentralDirections` (second conjunct) therefore gives \(f:A_J\to T\) with \(f\circ\iota=a_J\circ l_J\circ p_J\) and \(f_*(V(A_J))=\) `rootAnnihilator T J`. Both tori are split: \(A_J\) because a split component is a split subtorus, and \(T\) by maximality. The auxiliary result above gives a positive \(a'\in A_J(\mathbb A)\) with \(f(a')=t\). Put \(a=(a_J\circ l_J)(a')\in P_J(\mathbb A)\). It lies in `𝓕.positiveSplitComponent J` by the definition of that subgroup as the image of the intrinsic positive subgroup. Its image in \(G(\mathbb A)\) is \((a_J\circ l_J\circ p_J)(a')=\iota(f(a'))=\iota(t)\), by the factorization identity.

The factor \(f\) used here is the one produced by `standardLeviCentralDirections`, and the proof does not compare it with the field `𝓕.f J`. Only the identity \(f\circ\iota=a_J\circ l_J\circ p_J\) is used.

## Use

The theorem discharges the premise `PositiveTorusSplitComponentStatement` of the conditional reduction `eisensteinSystemDomination_of` (module `AdelicEisensteinSystemDominationReduction`). It turns the torus points \(t_\alpha\) and \(z_j\) of `IsLocalFinitenessGroupData` into points of \(\mathfrak A_{P_\alpha}\) and \(\mathfrak A_G\).
