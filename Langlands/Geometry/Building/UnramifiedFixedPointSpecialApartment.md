# A special apartment through a prescribed fixed point

`UnramifiedFixedPointSpecialApartmentStatement` is the one-point special-apartment
containment input for unramified building descent. Let \(F\) be a nonarchimedean
local field, \(K\) its maximal unramified extension, and \(G\) a connected
reductive group over \(F\). The supplied \(F\)-torus \(T\) becomes maximal split
over \(K\). Its supplied root-valuation apartment datum \(D\) satisfies full V6
with its actual centralizer and the canonical integer valuation, and is stable
under the coefficient action of every \(F\)-automorphism of \(K\).

For each coefficient-fixed point \(y\) of `D.ReducedBuilding`, the statement
asserts the existence of a maximal \(F\)-split subtorus \(S'\) and a containing
closed \(F\)-subgroup \(T'\) that becomes a maximal split torus over \(K\).
Containment is expressed by an actual morphism \(f':S'\to T'\) whose composition
with the inclusion of \(T'\) is the inclusion of \(S'\).
There are \(g\in G_K(K)\) and an isomorphism \(e:T_K\to T'_K\) such that
\(\operatorname{Int}(g)\circ i_{T,K}=i_{T',K}\circ e\), and a point \(x\) of the
original apartment such that \(y=g\cdot D.\mathrm{apartmentMap}(x)\).
Thus the special apartment is expressed as a translate in the supplied quotient.
The conjugator is a \(K\)-point; the statement does not require it to descend to
an \(F\)-point, and does not assert coefficient fixation of \(x\).

This is a derived formulation of the diagonal one-point case of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.3.8,
printed pages 334–335 (PDF pages 365–366). That proposition places two
coefficient-fixed building points in a special \(F\)-apartment. Section 9.2.2
describes the special torus and its maximal \(F\)-split subtorus. Conjugacy of
maximal split tori over \(K\) expresses this apartment in the original quotient
by \(g\) and \(e\). The supplied full V6 class is compared with the canonical
building by uniqueness of compatible valuation classes, Proposition 6.2.6,
printed page 216 (PDF page 247). These comparisons remain part of the geometric
proof obligation of the new statement.

The book is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' *Corrections and additions*, version of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pages 39–41, correct later special-apartment comparisons and leave
Proposition 9.3.8 unchanged.

`unramifiedFixedPointSplitTorus_of_specialApartment` proves the conditional
implication from this statement to `UnramifiedFixedPointSplitTorusStatement`.
For a \(K\)-point \(a\) in the character-valuation kernel of \(S'_K\), compose
\(f'_K\) with \(e^{-1}\) to map \(a\) into \(T_K\). The already proved
`torusUnitApartmentFixation` applies character-kernel functoriality and full V6
to show that this image fixes \(D.\mathrm{apartmentMap}(x)\). Composing the
conjugacy equation with \(e^{-1}\circ f'_K\), and using the factorization of
the inclusion of \(S'\), identifies its conjugate by \(g\) with \(i_{S',K}(a)\).
Acting by \(g\) on the fixation equation shows that \(i_{S',K}(a)\) fixes \(y\).
This proves fixation by every such \(a\), with \(S'\) maximal split as required.

The new geometric declaration is a proposition definition. The module proves
only the stated implication; it supplies neither a proof of special-apartment
containment nor an unconditional proof of the rational building covering
target. It uses no full building-descent assertion.
