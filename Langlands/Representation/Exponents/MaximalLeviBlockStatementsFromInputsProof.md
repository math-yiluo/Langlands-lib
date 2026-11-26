# Proof of the block corollary reduction in Renard VII.1.3

`Langlands.Aubert.General.RepresentedParabolic.maximalLeviBlockStatementsFromInputs`
proves `MaximalLeviBlockStatementsFromInputsStatement.{u, v}`. Its premises are
`MaximalLeviSupercuspidalReducibilityStatement.{u, max u v}` and
`MaximalLeviBlockFullEssSurjStatement.{u, v}`. The conclusion is
`MaximalLeviBlockStatements.{u, v}` for the normalized induction and Jacquet functors
on the actual rational points. [Reduction statement](MaximalLeviBlockReductionStatements.md)

## Irreducibility of the induced twists

`maximalLeviBlock_irreducible_detection` proves parts (i) and (ii) from the reducibility
premise. If \(\sigma\) is a twist of \(\rho\) by the unramified character \(\psi\), its
defining linear equivalence \(T\) gives a smooth isomorphism
\(\rho \otimes \psi \simeq \sigma\). The kernel of \(\psi\) is open.
`SmoothRep.isIrreducible_twist_iff` gives irreducibility of the twist.
`properJacquet_subsingleton_unramifiedTwist` gives vanishing for each proper Jacquet
module of the twist, and the corresponding Jacquet functor transports this vanishing
to \(\sigma\) along the smooth isomorphism.

If \(i_P^G\sigma\) were reducible, the first premise applied to \(\sigma\) would supply
a normalizing element \(g\) outside the Levi image, the induced automorphism \(\varphi\)
of \(M\), an unramified character \(\psi'\), and an intertwining equivalence \(T'\)
from \(\sigma\) to the twist pulled back along \(\varphi\). The proof uses the character
\[
  \chi = \psi'\,\psi\,(\psi \circ \varphi^{-1})^{-1}
\]
and the equivalence \(T'' = T^{-1} \circ T' \circ T\).
`Plancherel.rationalUnramifiedCharacterRestrict` supplies the unramified pullback along
\(\varphi^{-1}\). Writing \(\varphi(m)\) for the induced map on rational points, the
intertwining equations give
\[
 T''\rho(m) =
 \psi'(\varphi(m))\,\psi(\varphi(m))\,\psi(m)^{-1}\,\rho(\varphi(m))T''
 = \chi(\varphi(m))\,\rho(\varphi(m))T''.
\]
Thus the same \(g\) and \(\varphi\), with \(\chi\) and \(T''\), contradict the
non-self-association hypothesis on \(\rho\).

## Detection by normalized Jacquet restriction

For a nonzero object \(Y\) of `InBlockG`,
`SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient` supplies an
irreducible subquotient \(\tau\). By the block condition, \(\tau\) is a subquotient of
\(i_P^G\sigma\) for an unramified twist \(\sigma\) of \(\rho\). The induction is irreducible
by part (i), so `CuspidalSupport.NormalHecke.nonempty_iso_of_isSubquotient` gives
\(\tau \simeq i_P^G\sigma\).

Under `leviFrobeniusReciprocity`, the nonzero identity of \(i_P^G\sigma\) corresponds to
a nonzero map \(r_P^G(i_P^G\sigma) \to \sigma\). This map is surjective because \(\sigma\)
is irreducible. The isomorphism with \(\tau\) therefore makes \(\sigma\) a quotient of
\(r_P^G\tau\). Exactness from `leviParabolicFunctorsExact` and
`ExactSmoothTransport.map_isSubquotient` make \(r_P^G\tau\) a subquotient of \(r_P^G Y\).
`smoothSubquotientTransitivity` gives the required irreducible subquotient \(\sigma\).

## Induction on the blocks

The main theorem applies `maximalLeviBlock_irreducible_detection` and the second premise
to the same parabolic and inducing data. The second premise supplies preservation of
the block, fullness and essential surjectivity. `leviInductionFunctor_faithful` gives
faithfulness on all smooth representations of the Levi. Composing with the faithful
full-subcategory inclusion gives faithfulness on `InBlockM`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VII.1.3, Corollary and proof, printed pp. 226–227 / PDF pp. 232–233.
Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard derives part (i) from the reducibility theorem. The formal part (ii) expresses
the nonvanishing criterion used in the source to prove faithfulness of the projected
Jacquet functor. Renard obtains nonvanishing by the geometric lemma VI.5.3. The Lean
argument uses Frobenius reciprocity and exactness with the induction-occurrence
description of `InBlockG`.
