# Inflation and invariants along an identified quotient

In the Hom calculation following VI.9.7, Renard uses the adjunction of
inflation along \(P \to M\) and formation of \(N\)-invariants, where \(N\)
is the unipotent radical and \(M\) is the Levi subgroup. This is the
algebraic adjunction used before taking smooth vectors. See Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026,
VI.9.7, printed p. 206 / PDF p. 212.

`Langlands.Induction.quotientInflationInvariantsAdjunction` takes a normal
subgroup \(N\) of a group \(P\) and a group isomorphism \(e:P/N \simeq M\).
Over any commutative coefficient ring, its left functor is pullback along
\(P \to P/N \xrightarrow{e} M\). Its right functor first takes the
actual \(N\)-fixed submodule with the quotient action, then pulls that
action back along \(e^{-1}\). The group and representation carrier
universes are independent.

Pullback along \(e\) and \(e^{-1}\) gives an equivalence of algebraic
representation categories. The isomorphisms for the two composites
use the identity linear maps and the two inverse equations for \(e\).
Compose the adjunction of this equivalence with
`inflationInvariantsAdjunction` for \(P/N\). The counit acts by the
inclusion \(W^N \hookrightarrow W\), as recorded by
`quotientInflationInvariantsAdjunction_counit_app_apply`.

For \(P=M\ltimes N\), the identification \(P/N\simeq M\) is induced by
the inclusion of the complement. The two functors then use the Levi
projection and the restriction to the Levi of the action on the
unipotent-radical invariants.
