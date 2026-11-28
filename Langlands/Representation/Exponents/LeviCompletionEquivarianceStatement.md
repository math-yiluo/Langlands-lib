# Equivariance of the opposite Jacquet completion comparison

`Langlands.Aubert.General.RepresentedParabolic.LeviCompletionEquivarianceStatement`
relates the existing linear completion comparison to the Levi action used in
Renard, *Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, VI.9.7, printed pp. 205–206 / PDF pp. 211–212. The theorem gives
the component formula for the comparison, and the adjunction calculation
after the proof uses it on morphisms of \(M\)-modules.

Assume the existing `LeviCompletionOppositeJacquetStatement`. For a pair
of opposite rational parabolics \(P=MN\) and \(\bar P=M\bar N\) and each
smooth complex representation \(V\), the derived statement gives the
unique family of linear equivalences
\(\bar V^{N(F)} \simeq \overline{V_{\bar N}}\) characterized by the
Jacquet quotient formula on the compact-open components with Iwahori
contraction. The target uses
`leviUnnormalizedJacquetFunctor`, the action of \(M(F)\) on the
\(\bar N(F)\)-coinvariants before twisting by the modulus character.

For each Levi point \(m\), translating a radical-fixed family produces
a radical-fixed family, and the comparison identifies this translation
with the translation by \(m\) on the completed Jacquet module. The
statement also uses the actual maps of completed families
`CompactCompletion.mapFixed` and `CompactCompletion.map` to express
naturality in \(V\). The compact indices, contraction conditions, and
actual Levi inclusion are those of
`LeviCompletionOppositeJacquetStatement`.
