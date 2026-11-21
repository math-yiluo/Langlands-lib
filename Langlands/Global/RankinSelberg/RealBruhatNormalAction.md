# Nilpotence on the real Bruhat normal space

`Langlands.Global.RankinSelbergGlobal.RealBruhatNormalAction.RealBruhatNormalActionStatement`
starts at a point of the zero normal section of a real Bruhat product chart.
For any adjacent ascent of the permutation, the corresponding paired root
action has an infinitesimal action that preserves the tangent subspace. Its
induced endomorphism of the normal coordinates is nilpotent.

The proof applies the paired root action to a tangent path in the cell. The
path stays in the cell and its base point is fixed by the action. The derivative
of its inverse chart therefore has zero normal component. This holds for every
root parameter. Differentiating with respect to that parameter gives the
claimed zero normal component for the ambient infinitesimal map on tangent
inputs. The chart derivative conjugates the ambient nilpotent generator to
one on the product space. The normal projection intertwines that generator
with the transverse endomorphism, so nilpotence descends by surjectivity.

This internal consequence of the smooth product charts and the paired root
stabilizer supplies the normal action needed for the distribution argument on
lower Bruhat cells.
