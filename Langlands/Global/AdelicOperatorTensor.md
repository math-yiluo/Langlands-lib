# Operator actions on a finite-adelic and archimedean tensor

`Langlands.Global.AdelicOperatorTensor` uses a single slot for the restricted
finite adelic tensor and one slot for each real or complex place of the
number field. An archimedean carrier is transported through `ULift.moduleEquiv`
to place all the carriers in the universe of the finite carrier.

The designated operators are the finite adelic translations in the grouped
slot and the compact and complexified Lie operators in each infinite slot.
`operatorIndex` uses the actual inclusions of each local compact and
complexified Lie algebra. The complex-place Lie operators act on the
complexification of the full real Lie algebra of complex matrices.
`HasActions` identifies the image of each designated generator under a
supplied free algebra representation with its action on just its one slot.

The grouping implements the tensor of local constituents in Langlands
(1979), Lemma 1, printed p. 203 (Corvallis I PDF p. 198), and in Getz–Hahn
(2024), Theorems 10.7.1 and 10.7.5, printed pp. 286 and 288 (PDF pp. 298
and 300).
