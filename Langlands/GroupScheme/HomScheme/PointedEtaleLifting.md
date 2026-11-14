# Pointed etale lifting from a split torus

`SplitSourcePointedEtaleLiftingStatement` concerns an arbitrary scheme `S`, a
split torus `H` over `S`, and a smooth affine group scheme `G` over `S`. Every
actual homomorphism from the residue fibre of `H` to the residue fibre of `G`
extends over an etale neighbourhood with a specified point over the original
residue point. Evaluation at that specified point recovers the original
homomorphism exactly. There is no closedness or monicity assumption on the
homomorphism.

This is an internal consequence of the published smooth representability of the
actual relative Hom functor and the published pointed etale section construction
for smooth morphisms. The theorem `splitSourcePointedEtaleLifting` implements
that consequence: choose the universal Hom parameter of the prescribed fibre
homomorphism, extend that parameter by a pointed smooth section, and evaluate
the universal family on the resulting neighbourhood. Functoriality of
evaluation and the specified point equation give exact recovery.

All base changes in the statement are actual group-scheme pullbacks, and recovery
uses `HomScheme.evaluate`, including its canonical pullback comparisons. The
base scheme need not be affine or noetherian. For cocharacters, take `H` to be
the multiplicative group and use its published base-change isomorphism.
