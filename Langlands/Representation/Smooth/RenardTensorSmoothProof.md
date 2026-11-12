# Smoothness of the diagonal tensor product

Author: Worker 139. The theorem `Langlands.Renard.Smooth.tensorProductSmooth`
proves exactly `TensorProductSmoothStatement`, with independent group and carrier
universes and no additional hypotheses.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.14–III.1.15, printed pp.66–67 / PDF pp.72–73 (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The source defines the diagonal tensor representation and uses its smoothness
to define the tensor endofunctor on smooth representations.

The implementation applies the published general commutative-ring theorem
`TensorHom.tensor_smooth`. That theorem inducts over the algebraic tensor:
a pure tensor of vectors fixed by open subgroups K and L is fixed by K ∩ L,
and smooth vectors are closed under addition. The proof therefore needs
neither admissibility nor any finiteness condition on the representations.
The statement module and all its imports are unchanged.
