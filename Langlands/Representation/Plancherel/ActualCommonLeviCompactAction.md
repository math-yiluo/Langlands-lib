# Actual common-Levi action in the fixed compact tensor

`compactTensorRepresentation` acts on `compactFiber` by the external product
of the actual compact induction representations. The first factor uses the
original unramified parameter and the second uses its inverse on the inducing
smooth contragredient. `compactTensorRepresentationEquiv` intertwines this
representation with the actual coefficient fiber and has the existing
`compactTensorEquiv` as its linear equivalence. Its proof composes the actual
product induction equivalence with the tensor of the two compact restriction
equivalences, using `dualInductionEquiv` before restricting the dual factor.

For a fixed element of the full product group, the action is a polynomial
operator family on the parameter space. The two factors use the published
transported polynomial action theorem, algebraic parameter inversion in the
dual factor, and the polynomial tensor theorem. On the compact product both
factors restrict to the original compact-picture right actions, independently
of the parameter.

This is an internal consequence of the actual compact picture and the inverse
parameter identification. It supplies the full action needed when extending
the rational tensor in Waldspurger's Lemma V.3.1 (2003, printed p. 295,
PDF p. 61, registered source `waldspurger-2003-plancherel`).
