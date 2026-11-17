# Fixed compact carriers for the actual normalized tensor

This internal construction specializes the published actual common-Levi
continuations and the actual forward/inverse-reverse-dual comparison to fixed
compact carriers. Its source is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques*, V.3 formula (1), printed p.295 / PDF p.61. It supplies
elementary algebraic comparisons; it does not prove the analytic assertions of
V.3.1.

The carrier `compactFiber` is the tensor of the compact induction of the
original inducing object and the compact induction of its actual smooth dual.
The second factor uses the inverse of the same unramified parameter.
`dualCompactEquiv` composes the functional-preserving smooth-dual twist
identification with actual compact restriction.
`compactTensorEquiv` first inverts the published positive-Levi product tensor
equivalence and then restricts both factors. Its pure-tensor formula is proved
by cancellation of those equivalences.

The forward compact square is obtained by evaluating the already proved actual
continuation square. The reverse dual square cancels the two canonical
smooth-dual twist identifications and applies that same actual square to the
reverse continued integral. Thus both squares concern the specific continued
standard operators, rather than free families with an assumed square.

On the explicit `genericLocus` of `ActualCommonLeviTensor`, the compact reverse
inverse is the compact transport of the inverse of precisely the actual reverse
dual operator. Its two inverse identities follow from the reverse compact square
and the inverse identities of that actual operator. The `compactComparison` is
the tensor of the actual forward compact continuation and this specified compact
reverse inverse. The pure-tensor conjugacy follows from the actual generic
formula and the forward square; tensor induction proves the square on every
coefficient vector.

The continued presentations and generic bijectivity witnesses remain visible
helper inputs. There is no assertion here that their generic locus is nonempty
or dense, that it contains every unitary point, or that the individual standard
factors are regular at unitary points. Rationality from scalar composition and
the closed whole-tensor extension targets are separate units. The construction
does not alter compact probability coefficient maps, source formal degrees,
the normalized product-induced fiber, or its external rational-point action.
The field universe and representation-carrier universe remain independent.
