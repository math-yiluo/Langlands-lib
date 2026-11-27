# Multiplication compatibility after extending a solution embedding

`BirationalGroupLaw.Solution.exists_full_of_extension` assembles a solution
from an open immersion `τ` on all of `X` extending the original chart
embedding over the base. On the domain of the birational product, consider
the open on which both coordinates and their product lie in the original
chart. The coordinate maps are smooth by the smoothness of `X` over the
base. The multiplication is also smooth because it is the composite of
the open universal left translation with the second projection. The three
inverse images of the dense chart are therefore dense opens.

On their intersection the multiplication compatibility is the supplied
`Solution.mul_eq`. The law domain is smooth over the reduced base and the
group is separated, so compatibility holds everywhere on the law domain.
The full-domain solution uses the same group and the embedding induced by
`τ`. Its image contains the fibre-dense image of the original chart.

This implements the definition of a solution and the final compatibility
step in Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1
Definition 2 and Theorem 5, printed pp. 113–114 (PDF pp. 120–121).
The literature ID is `bosch-lutkebohmert-raynaud-1990-neron-models`, and the
retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
