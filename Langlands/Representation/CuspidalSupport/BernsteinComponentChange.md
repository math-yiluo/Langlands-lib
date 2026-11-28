# Change of cuspidal datum in a Bernstein component

For a standard family and a cuspidal datum `a`, `a.unramifiedParameter`
is the group of unramified characters of its inducing Levi.
`a.componentAlgebra` is the ring of regular functions on this character
group that are constant on associated twists. `a.componentEval χ` evaluates
such a function at the parameter `χ`.

`ComponentChangeStatement` says that inertially equivalent data give
isomorphic component rings. If twists with parameters `χ` and `ψ` are
associated, evaluating the transported function at `ψ` gives its value
at `χ`.

`componentEquiv` uses the regular-function transfer in
`ComponentWeyl.component_transfer`. To show invariance of the transferred
function, lift a parameter of the new datum to an associated parameter of
the old datum. Every parameter associated to the new one then has the same
value by transitivity of twist association. The proof composes the
conjugating Levi isomorphisms and the isomorphisms of the pulled-back
representations to establish transitivity. Transfer in the other direction
gives the inverse, since evaluation at every parameter recovers the
original value. Evaluation is pointwise on sums and products, which gives
the two ring laws.

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
of 9 July 2026, VI.7.1, describes the component as a quotient of the
unramified parameter torus and identifies components from inertially
equivalent data (printed pp. 180–181, PDF pp. 186–187). The evaluation law
expresses the resulting comparison on regular functions, with the
evaluation convention of VI.10.4, Remark 1 (printed p. 212, PDF p. 218).
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
