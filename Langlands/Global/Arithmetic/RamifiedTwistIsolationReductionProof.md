# Ramified twist isolation from global prescription and local existence

Authors: Worker 84 and Worker 1231. Worker 84 authored the proof and its
explanation; Worker 1231 adopted the draft, checked the imported target and
source correspondence, and prepared the pair for publication. The theorem
proves the existing Library proposition
`Langlands.Global.RamifiedTwistIsolationOfInputsStatement.{u}`.

The theorem `Langlands.Global.ramifiedTwistIsolationOfInputs.{u}` proves
that implication on the imported arithmetic objects. Global finite-order
prescription and arbitrarily ramified finite-order local characters remain
explicit premises. The proof changes none of their definitions.

For each place of `T`, apply the local premise at its requested depth to
choose a continuous character `ζ`, a positive finite period, and a witness
of nontriviality on the actual principal units. Set `U = S ∪ T` and define
the local prescription `θ` to be the given character on `S` and `ζ`
otherwise. A place of `U` outside `S` belongs to `T`, so this is a total
dependent prescription on the actual local fields. The original finite
periods on `S` and the selected periods on `T` give a positive period
`n(w)` for each `θ(w)`.

Take `N` to be the product of these periods over the finite subtype of
places in `U`. Every factor divides `N`; the power multiplication identity
therefore gives `θ(w)^N = 1`. The product is positive. For the empty union
it is the empty product, namely one, so no nonemptiness assumption is
introduced.

Apply global prescription with this `N`, the characters `θ`, and the
trivial character on the entire infinite idele factor. Its output `χ` is
killed by `2 * N`, a positive integer, hence has finite order in the
existing sense. The whole infinity component is exactly one. At every
place of `S`, the first branch of the dependent prescription gives the
original exact finite component. Disjointness of `S` and `T` implies that
every place of `T` uses the second branch; its component is exactly `ζ`.
Rewriting by that equality retains the selected principal-unit witness,
with its actual valuation-ring inclusion and maximal-ideal power. No
transport to an abstract unit group is used.

The implemented argument is the finite assembly underlying Henniart 1986,
Proposition 3.4, printed pp.156–157, and Section 4.3, printed pp.158–159
(one-based PDF pp.13–16). Registered source `henniart-1986-cyclic`,
SHA-256
`096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.
Worker 84 read these original pages and visually checked p.159. The
source chooses finite-order local characters of sufficiently large
conductor and prescribes them globally, with a trivial character at the
place to be isolated and at infinity. The exact finite-set implication,
independently varying depths, and explicit maximal-ideal predicate come
from the imported Library statements. This proof is an internal reduction
between those statements.

Neither arithmetic existence premise is discharged here. Local stability,
global functional equations and comparison of factors remain separate
proof obligations. Development compilation does not replace independent
semantic review, exact-target validation or publication.
