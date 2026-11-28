# The normalizer action on a fixed compact-open completion

Renard's VI.9.7 identifies the completed opposite Jacquet module with
the radical-fixed families in the ambient completion as a Levi module.
The Hom calculation immediately following it uses the same Levi action.
The construction applies to a subgroup \(N\) of the ambient group \(G\)
and a homomorphism \(\phi:H\to G\) whose image normalizes \(N\). For a
Levi decomposition, \(N\) is the unipotent radical and \(\phi\) is the
Levi inclusion.

`Langlands.CompactCompletion.fixedRepresentation` restricts the
completion translations along \(\phi\) to `completionFixed`. The
equation `completionFixed_eq_fixedVectors` identifies that submodule
with the fixed vectors of the completion action. Normalizer stability
then follows from
`Langlands.Jacquet.apply_mem_fixedVectors_of_mem_normalizer`. At a
compact open subgroup \(K\), the translated family has component
\(\rho(\phi(h))x_{\phi(h)^{-1}K\phi(h)}\).

`Langlands.CompactCompletion.fixedFunctor` takes smooth complex
representations of \(G\) to algebraic complex representations of \(H\).
On an intertwiner \(f\), it uses `mapFixed`, which applies \(f\) to every
component. The translation formula commutes with this map because
\(f\) intertwines the ambient action. The functorial identities are
the componentwise identities for the original intertwiners.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.9.7 and the ensuing Hom calculation,
printed pp. 205–206 (PDF pp. 211–212). Registered as
`renard-2026-representations-groupes-reductifs-padiques`.
