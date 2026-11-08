# Fixed completion and Jacquet completion

Author: Worker 1775.

This derived supporting unit assembles the abstract compatible-family argument
in David Renard, *Représentations des groupes réductifs p-adiques*, version dated
9 July 2026, VI.9.7, printed pp.205–206 / PDF pp.211–212. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The ambient group and representation carrier have independent universes. The
complex representation is smooth. The three subgroups are actual subgroups.
The following are explicit inputs: both normalizer inclusions, commutation of
the fixed element with the Levi, closedness of the Levi and the lower subgroup,
an opposite Iwahori contraction basis for one element and its inverse, covering
the lower subgroup by compact subgroups, stationarity of each compression stable
image on the basis, and bijectivity of the actual stable Jacquet map there.
No representation finiteness hypothesis is used.

`oppositeCompressionIndices_cofinal` applies the basis to the open neighborhood
given by an ambient compact open subgroup. The Levi version applies the existing
subspace-topology cofinality theorem to that same neighborhood basis. Thus no
additional cofinality hypothesis is retained.

`fixedCompletionStableEquiv` uses the previously proved equality of the
lower-fixed completion and the stable-image completion. Its two maps preserve
every component. `fixedCompletionJacquetEquiv` composes it with the previously
constructed stable-family Jacquet equivalence. The result is an actual linear
equivalence from the lower-fixed completion to the completion of the
unnormalized descended action on the upper-subgroup coinvariants.

The component at an arbitrary compact Levi subgroup is the Levi average of
the Jacquet class at any good ambient index with smaller Levi intersection.
At every ambient index having the lower–Levi–upper factorization, this equals
the Jacquet class of its ambient component. The factorization theorem uses
compact exhaustion at a smaller good index, so the target need not use the
element chosen for the basis.

Naturality is stated for an actual ambient intertwiner and two fixed
completion families related by that intertwiner on every component. Choose
a good ambient index below the target Levi index. The arbitrary-component
formula reduces naturality to the quotient map's defining formula and
commutation of compact averaging with the actual quotient intertwiner.
The second representation has its own independent carrier universe,
stationarity input, and pointwise bijectivity input.

This unit retains the structural and stabilization inputs. It supplies neither
their unconditional actual-parabolic proofs nor transport to actual Levi
rational points, normalization, or either exact parent proposition.
