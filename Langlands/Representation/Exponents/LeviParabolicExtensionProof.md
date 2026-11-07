# Actual extension from the original rational Levi

This proof targets the unchanged proposition
`Langlands.Aubert.General.RepresentedParabolic.LeviParabolicExtensionStatement`.
It retains the arbitrary field universe, every supplied map and decomposition,
and the exact original inner Levi scheme `N`.

Let `tP : P → M` be the retraction constructed from the supplied multiplication
isomorphism `M × U → P`. Define `R = P ×_M Q`, with inclusion `i : R → P`,
projection `t : R → Q`, and the canonical section of `t` induced by `Q → M → P`.
Define `W = R ×_Q V`; its inclusion `rR : W → R` is the actual inverse image
of the supplied inner radical. The new Levi map is the original `N → Q`
followed by that canonical section.

The outer radical gives a smooth geometrically connected retraction. The inner
retraction similarly proves that `Q` is connected. Pullback then makes `R`
smooth, connected and affine, and makes `t` smooth and surjective. The full
kernel of `t` is represented by the original `U`, as an equality of subgroup
functors on every relative test scheme. Transfer through this representative
proves that the actual kernel is smooth, connected and unipotent.

The preimage-radical theorem proves that `W → R` is the geometric unipotent
radical, both over the ground field and over its algebraic closure. The generic
preimage multiplication theorem lifts the supplied decomposition `N × V → Q`
to `N × W → R`, using the exact original map `N → Q`. Closedness of `N → R`
follows by its composite into `P`; the same original `N` is connected reductive.
These facts give the rational Levi predicate.

Ambient parabolicity is supplied by `LeviPreimage.isParabolicSubgroup_ambient`.
That helper pulls a geometric Borel back through the supplied Levi retraction,
proves maximality by taking images of solvable overgroups, and promotes the
resulting Borel from `P` to the original ambient group.

The section identity gives the exact original composite equality. The actual
factorization through `P` gives containment. The pullback and retraction give
the exact intersection with the original `M` on every test scheme, including
nonreduced tests. No rational-point replacement or structural-existence premise
is used.

This is a derived proof using the existing Library interfaces. The statement's
geometric provenance remains the Borel–Tits packaging recorded in its unchanged
Markdown; the proof here follows the actual retraction and inverse-image route
described above. Worker 1452 assembled the extension and its parabolic geometry;
Worker 74 supplied the preimage-radical and original-Levi multiplication helpers.
