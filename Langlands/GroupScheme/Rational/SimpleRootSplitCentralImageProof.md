# Integral simple-root annihilators and split components: proof

`Langlands.GroupScheme.simpleRootSplitCentralImage` proves exactly
`Langlands.GroupScheme.SimpleRootSplitCentralImageStatement.{u}`. Over every
field `k : Type u`, it identifies the common integral annihilator of the
simple relative roots with the integral cocharacter image of any actual
split component along the supplied compatible morphism to the chosen
maximal split torus. The ambient group is connected reductive, and the
cocharacter defining positivity is generic. The statement retains arbitrary
characteristic, non-split groups, nonreduced relative roots and rank zero.

For the first inclusion, the proof rewrites the split-component image as
`centralCocharacters i` using
`IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`.
The affine and monomorphism hypotheses come from connected reductivity and
the maximal split torus. For a cocharacter annihilating all simple roots,
evaluation in the character variable is the additive map obtained from
`(latticePairing T).flip`. Its kernel contains the simple roots and therefore
their additive subgroup closure. The theorem
`relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots`, applied to
genericity and `relativeRootNegation`, puts every relative root in that
closure. Thus the cocharacter annihilates every actual relative root, and
`rootAnnihilatorCentrality` gives centrality on every test scheme. This
proves membership in the integral image.

For the reverse inclusion, the split component is a central split torus.
The equation `CommGroupScheme.groupHom f ≫ i = a` transports its centrality
to the composite through the maximal split torus.
`root_restrict_eq_zero_of_isCentral` makes every actual relative root zero
after restriction along `f`. For any cocharacter of the split component,
associativity of composition and the zero-composition law then make its
integer pairing with every simple root zero. The proof concludes by
antisymmetry of the two integral submodules.

The original motivation is Renard's French edition dated 9 July 2026,
V.3.23–V.3.24, printed p.117 / PDF p.123, together with V.2.5, printed
p.107 / PDF p.113 and V.3.7, printed p.111 / PDF p.117. The source is
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is the internal integral comparison described in the statement
Markdown; the implemented proof composes existing general group-scheme
theorems. It preserves the universe parameter and all premises of the
published statement. Existence of the compatible morphism, uniformizer
quotients and the nonnegative monoid are separate questions.
