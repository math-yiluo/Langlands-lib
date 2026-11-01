# Canonical additive associativity of original balanced tensors

Worker 691 states an intrinsic additive generalization motivated by David
Renard, French version dated 9 July 2026, I.2.2.4 and I.2.2.7 (printed
pages 15–16 / PDF21–22). The main propositions are unproved. Only elementary
evaluation pairings, balancing and biadditivity needed for the nested
published quotient lifts are constructed here.

The actual tensor is `NonUnitalModuleTensor.Tensor`. Its inherited additive
groups, pure tensors, universal additive lifts and maps are retained.
Right actions are left actions of opposite rings. `X` is a right
`R`-module, `Y` has commuting left `R` and right `S` actions, and `Z` is a
left `S`-module. No further actions, unit laws or nondegeneracy are assumed.
`LeftTensor` uses exactly `NonUnitalBimoduleTensor.rightModule X hY`;
`RightTensor` uses exactly `NonUnitalBimoduleTensor.leftModule hY Z`.
These abbreviations retain the actual quotients without transporting groups.

`forwardInner z` is `c_z(x)(y) = x ⊗ (y ⊗ z)`, balanced over `R` by the
original balancing equation and the named residual left action.
`forwardAt z` is its actual published `lift R`.
`forwardPairing` is `B(t)(z) = forwardAt z t`. Its additivity in `z` follows
by tensor extensionality from the pure-tensor formulas, and its additivity in
`t` is additivity of that lift. Its `S`-balancing is proved using the named
residual right action and the original `S`-balancing equation.
`inverseInner x` is `d_x(y)(z) = (x ⊗ y) ⊗ z`, balanced over `S`.
`inverseAt x` is its published `lift S`. `inversePairing` is
`C(x)(u) = inverseAt x u`; its `R`-balancing uses the original
`R`-balancing equation and the named residual left action.

`PureTensorFormulas` specifies the forward and inverse triple-tensor values.
`NestedLiftFormulas` identifies the complete forward map with `lift S B hB`
and the complete inverse map with `lift R C hC`.
`InverseIdentities` exposes both complete additive-map inverse identities.
`Canonical` conjoins these clauses, and `ExistsCanonical` existentially
quantifies the additive equivalence without an existence-certificate premise.
`Naturality` quantifies any two canonical witnesses and all original maps
`f`, `g`, `k`. Its two whole-map squares use exactly the published tensor
maps of `rightMap hY hY' f g` with `k`, and `f` with
`leftMap hY hY' g k`. The closed
`Langlands.Algebra.NonUnitalTensorAssociativityTheorem` asserts existence
for every original triple at both sets of carrier universes and those squares
in all three variables. The eight universes are independent; the second
existence conjunct ensures target witnesses are supplied even when their
carrier universes differ from the source universes.

The intended direct proof successor constructs the two nested lifts,
establishes their triple-tensor values and uses tensor extensionality twice
to prove the inverse identities and naturality. That principal proof is not
part of this statement unit.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 691 read the conventions at printed pages 5–7 / PDF11–13,
I.2.1 at printed page 14 / PDF20 and the entire theorem, corollary,
corollary proof and three-variable naturality remark at printed pages 15–16 /
PDF21–22. The theorem is complex-linear and uses complex unitizations;
the corollary uses nondegenerate modules over complex algebras with
idempotents and the comparison I.2.1.2. The book refers the theorem's proof
to bibliography [34], pages 97–98, which was not read here. The nested
quotient-lift route above is internal.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–2 and PDF18–19. It corrects induction adjunctions and
explains a nonunital corner action, and adds a complex vector-space
hypothesis to an older theorem. It is supplementary to the 2026 original;
these passages do not change the elementary additive construction here.

Additive associativity alone is not full coverage of I.2.2.4 or I.2.2.7.
Comparisons with actual unitized tensors and canonical coefficient
structures, and coefficient-linearity of the associator, remain parent
obligations. Extra outer actions, pentagon coherence, tensor-Hom
equivalences, exactness, categorical adjunctions and source
forgetful/induction constructions are separate units.

The companion `NonUnitalTensorAssociativityChecks` checks complete unapplied
telescopes and exact unfoldings, including complementary unequal 0/1
universe assignments. Its competing-instance checks cover both rings, all
six original carriers, all inner tensor groups and residual actions, and
all iterated groups. Its boundary checks admit subsingleton carriers and
regular integer actions, and detect nonzero left and right iterated tensors
on integer groups with zero original actions. These checks do not establish
the main existence or naturality propositions.
