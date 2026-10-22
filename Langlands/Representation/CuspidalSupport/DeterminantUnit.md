# Determinant-unit subgroup and smooth restriction

Author: Worker 180. This definition pair belongs to task
`555ebffe-477f-496f-9019-754864be425e`, revision 1.

For every prime `p`, actual p-adic field `F : PadicField p`, compatible
`T : F.TopologicalData`, total rank `n`, and ordered `B : BlockShape n`,
`Langlands.CuspidalSupport.determinantUnitSubgroup T B` is the actual subgroup
of `B.Levi F.Carrier` consisting of tuples of invertible matrices whose
residue-normalized determinant absolute values equal one in every block.
The rank is any natural number, including zero: an empty product imposes no
conditions. The field universe `uF` and representation carrier universes
`uV`, `uW`, and `uX` are independent. Representations have complex coefficients
and need neither a topology on their carrier nor finite dimension.

The declarations in `Langlands.CuspidalSupport` have these roles:

- `leviDeterminantNorm T B` is the tuple of the accepted characters
  `T.determinantNorm (B.size i)`. Its coordinate formula is proved by reflexivity.
- `determinantUnitSubgroup T B` is its kernel. The membership lemmas
  `mem_determinantUnitSubgroup` and
  `mem_determinantUnitSubgroup_iff_normalizedAbs` identify membership with,
  respectively, equality of each unit-valued character to one and the equation
  `T.normalizedAbs (GeneralLinear.determinant (g i)) = 1` in each block.
- `determinantUnitSubgroup_normal` supplies normality by the general kernel
  theorem. `determinantUnitSubgroup_eq` proves independence from the supplied
  compatible realization, using equality of the determinant characters.
- `determinantUnitInclusion` is the actual subgroup inclusion into the product
  Levi, with its value equation and injectivity proved.
- `isOpen_determinantUnitSubgroup` proves openness by expressing the subgroup
  as the finite intersection of coordinate preimages of the open kernels
  `T.isOpen_ker_determinantNorm`. `determinantUnitOpenSubgroup` packages this
  same subgroup with that proof. The inclusion is continuous for the subgroup
  topology. All topology-dependent declarations explicitly install
  `T.topology`; the Levi has the induced product of matrix-unit topologies.
- `determinantUnitRestriction` composes the original action with inclusion,
  keeping the exact carrier and giving the equation `ρ|G°(g)(v) = ρ(g.val)(v)`.
  `determinantUnitRestrictionMap` retains the original linear map. Its value,
  identity, and composition equations are proved by reflexivity.
- `isSmooth_determinantUnitRestriction` follows from the accepted continuous
  pullback theorem `Langlands.isSmooth_comp`.
  `determinantUnitRestrictionFunctor` bundles these objects and maps as the
  actual functor between smooth complex representation categories, with
  identity and composition laws proved by reflexivity.

The original source is Bernstein and Zelevinsky (1976), Chapter II, section
3.20, printed page 34. It defines `G°` as the product of the subgroups whose
determinants belong to the units of the valuation ring, and states normality
and openness. The norm-one condition here expresses this determinant-unit
condition using the accepted residue-normalized absolute value. In particular,
this is a condition on every block separately, rather than only on the product
of their determinants. The accepted normalized character and its open-kernel
proof are reused, with no arbitrary valuation introduced.

Source ID: `bernstein-zelevinsky-1976-representations-gln`. SHA256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The registered original PDF is *Representations of the group GL(n,F) where F is
a non-Archimedean local field*, Russian Mathematical Surveys 31:3 (1976),
1–68, English translation. Printed pages 34–37 were read, including sections
3.26, 3.28, and 3.30. Those later results motivate this interface but are not
asserted or assumed here. The extension to rank zero and categorical packaging
are internal constructions from the imported definitions. This pair claims no
Harish-Chandra compact-support equivalence, semisimplicity, finite-index center
enlargement, isotypic splitting, or constituent splitting.

Project dependencies are the accepted modules
`Langlands.Group.GL.Blocks`, `Langlands.Group.GL.NormalizedCharacter`,
`Langlands.Representation.Category.Basic`, and
`Langlands.Representation.Smooth.Transfer.PullbackProof`. Their implementations
are imported by Lean name and unchanged. The Mathlib ingredients used directly
are kernels and their normality, finite intersections of open sets, continuity
of product projections and subtype inclusion, and actual representation
intertwiners. The environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
