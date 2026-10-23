# Finite-type isolation of a cuspidal constituent on a determinant-unit Levi

Authors: Worker 319 (selected-family construction and final assembly) and
Worker 276 (intrinsic isotypic complements and finite restriction).

`Langlands.CuspidalSupport.leviCuspidalBlockIsolationTheorem` proves exactly
`LeviCuspidalBlockIsolationTheorem.{uF, uV}`. It retains every prime, actual
`PadicField`, compatible topology, natural rank including zero, block shape,
and smooth complex representations `A` and `D` in the published statement.
The field and representation-carrier universes are independent. The only
hypotheses are irreducibility and cuspidality of `D`; `A` is an arbitrary
smooth representation.

## Implemented proof

Put `N = determinantUnitSubgroup T B`, with its actual subtype topology.
The proof installs the published topological-group and Hausdorff instances
on the product Levi, and the nonarchimedean and locally compact instances
on `N`. Mathlib supplies total disconnectedness. Equip `N` with its Borel
measurable structure and a chosen left Haar measure `μ`. Compact open
subgroups are cofinal among open subgroups: apply
`Hecke.TestFunction.commonCompactOpenBiInvariance` to the empty set of test
functions and the given open subgroup.

The intrinsic complement theorem
`CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation`
then gives complementary isotypic and annihilator submodules for every
compact-coefficient class and every smooth representation of `N`. These
are actual subrepresentations, and the complement theorem applies without
an admissibility hypothesis on the ambient representation.

`FiniteRestriction.leviFiniteRestriction F T B D hD` supplies a finite
family `V : Fin m → Subrepresentation (determinantUnitRestriction T B D.representation)`
of irreducible subrepresentations whose underlying submodules span the
carrier of `D`. Its proof uses finite index after adjoining the centre,
scalar central action, and the finite-index restriction theorem; details
are in `DeterminantUnitFiniteRestriction.md` and `FiniteIndexRestriction.md`.
The final assembly uses the finite-family component of that result.

Cuspidality includes quasicuspidality. The forward direction of the exact
Harish–Chandra theorem `leviHarishChandraTheorem` therefore gives compact
smooth-dual coefficients for the restriction of `D` to `N`.

Apply `CompactCoefficientClass.finiteFamilyBlockIsolation_of_isCompl` to
`N`, `μ`, the intrinsic complements, `A`, `D`, and the finite family. This
published generic theorem constructs actual Levi-subrepresentations `S`
and `Q`. Its selected isotypic projector has complementary range and
kernel; conjugation permutes the finite family of types and makes both
subrepresentations invariant under the full Levi. Compact coefficients
and the compact-coefficient semisimplicity theorem give semisimplicity of
the restrictions of `D` and `S`. Detection of irreducible subrepresentations
in the selected range gives an actual representation equivalence to some
`V i`. The generic exclusion argument uses exact restriction of actual
subquotients and preimages of subrepresentations under quotient maps to
rule out `D` as a smooth subquotient of `Q`. These arguments are described
in `SelectedAssembly.md` and its imported helper modules.

The final line packages these conclusions with `m` and `V` in the exact
order required by the unchanged statement. All restriction constructions
agree definitionally. No theorem-valued inputs or additional witnesses
are assumed. The argument works uniformly at rank zero: both the finite
restriction and Harish–Chandra theorems cover the empty product, and the
generic assembly needs no positive-rank assumption.

## Provenance and scope

The original source is Bernstein and Zelevinsky, *Representations of the
group GL(n,F) where F is a non-Archimedean local field* (1976), registered
as `bernstein-zelevinsky-1976-representations-gln`. Lemma 3.26, p.36,
supplies finite irreducible restriction; Theorem 3.21, pp.34–35, supplies
compact smooth-dual coefficients for the cuspidal restriction; §§2.43–2.44,
p.28, supply the isotypic splitting; and the proof of Proposition 3.28,
p.36, explains invariance under the full group. The final assembly combines
the formal versions of these ingredients through their published APIs.

This proves the reduced target: the finite family spans but is not asserted
to be a direct sum or pairwise nonisomorphic. Compact-coefficient finiteness
is not finite dimensionality. The result includes explicit type coverage
and excludes `D` as a subquotient of `Q`; it does not classify other
irreducible constituents by character twists. Rank zero is the elementary
empty-product extension already included in the target.
