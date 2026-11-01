# Canonical fixed-part duality statements

Worker 1156 adapted Worker 6's private typing audit into this statement pair.
Worker 6 is a coauthor. The imported constructions retain their existing
Worker 1149 and Worker 1156 attribution. The declarations in namespace
`Langlands.Algebra.NonUnitalModuleDualFixedPart` are proposition definitions;
this pair supplies statement targets and does not prove them.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source assertion is the fixed-part isomorphism in I.4.1, printed page 23 /
one-based PDF page 29; the nondegenerate dual is defined on printed page 22 /
PDF page 28. Its proof uses the idempotent splitting from I.3.1, printed
page 19 / PDF page 25. The original-action conventions are on printed
pages 5–7 / PDF pages 11–13, and the canonical complex scalars are in I.2.1,
printed page 14 / PDF page 20. Worker 1156 read these passages directly.

The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2. It corrects nearby induction, bidual-injection,
duality-comparison and admissibility arguments without changing the
restriction and projection-extension maps used here. The 2026 edition
governs. The registered author-page snapshot
`renard-author-book-links-2026-10-31`, SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`,
is byte-identical to the page downloaded on 1 November 2026: its book section
links the corrected French 2026 edition and labels the separate errata as
belonging to the 2010 edition. No separate 2026 errata link occurs in that
section. No Renard-specific project erratum was found in the checked public
notes locations. These are bounded source checks.

Let `A : Type uA` have its specified `NonUnitalRing A`, `Module ℂ A`,
`IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`, and let
`hA : IsIdempotented A`. Let `M : Type uM` have its specified
`AddCommGroup M`, original `NonUnitalModule A M`, and
`hM : IsNondegenerate A M`. For naturality, independently let
`N : Type uN` have its specified `AddCommGroup N`,
`NonUnitalModule A N` and `hN : IsNondegenerate A N`.
The three universes are independent.

There is no assumed complex module on either original carrier: the full
duals and the published maps use exactly
`NondegenerateScalars.complexModule hA hM` and its counterpart for `N`.
For an actual `e : Idempotent A`, write

```text
F_M   = NonUnitalModuleCorner.FixedPart e M
R_M   = NonUnitalModuleDualFixedPartMaps.RightFixedPart hA hM e
rho_M = NonUnitalModuleDualFixedPartMaps.restriction hA hM e
eta_M = NonUnitalModuleDualFixedPartMaps.extension hA hM e.
```

The scalar modules are precisely
`NonUnitalModuleCorner.complexModule hA hM e` on `F_M` and
`NonUnitalModuleDualFixedPartMaps.rightFixedModule hA hM e` on `R_M`;
the corresponding named modules are selected for `N` as well.
The right fixed carrier is the existing fixed subtype of the existing
nondegenerate dual, with its nested full-functional subtype and original
`fullAction` and `dualAction`. Right actions are encoded as left actions
of `Aᵐᵒᵖ`, and `oppositeIdempotent e` has value `op e`.
No carrier, additive group or original algebra action is replaced.

The already published maps have the formulas

```text
rho_M(phi)(x)          = phi.val.val(x.val)
(eta_M(ell)).val.val(m) = ell(NonUnitalModuleCorner.projection e m).
```

Here projection has underlying value `e • m`, while inclusion has
underlying value `x.val`. These are restriction of the included full
functional and extension by the actual idempotent projection. They make
explicit the source's argument using functionals that vanish on
`(1-e)M`; the symbol `1` in this splitting denotes the identity operator.

`InverseIdentities hA hM e` states both equalities of entire complex-linear
maps:

```text
rho_M.comp eta_M = LinearMap.id
eta_M.comp rho_M = LinearMap.id.
```

`EquivalenceExists hA hM e` asserts the existence of
`E : R_M ≃ₗ[ℂ] Module.Dual ℂ F_M` with both specified entire maps:

```text
E.toLinearMap      = rho_M
E.symm.toLinearMap = eta_M.
```

Thus the claimed isomorphism has the canonical restriction as its forward
map and the canonical projection-extension as its inverse.

For each original `f : NonUnitalModuleHom A M N`, let
`f_e = NonUnitalModuleCorner.restrictLinear hA hM hN e f`.
`Naturality hA hM hN e f` asserts the existence of
`T : R_N →ₗ[ℂ] R_M` such that

```text
T.toAddMonoidHom =
  (NonUnitalModuleCorner.restrict (oppositeIdempotent e)
    (NonUnitalModuleDual.pullback hA hM hN f)).toAddMonoidHom

rho_M.comp T = f_e.dualMap.comp rho_N
T.comp eta_N = eta_M.comp f_e.dualMap.
```

The local instances explicitly select the published full-dual and
nondegenerate-dual right actions for both carriers. Equality of entire
additive maps identifies `T` uniquely with the restriction of the original
contravariant dual pullback, whose full functional is precomposition
with `f`. Existence of this complex-linear form is part of the conclusion.
The two squares are equalities of entire complex-linear maps under the
four named fixed-part modules.

The isomorphism itself is the source assertion. The explicit inverse
identities, specified bundled equivalence maps and whole-map naturality
are derived formulations of its canonical restriction/projection-extension
argument and the fact that original intertwiners preserve the splitting.
The named scalar modules and additive-map identification make the
formal interfaces precise.

`FixedPartDuality.{uA,uM,uN}` is the closed conjunction: for every such
`A`, `M`, `hA`, `hM` and `e`, it asserts `InverseIdentities` and
`EquivalenceExists`, and for every independently sized `N`, `hN` and
original `f`, it asserts `Naturality`. It is a convenient exact proof
target containing all three explicit assertions.

The final Lean examples check the complete unapplied interfaces of the
three predicates and the closed target. They retain independent
universes and check naturality at `(uA,uM,uN) = (0,1,2)` and `(2,1,0)`.
These examples check types and do not establish the asserted propositions.
No finite-dimensionality, admissibility, nontriviality, faithful action,
global algebra unit or additional unit-action law is assumed. Zero
algebras, zero modules and the zero idempotent are allowed, and the
original nonunital actions remain specified even when the algebra has
a global unit.

This pair does not establish the separate comparison with fixed parts in
the full dual or the original right-corner action comparison. Those
remain parent obligations with their existing owners. It also supplies no
proof of duality exactness, bidual injection, I.4.2 or I.4.3 comparisons,
or admissible reflexivity. Statement acceptance supplies targets for a
separate exact proof task after publication.
