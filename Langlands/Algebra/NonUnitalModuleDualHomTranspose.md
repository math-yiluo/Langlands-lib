# Actual dual-Hom transpose maps

This module constructs the two complex-linear swap maps underlying Renard's
formula (I.4.2.1). It proves their intrinsic membership, intertwining, scalar and
naturality laws. The inverse identities and the natural linear equivalence are
reserved for separate statement and proof successors.

## Sources and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The unnumbered lemma in I.4.2, printed p.24 / PDF p.30, gives the formula

```text
phi ↦ psi,   psi(w)(v) = phi(v)(w)
```

between the original right Hom from `V` to the nondegenerate dual of `W` and
the original left Hom from `W` to the nondegenerate dual of `V`. The source
asserts a natural isomorphism and proves it using tensor-Hom comparisons.
The present construction implements the forward formula and its reverse
swap directly, without using those comparisons or asserting the isomorphism.

The original conventions and nondegeneracy definition are on printed
pp.5–7 / PDF pp.11–13. The canonical complex scalars, automatic complex
linearity of original intertwiners and pointwise Hom scalars are in I.2.1,
printed p.14 / PDF p.20. The actual nondegenerate dual and its change of
handedness are in I.4.1, printed pp.22–23 / PDF pp.28–29.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, was checked for the nearby adjunction and duality corrections.
Those pages do not change the swap formula used here. The 2026 French
edition governs. The project errata locations and relevant public source
notes were also checked; no correction to (I.4.2.1) was found there.

## Exact carriers, actions and scalars

The algebra has exactly
`[NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
[SMulCommClass ℂ A A]` and `hA : IsIdempotented A`.
The original right module `V` has its given additive group, action of
`Aᵐᵒᵖ`, and nondegeneracy witness `hV`; the original left module `W`
has its given additive group, action of `A`, and witness `hW`.
There is no assumed complex module on either original carrier. The full
duals use precisely `NondegenerateScalars.complexModule hA.op hV`
and `NondegenerateScalars.complexModule hA hW`.

All declarations are in
`Langlands.Algebra.NonUnitalModuleDualHomTranspose`. They import the
published mathematics from `NonUnitalModuleDual`,
`NonUnitalModuleDualMap`, `NonUnitalModuleDualFunctor` and
`NondegenerateModuleHomScalars`.

`R hA hV hW` is exactly
`NonUnitalModuleHom Aᵐᵒᵖ V (Dual hA hW)` with the inherited action
from `fullAction hA hW`. `L hA hV hW` is exactly
`NonUnitalModuleHom A W (Dual hA.op hV)`. Both use the actual
published dual subtypes. For `L`, the named `rightDualAction` is the
published `fromDoubleOppositeAction` applied to the inherited
double-opposite action obtained from `fullAction hA.op hV`. It keeps
the same subtype and additive structure. The transported action is selected
explicitly where needed; it is not installed as a global instance.

`rightDual_isNondegenerate` transports intrinsic nondegeneracy of this
subtype. `rightDualAction_val` identifies the entire full functional
after applying `a : A` with precomposition by the original action of
`op a` on `V`; `rightDualAction_apply` gives its evaluation.
`rightDual_canonicalModule_eq` identifies the complex module recovered
from this transported action with the inherited `dualModule hA.op hV`.
Its proof uses the published dual scalar tower, its double-opposite
transport, and uniqueness of compatible recovered scalars.
`rightDual_canonical_smul_val` and `_apply` expose the resulting
pointwise scalar formulas.

`rModule` and `lModule` are precisely the named
`NondegenerateModuleHomScalars.complexHomModule` for the two original
Hom carriers and their actual target nondegeneracy. Their `_eq` laws
retain these entire structures. Their `_smul_apply` laws use the
canonical recovered target scalars, while `_smul_val` identifies the
entire included functional with its usual pointwise scalar multiple.
No alternative complex structures on the original carriers or Hom spaces
are selected by the construction.

## Swap constructions and implemented proofs

`transposeFull hA hV hW phi w` is the full complex-linear functional
on the original `V` with value `(phi v).val w`. The theorem
`transposeFull_coe` identifies its whole function, and
`transposeFull_apply` gives evaluation. Additivity follows from
original additivity of `phi`; scalar linearity uses automatic complex
linearity of that original intertwiner and the published comparison
between recovered and inherited dual scalars.

For membership, take an original idempotent `e : A` fixing `w`.
Original right intertwining gives
`phi (op e • v) = op e • phi v`. Evaluation at `w` moves `e`
to `w`, so the swapped functional is invariant. This is
`transposeFull_fixed`; `transposeFull_mem` turns it into membership
in the actual nondegenerate dual using `mem_dual_iff` for `Aᵐᵒᵖ`.
Thus `transpose phi` is an actual original left intertwiner in `L`,
with no replacement carrier. Its additivity follows by evaluating the
linear functionals `phi v`; its original `A`-intertwining follows
by the same calculation with an arbitrary `a`.
`transpose_val`, `_apply` and `_map_smul` expose the full functional,
the source formula and original intertwining.

Conversely, `reverseFull hA hV hW psi v` is the full functional on
the original `W` given by `(psi w).val v`. Its `_coe` and `_apply`
laws retain that exact function. Automatic scalar linearity of `psi`
uses the transported target action and the comparison
`rightDual_canonical_smul_apply`. If an original right idempotent
in `Aᵐᵒᵖ` fixes `v`, its `unop` is an idempotent of `A`.
Intertwining of `psi` then fixes the full functional.
`reverseFull_fixed` and `_mem` implement this local-fixer argument.
`reverse psi` is the resulting original right intertwiner in `R`;
`reverse_val`, `_apply` and `_map_smul` expose its corresponding laws.

`T : R →ₗ[ℂ] L` and `S : L →ₗ[ℂ] R` use exactly
`rModule` and `lModule`. Their linearity proofs evaluate equality
of original intertwiners and dual subtypes; the scalar case uses the
two entire-functional pointwise scalar laws. `transposeAdd` and
`reverseAdd` bundle the same swap functions as additive maps.
`T_toAddMonoidHom` and `S_toAddMonoidHom` identify those entire
additive maps. The `_coe` and `_apply_hom` laws expose the complete
functions and original intertwiners; `_val` retains the full functional;
`T_apply` and `S_apply` are the exact swap evaluations.
The `_map_add` and `_map_smul` laws state addition and complex scalar
preservation on the original Hom carriers.

## Whole-map naturality and generality

For arbitrary original intertwiners `f : V' → V` on the right and
`g : W' → W` on the left, `Rfg` and `Lfg` are additive maps
defined by exactly

```text
Rfg(phi) = (pullback hA hW' hW g).comp (phi.comp f)
Lfg(psi) = (fromDoubleOppositeMap
             (pullback hA.op hV' hV f)).comp (psi.comp g).
```

Their `_coe` and `_apply` laws identify these whole composites,
not chosen isomorphic maps. Their `_val` laws retain the full
functional as precomposition by the published complex-linear original
map. Their `_eval` laws evaluate at `f v'` and `g w'`.
`T_natural` and `S_natural` are equalities of complete bundled
additive maps for the two squares. Their proofs use extensionality
of additive maps, original intertwiners and actual dual functionals;
both sides then reduce definitionally to the same evaluation.

The algebra and the four module carriers have independent universes
`uA`, `uV`, `uW`, `uV'`, `uW'`, with no inequalities.
There are no nontriviality, dimension, admissibility, reflexivity or
anti-involution hypotheses. In particular, zero algebras and zero
modules are allowed. The companion
`NonUnitalModuleDualHomTransposeChecks` pair checks complete unapplied
declaration types and the specified structure choices.

The explicit double-opposite specialization, local-fixer proofs,
scalar comparisons, linear/additive packaging, naturality equations
and interface checks are derived internal content implementing the
source formula. They neither use nor prove the fixed-part duality,
bidual injection, exactness, tensor-Hom comparison or general adjunction
results. Worker 1187 authored the construction; Worker 1151 contributed
the source/contract audit and companion interface checks.
