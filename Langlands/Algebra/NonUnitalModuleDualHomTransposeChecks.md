# Dual-Hom transpose declaration checks

Worker 1151 authored this companion to the construction by Worker 1187. The
generic examples assign unapplied constants directly to complete explicit
telescope types, including every original action, scalar structure and
nondegeneracy witness. Later examples specialize the same interfaces to explicit
structure choices and zero carriers. These are derived internal interface
checks for the construction in
[NonUnitalModuleDualHomTranspose](NonUnitalModuleDualHomTranspose.md).

The mathematical source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The unnumbered lemma and displayed formula (I.4.2.1), printed p.24 / PDF p.30,
give the forward swap
`(T phi w).val v = (phi v).val w`. The reverse construction has
`(S psi v).val w = (psi w).val v`.
The conventions, canonical scalar passage and dual definitions are on printed
pp.5–7, p.14 and pp.22–23 / PDF pp.11–13, p.20 and pp.28–29.
The supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, and the current project errata were checked; the governing source
and relevant correction scope are described in the construction companion.

The checks cover the actual published dual subtypes and the following
interfaces:

- `rightDualAction`, its intrinsic nondegeneracy, its entire-functional and
  evaluation action formulas, and comparison of its recovered complex scalars
  with the inherited pointwise scalars;
- the original Hom carriers `R` and `L`, the named `rModule` and `lModule`,
  their entire-structure equalities with the published canonical Hom modules,
  and scalar formulas on target elements and included full functionals;
- `transposeFull` and `reverseFull`, their whole functions, evaluations,
  local-idempotent invariance and actual dual membership;
- `transpose` and `reverse` as original intertwiners, their full-functional
  identities and original-action intertwining;
- the linear maps `T` and `S`, their underlying additive maps and whole
  functions, and their addition, scalar and evaluation laws;
- `Rfg` and `Lfg`, their precise full original pre/postcomposites, their
  included-functional precomposition and evaluation formulas, and both
  naturality identities as equalities of entire bundled additive maps.

In the implemented construction, an original idempotent fixing `w` fixes
`transposeFull phi w`: intertwining of `phi` moves its action from `v` to the
functional, and dual evaluation then moves it to `w`. The reverse proof uses
an original right idempotent fixing `v` and its `unop` on `W`. Published
automatic complex linearity of original intertwiners, together with the
recovered/inherited dual scalar comparison, proves linearity of both full
functionals. Extensionality and the entire-functional pointwise scalar laws
prove linearity of `T` and `S`. Both naturality proofs use extensionality of
additive maps, original intertwiners and actual dual functionals; their
evaluations then agree definitionally. The companion checks specify these
implemented interfaces.

The generic naturality checks retain five independent universes for the
algebra and the four module carriers, with no inequalities. Concrete checks
use `Type 0`, `Type 1`, `Type 2`, `Type 3`, `Type 4` in that order and also
put the algebra in `Type 4` with the four carriers in `Type 0` through
`Type 3`. Separate three-universe checks test both linear maps in each
unequal algebra/carrier direction.

The competing-structure sections introduce unrelated original actions and
complex modules, then explicitly select the specified original actions and
named recovered scalar modules. They check both maps and scalar laws,
including competing complex modules on the original Hom carriers. A
four-carrier section checks the actual composition maps and both naturality
squares expressed through the additive maps underlying `T` and `S`, with all
four original actions and recovered carrier scalars selected explicitly.

The opposite-ring sections specialize to `A = Bᵐᵒᵖ`, with named original
double-opposite actions on `X`, `X'` and right actions on `Y`, `Y'`. They
select the published full-dual actions and transported right-dual actions
explicitly, and check both linear maps and both complete naturality squares.
Finally, concrete `PUnit` carriers with the original zero actions check both
linear maps when either module is zero and when the algebra and both modules
are zero. Those checks retain arbitrary carrier universes and supply
nondegeneracy using the zero idempotent.

No dimension or nontriviality condition is added. The source claims a natural
isomorphism; the construction and these checks cover the two maps and their
intrinsic laws. The inverse identities and natural linear equivalence remain
separate statement and proof successors.
