# Integer multiplication and torsion on the actual conditional dual

This module constructs the group-scheme isomorphism from the kernel of the
actual dual of integer multiplication to integer torsion on the constructed
dual group scheme. Its two inclusion laws identify the same subgroup of the
dual. The construction uses the published additive dual-map interface and
retains its endpoint-specific additivity premise explicitly.

## Inputs

Let `S` be a scheme and `A`, `B` abelian schemes over `S`, all in the same
universe. The seven inputs used by the actual dual group-scheme constructors
remain explicit:

- `pullbackTensorComparisonIsIsoStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`.

At each endpoint there is an actual universal-family existence witness
`hA : HasDualScheme A` (and `hB` for the two-object scaling law). There is also
an ordinary line bundle `MA` on the universal family space
`(relativeSpace A.X.hom).obj (dualScheme A hA)`, together with a module-sheaf
isomorphism from the tensor of the Poincare family with `MA` to the structure
sheaf. These are exactly the concrete inverse and evaluation data of
`dualCommGroupSchemeFromEvaluation`. The analogous data are supplied at `B`
for the scaling law.

The additional premise for that law is
`DualSchemeMapAdditivity preservation stability A B hA hB`. It asserts
addition compatibility of the actual dual scheme maps for these fixed
endpoints. For multiplication and the kernel comparison, only the endpoint
pair `(A, A)` and its corresponding premise `additivityAA` are used. The
construction does not prove this geometric premise. All results are
conditional over arbitrary `S`; no global relative additivity theorem is
silently inferred from a field theorem.

## Scalar and multiplication laws

Write `D(f)` for `dualCommGroupSchemeMapFromEvaluation` with the displayed
inputs, and `GA` for `dualCommGroupSchemeFromEvaluation A` with the same
inputs. The morphisms in the category of commutative group schemes have the
published additive Hom-group notation.

`dualGroupSchemeMap_zsmul` proves, for every `n : ℤ` and `f : A ⟶ B`,

`D(n • f) = n • D(f)`.

The proof applies `AddMonoidHom.map_zsmul` to the existing
`dualGroupSchemeMapAddHom`, whose function is the actual Poincare pullback
map. Thus the equality concerns that map, rather than an independently
chosen additive dualization.

`dualGroupSchemeMap_multiplication` specializes this law to the identity and
uses the published dual identity law. As `multiplication A n = n • 𝟙 A`, it
gives

`D(multiplication A n) = n • 𝟙 GA`.

`dualGroupSchemeMap_multiplication_groupHom` forgets the additive wrapper
by congruence under `CommGroupScheme.groupHom`. The right side becomes the
existing `GroupScheme.multiplication GA.toGrp n`. This is equality of actual
group-object morphisms, with all integers allowed, including zero and
negative integers.

## The kernel comparison

`dualMultiplicationKernelIso` is an isomorphism in `Grp (Over S)`:

`GroupScheme.kernel (groupHom (D(multiplication A n))) ≅
  GroupScheme.torsion GA.toGrp n`.

The Library defines kernels as pullbacks of the given morphism along the
unit and defines integer torsion as the kernel of integer multiplication.
The isomorphism is `pullback.congrHom` applied to the proved multiplication
equality and reflexivity for the unit map. It therefore compares those
actual scheme-theoretic subgroup constructions.

`dualMultiplicationKernelIso_hom_ι` says that its forward map followed by
the torsion inclusion is the original kernel inclusion.
`dualMultiplicationKernelIso_inv_ι` says that its inverse followed by the
original kernel inclusion is the torsion inclusion. Both have reassociated
simplification lemmas. The first proof unfolds the pullback comparison and
uses its first-projection law; the second follows by cancellation with the
inverse isomorphism. The local transparency setting in the first proof
allows Lean to recognize the underlying pullback projection.

With `geometryA : DualSchemeGeometry A hA`, the final lemma
`dualAbelianSchemeMap_multiplication` expresses the same integer law for
`dualAbelianSchemeMapFromEvaluation` and multiplication on
`dualAbelianSchemeFromEvaluation`. The underlying Hom-group equality is the
one already proved. This specialization retains the explicit geometry
witness; it does not construct that witness.

## Provenance and scope

This is an internal algebraic consequence of the published `DualMapAdditive`,
`MultiplicationSpecialization`, `Kernel` and `Torsion` constructions. The
source convention is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter VII, Corollary (7.17), printed p.104 / PDF p.108:
dualization of abelian varieties over a field is additive and sends integer
multiplication to the same integer multiplication on the dual. Registered
source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The present conditional derivation over `S` does not extend the source's
geometric additivity theorem beyond its hypotheses. The kernel isomorphism
is the formal pullback consequence of the multiplication equality. It is
not Cartier duality of kernels and does not construct a character, finite
Weil pairing or perfectness proof. No finiteness, finite-etaleness or rank
claim is made about torsion, and this unit does not complete the Tate/PEL
task.
