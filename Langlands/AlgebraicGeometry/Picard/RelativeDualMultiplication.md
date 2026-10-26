# Relative additive dualization, multiplication and torsion

This module specializes the published conditional `DualMapAdditive` and
`DualMultiplication` constructions using the proved theorem
`Langlands.AbelianScheme.relativeDualSchemeMapAdditivity`. It removes their
endpoint additivity arguments over a quasi-separated base scheme.

## Inputs

Let `S : Scheme` have an instance of `QuasiSeparatedSpace S`, and let `A`
and `B` be abelian schemes over `S`. The seven propositions used by the
existing dual constructors remain explicit:

- `pullbackTensorComparisonIsIsoStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`.

At each endpoint, `hA : HasDualScheme A` and `hB : HasDualScheme B` supply
existence of the actual universal family. The concrete inverse data at `A`
are a line bundle `MA` on
`(relativeSpace A.X.hom).obj (dualScheme A hA)` and an isomorphism

`tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA))`.

The analogous data at `B` are `MB` and `evaluationB`. These are exactly the
inverse and evaluation inputs of `dualCommGroupSchemeFromEvaluation`;
they are not chosen homomorphisms or pairings. The multiplication and
kernel results use only the endpoint `A`.

No `DualSchemeMapAdditivity` proof is an input to this module's
declarations. The existing theorem in
`RelativeDualSchemeMapAdditivityProof` supplies it as
`relativeDualSchemeMapAdditivity preservation stability S A B hA hB`,
or its specialization to `(A, A)`. The base's quasi-separatedness
hypothesis is retained in every exported declaration.

## Additive dualization

Write `GA` and `GB` for the existing dual commutative group schemes from
the displayed data, and `D(f)` for
`dualCommGroupSchemeMapFromEvaluation ... f`. The definition
`relativeDualGroupSchemeMapAddHom` has type

`(A ⟶ B) →+ (GB ⟶ GA)`.

It is the existing `dualGroupSchemeMapAddHom` applied to the proved
relative additivity equation. The application lemma
`relativeDualGroupSchemeMapAddHom_apply` identifies its function with
`D` by reflexivity. Thus it bundles the actual Poincare pullback map.

The lemmas `relativeDualGroupSchemeMap_add` and
`relativeDualGroupSchemeMap_zsmul` give

`D(f + g) = D(f) + D(g)` and `D(n • f) = n • D(f)`.

Here `f g : A ⟶ B` and `n : ℤ`. Each proof specializes the corresponding
published conditional lemma to the same relative additivity proof.

## Multiplication and its kernel

`relativeDualGroupSchemeMap_multiplication` proves

`D(multiplication A n) = n • 𝟙 GA`.

`relativeDualGroupSchemeMap_multiplication_groupHom` gives the same
equation after forgetting the additive wrapper, with right side
`GroupScheme.multiplication GA.toGrp n`. Both statements allow every
integer, including zero and negative integers.

Let `dn` denote the actual group-object morphism underlying
`D(multiplication A n)`. The definition
`relativeDualMultiplicationKernelIso` is an isomorphism in `Grp (Over S)`:

`GroupScheme.kernel dn ≅ GroupScheme.torsion GA.toGrp n`.

It specializes `dualMultiplicationKernelIso`. That construction uses
`pullback.congrHom` to transport the actual kernel along the
multiplication equation. Torsion is the existing kernel of integer
multiplication, so both sides are the actual scheme-theoretic subgroup
constructions.

The inclusion laws are

- `relativeDualMultiplicationKernelIso_hom_ι`: the forward map followed
  by the torsion inclusion is the original kernel inclusion;
- `relativeDualMultiplicationKernelIso_inv_ι`: the inverse map followed
  by the original kernel inclusion is the torsion inclusion.

These proofs specialize the published inclusion laws, with no new
pullback choice. Both have reassociated simplification lemmas.

## Dual abelian schemes

With `geometryA : DualSchemeGeometry A hA` and
`geometryB : DualSchemeGeometry B hB`,
`relativeDualAbelianSchemeMapAddHom` bundles the same additive map
between the actual `dualAbelianSchemeFromEvaluation` objects.
`relativeDualAbelianSchemeMapAddHom_apply` identifies it by reflexivity
with `dualAbelianSchemeMapFromEvaluation`.

Using only `geometryA`, `relativeDualAbelianSchemeMap_multiplication`
says that the actual dual abelian-scheme map of `multiplication A n`
is multiplication by `n` on the constructed dual abelian scheme. This
is the same underlying group-map equality as above. The geometry
witnesses remain explicit inputs.

## Provenance and scope

This is an internal specialization of published Library constructions.
Its mathematical input is the proved relative additivity theorem; the
additive maps, scalar laws, multiplication laws, kernel comparison and
inclusion laws all come from `DualMapAdditive` and `DualMultiplication`.
No external theorem is newly imported or generalized in this module.

The specialization discharges endpoint additivity. It retains the
seven constructor propositions, actual universal-family existence,
concrete inverse/evaluation data and, for the abelian-scheme results,
dual geometry. The kernel comparison identifies two subgroup
constructions on the same dual; Cartier duality of kernels, the
intrinsic character, a finite Weil pairing and its perfectness remain
separate constructions or theorem obligations. This unit makes no
torsion finiteness or rank claim and does not complete the Tate/PEL task.
