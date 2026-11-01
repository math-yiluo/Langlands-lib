# Right exactness of the actual regular-carrier induction P

`Langlands.Algebra.NondegeneratePInductionRightExactness.sequenceRightExact`
proves the full `Langlands.Renard.SequenceRightExact` predicate for the published
`NondegenerateTensorFunctor.P`. Its ring universes `uA`, `uB` and source carrier
universe `v` are independent. It uses exactly the named abelian structures
`NondegenerateModuleCat.abelian A hA` at carrier `v` and
`NondegenerateModuleCat.abelian B hB` at carrier `max uB v`.

The inputs are idempotented nonunital rings A and B, the specified right A-action
on the actual additive carrier B, its commutation with the regular left B-action,
and the specified nondegenerate B–A bimodule hypothesis. The functor's object
carrier is exactly `Tensor A B M.obj`; its maps are the published tensor maps.
There is no left A-action on B or ring homomorphism among the inputs. Zero rings
and trivial modules are allowed.

## Source and internal scope

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exactness assertion is the unnumbered theorem of I.2.4, printed pp.18–19 /
PDF24–25. The tensor-Hom formulas and actual induction constructions are
I.2.2–I.2.3, printed pp.15–18 / PDF21–24. The sequence convention is A.VIII.1,
printed p.266 / PDF272. These passages were read for this work.

The supplementary earlier-edition corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked at PDF1–2 and PDF18–19. PDF1 confirms P left adjoint to pseudo-F,
as already stated in the governing 2026 edition; PDF18 corrects Hom map order,
and PDF18–19 retain a separate coefficient/unitization warning. The proof here
uses the original additive curry and uncurry maps, rather than a categorical
adjunction between categories at a common carrier universe.

This is an internal arbitrary-ring additive generalization of the P assertion
in Renard's complex-algebra setting. Coefficient actions, complex-linearity,
scalar restriction and agreement with the source's complex unitizations remain
separate obligations. The module supplies an intrinsic helper for the closed
P/pseudo-F exactness target; it makes no assertion about the other induction
family or injectivity preservation.

## Implemented proof

Let `S` be any short complex of nondegenerate A-modules with `S.Exact` and
`Epi S.g`. The accepted inclusion-exactness theorem carries exactness to the
original nonunital module category. Its published concrete criterion gives
`range S.f.hom = kernel S.g.hom`. For the boundary, exactness of that inclusion
preserves epimorphisms; the published integer-unitization equivalence and
Mathlib's module epi criterion show that the original additive map `S.g.hom`
is surjective. This step reuses the existing equivalence and defines no new
unitization comparison.

For an arbitrary nondegenerate B-module N at carrier `max uB v`, suppose
`φ : P(S.X₂) → N` kills `P(S.f)`. The published
`NonUnitalTensorHomAdjunction.Left.curry` sends φ to the original A-linear map
from `S.X₂` to `NonUnitalModuleHom B B N.obj`, with exactly the source action
`(a • h)(b) = h(op a • b)`. Evaluating the assumed zero composite on pure tensors
shows that this curried map vanishes on the range of `S.f.hom`, hence on the
kernel of `S.g.hom`.

`AddMonoidHom.liftOfSurjective` descends this additive map through the original
surjection. Checking the A-linear law on preimages makes the descent an
original A-intertwiner out of `S.X₃`; no categorical carrier enlargement of the
A-module is needed. The published `Left.uncurry` then produces the required
original B-linear morphism `P(S.X₃) → N`.

The additive descent identity and `NonUnitalModuleTensor.hom_ext` prove the
factorization on the entire tensor quotient. Surjectivity of `S.g.hom` and the
same pure-tensor extensionality prove uniqueness. Thus `P(S.g)` is a cokernel
of `P(S.f)`, via `CokernelCofork.IsColimit.ofπ`. Mathlib's
`ShortComplex.exact_and_epi_g_iff_g_is_cokernel` gives both exactness of the
mapped short complex and its boundary epimorphism. This applies to every
one-sided right exact sequence, as required by `SequenceRightExact`.

All imported Library declarations are unchanged. The proof uses only the
standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`.
