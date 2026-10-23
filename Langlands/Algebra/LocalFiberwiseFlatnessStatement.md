# Local fibrewise flatness for essentially finite type algebras

`Langlands.Algebra.LocalFiberwiseFlatnessStatement` states Stacks Project,
Commutative Algebra, Lemma 10.128.9, tag [05UV](https://stacks.math.columbia.edu/tag/05UV).
It is a universally quantified proposition definition, not a proof of the criterion.

For local rings and local homomorphisms `R → S → S'`, let `M` be an `S'`-module
and let `m` be the maximal ideal of `R`. If `S'` is essentially of finite
presentation over `R`, `S` is essentially of finite type over `R`, `M` is finitely
presented over `S'` and nonzero, `M/mM` is flat over `S/mS`, and `M` is flat over
`R`, then `S` is essentially of finite presentation over `R`, `S` is flat over
`R`, and `M` is flat over `S`.

## Correspondence with the source

The three `CommRing` and `IsLocalRing` instances express the three local rings.
The `Algebra` instances encode the homomorphisms, the two `IsLocalHom` instances
assert their locality, and `IsScalarTower R S S'` identifies the composite with
the given `R`-algebra structure on `S'`. The three module structures and their
scalar towers make the actions on `M` restrictions of the given `S'`-action.
These compatible actions are always available by restriction of scalars from
an ordinary module in the source; they do not impose a further mathematical
hypothesis. There is no assumption that either ring homomorphism is injective.

| Source hypothesis or conclusion | Lean expression |
| --- | --- |
| `R → S'` essentially of finite presentation | `EssFinitePresentation R S'` |
| `R → S` essentially of finite type | `_root_.Algebra.EssFiniteType R S` |
| `M` finitely presented over `S'` | `Module.FinitePresentation S' M` |
| `M` nonzero | `Nontrivial M` |
| `M/mM` flat over `S/mS` | The tensor-product `Module.Flat` hypothesis explained below |
| `M` flat over `R` | `Module.Flat R M` |
| `S` essentially of finite presentation over `R` | First conjunct, `EssFinitePresentation R S` |
| `S` flat over `R` | Second conjunct, `Module.Flat R S` |
| `M` flat over `S` | Third conjunct, `Module.Flat S M` |

The imported `EssFinitePresentation` predicate uses the Stacks meaning from
Definition 10.54.1, tag [00QM](https://stacks.math.columbia.edu/tag/00QM): a
localization of a finitely presented algebra. No properties of that definition
are proved here. The universes `u`, `v`, `w`, and `z` for `R`, `S`, `S'`, and `M`
are independent. No Noetherian, field, domain, or dimension assumption is added.

## Actual fibre and its module

Write `k = IsLocalRing.ResidueField R`, which is the quotient `R/m`, not an
arbitrary field. The Lean fibre ring is

`F = S ⊗[R] k`.

It has its canonical `S`-algebra structure from the first factor. The fibre
module is `F ⊗[S] M`, with its canonical `F`-module structure from the first
factor. Thus its flatness is the ordinary flatness predicate for an actual
base-changed module over an actual base-changed ring.

The standard quotient-tensor identification gives `F ≃ₐ[S] S/mS`, where `mS`
is `Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)`. In pinned Mathlib
this ring identification is
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (IsLocalRing.maximalIdeal R)`
in the reverse direction. Extension of scalars then identifies
`F ⊗[S] M` with `(S/mS) ⊗[S] M`, hence with `M/(mS)M = M/mM`.
Explicitly, `(s ⊗ r̄) ⊗ x` corresponds to the class of `(r • s) • x` in
`M/mM`. The equality `(mS)M = mM` follows from the compatible scalar actions.
The induced `S/mS` action is the usual quotient action. Equivalently, tensor
associativity identifies this module with `k ⊗[R] M`. These explanations
identify the source objects; this file introduces no abstract fibre parameter
and claims no new formal comparison theorem.

## Related criteria and proof boundary

Lemma 10.128.8, tag [00R7](https://stacks.math.columbia.edu/tag/00R7), assumes
that both `R → S` and `R → S'` are essentially of finite presentation and
concludes the two flatness assertions. The present tag 05UV weakens the
hypothesis on `R → S` to essentially finite type and additionally concludes
its essential finite presentation. The source derives it using tag 00R7 and
Lemma 10.128.4, tag 046Y.

Lemma 10.99.15, tag [00MP](https://stacks.math.columbia.edu/tag/00MP), instead
assumes all three rings Noetherian and `M` finite over `S'`, with the same
nonzero and two flatness hypotheses. It concludes the two flatness assertions
without requiring either ring map to be essentially of finite type. Over a
Noetherian ring a finite module is finitely presented, but tag 00MP is a
separate criterion with different ring hypotheses. The source proves tag 00R7
by Noetherian approximation and reduction to tag 00MP. None of these auxiliary
results, nor tag 05UV itself, is proved by this statement file.

For the scheme-level fibrewise flatness criterion, the intended specialization
is `R = O_{base,s}`, `S = O_{Y,y}`, and `S' = M = O_{X,x}`. The statement retains
the arbitrary module `M` of tag 05UV.

## Registered source

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
retained in `literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The precise locators are `05UV.html`, Lemma 10.128.9 (the statement translated
here); `07DR.html`, Definition 10.54.1 (00QM); `00R7.html`, Lemma 10.128.8; and
`00MP.html`, Lemma 10.99.15. The source's first proof sentence in `05UV.html`
says “essentially of finite presentation” where its hypothesis is essentially
of finite type; the formal statement follows the displayed lemma hypotheses,
not that proof wording. The tensor-product presentation and explicit scalar
towers are internal formalization choices implementing those hypotheses.
