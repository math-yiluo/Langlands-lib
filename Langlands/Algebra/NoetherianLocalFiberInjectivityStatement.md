# Noetherian lifting of residue-fibre injectivity

`Langlands.Algebra.NoetherianLocalFiberInjectivityStatement` states Stacks
Project, Commutative Algebra, Lemma 10.99.1, tag
[00ME](https://stacks.math.columbia.edu/tag/00ME). It defines a proposition;
it does not prove the lemma.

Let `R → S` be a local homomorphism of commutative local rings with `S`
Noetherian. Let `A` be a finite `S`-module with its restricted `R`-action,
let `B` be a flat `R`-module, and let `f : A →ₗ[R] B`. Write `m` for the
maximal ideal of `R`. If the induced map `A/mA → B/mB` is injective, then
`f` is injective and its cokernel `B/f(A)` is flat over `R`.
The source denotes `A`, `B`, and `f` by `N`, `M`, and `u`, respectively.

## Exact Lean objects and scope

`Algebra R S` specifies the ring map and
`IsLocalHom (algebraMap R S)` its locality. Both rings have `IsLocalRing`
instances, but only `S` has an `IsNoetherianRing` hypothesis.
`Module S A`, `Module R A`, and `IsScalarTower R S A` specify the
compatible actions on the finite source; `Module.Finite S A` is finiteness
over `S`. The target has only an `R`-module structure. The map `f` is
`R`-linear.

For `k = IsLocalRing.ResidueField R = R/m`, the expression
`LinearMap.lTensor k f` is the actual map
`k ⊗[R] A → k ⊗[R] B`, sending `a ⊗ x` to `a ⊗ f(x)`.
The canonical quotient-tensor identifications with `A/mA` and `B/mB`
carry this map to the source's induced quotient map. These identifications
require no flatness hypothesis. The conclusion uses the actual quotient
`B ⧸ LinearMap.range f`, where the range is an `R`-submodule with
underlying set `{f(x) | x ∈ A}`.

The universes of `R`, `S`, `A`, and `B` are independent. There is no
Noetherian hypothesis on `R`, finite-presentation hypothesis on `A`,
`S`-action or finiteness hypothesis on `B`, `S`-linearity hypothesis on
`f`, flatness hypothesis on `A`, or nonzero-module assumption.

## Source and proof boundary

The displayed statement and complete original proof were read in
`00MD.html`, Section 10.99, Lemma 10.99.1 (tag 00ME), from registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
at `literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
No source-specific registered errata note was found in the project or
current Library notes at the scope check on 25 October 2026.

The original proof first lifts injectivity modulo each power of `m`,
using flatness of the target and exact sequences for successive powers.
It then applies Krull intersection to the finite source over `S`.
For cokernel flatness, it repeats the injectivity argument after quotienting
by ideals of `R` and uses the Tor criterion for flatness. The unit ideal
case is trivial; for proper ideals these quotient rings remain local.
This describes the source's route, not a formal proof supplied by this file.
The consumer `046Y.html`, Lemma 10.128.4, uses 00ME in its final paragraph.

The explicit scalar tower, tensor presentation of the residue map, and
range-quotient presentation of the cokernel are internal translations of
the original objects. This statement claims no separate formal comparison
theorem and does not import or assume the related 00MK, 00ML, or 00MP results.
