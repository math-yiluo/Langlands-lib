# Degree filtration of the universal enveloping algebra

Author: Worker 94. This is an internal algebraic construction from Mathlib's
actual universal enveloping algebra and submodule multiplication. No PBW
isomorphism is assumed.

For a commutative ring `R` and an `R`-Lie algebra `L`, `degreeOne R L` is
the sum of the constant submodule and the image of the canonical Lie map
into `UniversalEnvelopingAlgebra R L`. The submodule
`degreeFiltration R L d` is its `d`th power. Thus constants have degree
zero, Lie generators have degree at most one, and the constant summand
allows words of shorter length in each positive degree.

The filtration is monotone. Multiplying pieces of indices `p` and `q`
gives exactly the piece of index `p+q`. `degreeFiltrationLT` is the
supremum of pieces with strictly smaller index; together they form an
`IsRingFiltration`.

`exists_mem_degreeFiltration` proves exhaustivity by lifting an element
through the actual quotient map from the tensor algebra and using tensor
algebra induction. Scalars and generators supply the initial cases;
multiplication adds indices and addition takes their maximum.
`iSup_degreeFiltration` states the resulting supremum is the whole
enveloping algebra.

`commutator_mem_degreeOne` reduces a pair of degree-one elements to
scalars plus canonical Lie generators. Scalars commute and the defining
enveloping relation expresses the remaining commutator as a Lie generator.
`commutator_degreeOne_mem` then uses induction on products and the identity
`[a,xy] = [a,x]y + x[a,y]`. A second product induction, using
`[xy,b] = x[y,b] + [x,b]y`, proves the positive-index bound in
`commutator_mem_degreeFiltration_succ`. The general theorem
`commutator_mem_degreeFiltration` places the commutator of pieces `p` and
`q` in piece `p+q-1`, with natural-number subtraction. If the second index
is zero, its elements are scalars, so the commutator is zero. These
arguments work over an arbitrary commutative coefficient ring.

If `L` is finite as an `R`-module, `degreeOne_fg` proves finite generation
of the sum of constants and the generator image. `degreeFiltration_fg`
uses finite generation of powers under submodule multiplication, and
`degreeFiltration_finite` gives finite `R`-module structures on all pieces.
No finite-dimensionality assertion for the entire enveloping algebra,
PBW, symmetrization, central generation or automorphic growth follows
from this construction alone.
