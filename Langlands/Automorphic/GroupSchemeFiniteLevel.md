# Finite-place regularity for actual group-scheme functions

Let `F` be an arbitrary number field and `G` an affine group scheme over
`Spec F`. The functions are the existing `ContinuousRationalFunctions F G`:
continuous complex-valued functions on the actual group `G(A_F)` invariant
under the actual rational left action. The topology is the existing topology
defined by evaluation of global functions on the scheme. All finite groups
below are `FiniteAdelicGroupPoints F G`, with that topology over the original
finite adele ring. No reductivity, connectedness or splitting assumption is
needed for this construction.

`evaluate` evaluates such a function, and `finiteSlice a` is the complex-linear
restriction `b ↦ f(pair a b)` for a fixed actual infinite point `a`.
`finiteLocallyConstantSubrepresentation` consists of functions for which every
finite slice is locally constant. Addition and scalar multiplication preserve
this property. Full adelic right translation preserves it because translating
`pair a b` by `g` gives
`pair (a * infinite g) (b * finite g)`, and right multiplication on the finite
factor is continuous.

`finiteRightAction` is the actual right action restricted along `ofFinite`.
`finiteSmoothSubrepresentation` is its submodule of vectors having one common
open finite stabilizer, using `Langlands.smoothVectors`. Full adelic translation
preserves this submodule: for a translated vector the fixing subgroup is the
inverse image of the original fixing subgroup under conjugation by the inverse
finite component of the translating point. The proof uses the actual
`finite_conjugation` identity and the representation law. An open stabilizer
also makes each finite slice locally constant, by constancy on the open coset
`bL`. This gives `finiteSmooth_le_finiteLocallyConstant`, the restricted full
action `finiteSmoothRightAction`, and the equivariant linear inclusion
`finiteSmoothLocallyConstantInclusion`. No converse between slice-wise local
constancy and a common open stabilizer is asserted.

`levelSubmodule L` imposes right invariance under a specified finite subgroup
`L`. `HasFiniteLevel` requires some such subgroup whose underlying subset is
both compact and open. Finite level gives a common open stabilizer. Conversely,
given an explicitly supplied compact open subgroup `C`, a common open
stabilizer `L` can be replaced by `C ∩ L`: it is open, compact because `L` is
closed, and still fixes the function. The construction does not prove or
assume the existence of `C`.

## General-linear comparison

For every natural rank `n`, including zero, the comparison uses the actual
group scheme `GeneralLinear.groupScheme (Fin n) F` and the original matrix
function spaces. It restricts `continuousGeneralLinearEquiv` from
`Langlands.Automorphic.GroupSchemeAmbient`; it does not replace those spaces.
Evaluation at corresponding adelic points agrees. The actual pairing
comparison identifies each finite slice after applying the original infinite
and finite multiplicative homeomorphisms.

`continuousGeneralLinearEquiv_mem_finiteLocallyConstant` preserves and reflects
local constancy by composition with the finite homeomorphism and its inverse,
using surjectivity of the infinite homeomorphism. It yields
`finiteLocallyConstantGeneralLinearEquiv`. The finite right actions intertwine
by the existing comparison for `ofFinite`. Inverse images of open stabilizers
under the finite homeomorphism and its inverse then prove
`continuousGeneralLinearEquiv_mem_finiteSmooth` and
`finiteSmoothGeneralLinearEquiv`. Both linear equivalences intertwine the
restricted **full** adelic right actions with the original matrix actions.
The target common-stabilizer space is precisely
`Langlands.Automorphic.finiteSmoothSubrepresentation`; no infinite smoothness
condition is added to either side.

For a specified matrix subgroup `L`, the corresponding actual subgroup is its
inverse image under `finiteHomeomorph`. Fixed-vector membership agrees, giving
`levelGeneralLinearEquiv`. Finally,
`continuousGeneralLinearEquiv_hasFiniteLevel` preserves and reflects
`HasFiniteLevel`: inverse images under the finite homeomorphism and its inverse
preserve openness and compactness, and the finite-action identity preserves
invariance. This proves agreement with the original compact open level
predicate, without relying on existence of any particular level.

## Provenance and scope

This is a derived construction from the actual product decomposition in
`Langlands.Global.AdelicGroupProduct`, the continuous ambient comparison in
`Langlands.Automorphic.GroupSchemeAmbient`, and the finite-place constructions
in `Langlands.Automorphic.Smooth` and `Langlands.Automorphic.Ambient`. The
proofs adapt their direct submodule, open-coset, conjugation and compact
intersection arguments to the existing affine-point groups. The general-linear
comparisons are consequences of the published point homeomorphisms and their
pairing and inclusion identities. No new external structure theorem is invoked.

These are finite-place conditions on ambient rational-invariant functions.
They do not construct an archimedean differentiable structure, assert infinite
smoothness, impose a central character or growth condition, or supply the
split-centre quotient, reduction theory, finite volume, constant terms or
cuspidal realizations. Those remain separate obligations of the general
reductive program.
