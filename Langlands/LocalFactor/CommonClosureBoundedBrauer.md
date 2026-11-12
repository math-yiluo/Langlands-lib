# Brauer induction for local Weil representations trivial on a Weil subgroup

Author: Worker 5134. Module `Langlands.LocalFactor.CommonClosureBoundedBrauer`,
namespace `Langlands.LocalFactor.CommonClosure`. Universes: `uF` (the p-adic
field) and `uV` (extra carrier universe; carriers live in `max uF uV`).

Throughout, `F : PadicField.{uF} p` is a p-adic field, `W_F = localWeilGroup F`
is its actual local Weil group, and an `Extension F` is a finite intermediate
field `L` of the common algebraic closure `AlgebraicClosure F.Carrier / F.Carrier`
with Weil subgroup `W_L = weilSubgroup F L` (the elements of `W_F` whose Galois
projection fixes `L`).

## Definition: `inducedCharacterClassesAbove`

For a subgroup `N` of `W_F`, `inducedCharacterClassesAbove F N` is the set of
classes

```text
Ind_{W_L}^{W_F} η   in   LocalWeil.ContinuousExactGroup.{uF, max uF uV} F
```

(the exact Grothendieck group of continuous finite-dimensional complex
representations of `W_F`) where

- `L : Extension F` with `N ≤ W_L`,
- `η : W_L →ₜ* ℂˣ` is a continuous character of `W_L` with `η w = 1` for every
  `w ∈ W_L` that lies in `N`,

and the class is `ExactGrothendieckGroup.continuousInduce (weilSubgroup F L) _
(ExactGrothendieckGroup.characterClass η)`, the continuous induction of the
one-dimensional class of `η` from the open subgroup `W_L`.

## Results

- `exists_open_normal_le`: for every open subgroup `N` of finite index of
  `W_F` there is an open normal subgroup `U` of the absolute Galois group of `F`
  such that `N` contains every `w ∈ W_F` whose Galois projection lies in `U`. Proof: the permutation representation
  of `W_F` on `W_F ⧸ N` is continuous (it is trivial on the open normal core of
  `N`) and has finite image, so `localWeilGaloisTypeFor` gives a Galois
  representation `τ` realizing it; `τ` is continuous on a profinite group with a
  finite-dimensional complex target, so its kernel `U` is open
  (`Weil.open_kernel_of_continuous_nonarchimedean_representation`). If the
  projection of `w` lies in `U`, then `w` acts trivially on `W_F ⧸ N`, in
  particular it fixes the coset `N`, so `w ∈ N`.
- `exists_extension_eq`: if a subgroup `H` of `W_F` contains every `w` whose
  projection lies in an open normal subgroup `U`, then `H = W_L` for an extension
  `L` contained in the fixed field of `U`. Proof: `L` is the fixed field of the
  open subgroup `P(H) ⊔ U` (`P` the Galois projection), finite-dimensional by
  infinite Galois theory; an element of `W_F` with projection in `P(H) U` lies in
  `H` because `H` absorbs the elements with projection in `U`.
- `inflate_induce_oneDimensional_weil`: for a surjection `π : W_F → Q` onto a
  finite group with open kernel, a subgroup `S ≤ Q` with `π⁻¹(S) = W_L` and a
  character `χ` of `S`, the inflation along `π` of the virtual class
  `Ind_S^Q χ` equals `Ind_{W_L}^{W_F} η` for the continuous character
  `η = χ ∘ π|_{W_L}` of `W_L`, which is trivial on the kernel of `π`. Proof:
  `ExactGrothendieckGroup.inflate_ofClass_induce` with the identification of the
  one-dimensional representation of `χ ∘ π` with `characterLine η`.
- `ofRepresentation_mem_span_inducedCharacterClassesAbove`: let `N` be an open
  normal subgroup of finite index of `W_F`. Every continuous finite-dimensional
  representation `B` of `W_F` (carrier in `max uF uV`) that is trivial on `N`
  has exact class in the `ℤ`-span of `inducedCharacterClassesAbove F N`.

## Proof of the spanning result

`Q = W_F ⧸ N` is finite and the quotient map `π` has open kernel `N`. `B`
factors through a representation `ρ` of `Q`, and the inflation of the class of
`ρ` along `π` is the class of `B` (`ExactGrothendieckGroup.inflate_ofClass` and
`inflateEquiv`).

By the integral Brauer induction theorem for finite groups
(`FiniteRep.BrauerTheory.spanning`), the class of `ρ` is a `ℤ`-combination of
classes `Ind_S^Q χ` of monomial data `(S, χ)`. The inflation map is `ℤ`-linear,
so it suffices that each inflated generator is in the span. Take `U` from
`exists_open_normal_le` for `N`. For `(S, χ)`, `π⁻¹(S)` contains `N`, hence
every element whose projection lies in `U`; `exists_extension_eq` gives an
extension `L` with `W_L = π⁻¹(S) ⊇ N`, and `inflate_induce_oneDimensional_weil`
identifies the inflated generator with `Ind_{W_L}^{W_F} η` for a continuous `η`
trivial on the kernel `N` of `π`, an element of
`inducedCharacterClassesAbove F N`.

## Provenance

Internal. This is the standard reduction of Brauer's induction theorem for
finite groups (the Library's `FiniteRep.BrauerTheory.spanning`) to continuous
representations of the Weil group that factor through a finite quotient
`W_F ⧸ N`. The set `inducedCharacterClassesAbove` is an auxiliary set of
generators introduced for this reduction; it has no separate literature
definition.
