# Constructions on actual local parameters

Author: Worker 53. This definition contribution applies Worker 17's generic
parameter operations to the actual local group, inertia and norm character.
It imports `Langlands.Weil.Local.Parameters` (published at Library commit
`22b4f024e0d4218752e970d09329d1799f6d81d1`) and Worker 17's `Langlands.WeilDeligne.ParameterOperations`
and `Langlands.WeilDeligne.Invariants` (published at Library commit
`0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`). The environment is Lean 4.34.0
with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The constructions hold for every prime `p` and every algebraic
`F : PadicField.{u} p`, with independently chosen vector-space universes. They
use the actual local inertia and norm character of `Assembly`. No inertia
subgroup, comparison equivalence, Frobenius lift or residue cardinality is
supplied as an extra hypothesis.

## Certificates proved here

`localNormCharacter_on_inertia` proves that the actual norm is trivial on
actual inertia. This follows from the published degree-character formula,
because inertia is the kernel of the degree. It is the input that the generic
invariant-pair and special-block constructions need.
`localUnramifiedCharacter_inertiaKernel_isOpen` proves that every actual
unramified character contains all of inertia in its kernel, so the kernel on
inertia is all of inertia and hence open.

## Operations on parameter objects

- `localParameterSum`, `localParameterTensor`, `localParameterDual` and
  `localParameterDeterminant` specialize the generic constructions. Tensor
  monodromy is `N ⊗ 1 + 1 ⊗ N'`, dual monodromy is the negative transpose, and
  determinant monodromy is zero. Each result carries the generic proof of open
  inertia kernel.
- `localParameterTwist χ hχ` twists by a character `χ` of the local Weil group.
  It keeps the explicit hypothesis `hχ` that `χ` has open kernel on inertia,
  which the generic twist needs. No claim is made about arbitrary characters
  that are continuous for the usual topology.
- `localParameterUnramifiedTwist z` twists by the actual unramified character
  with value `z` at geometric Frobenius. It needs no further hypothesis, by the
  certificate above.
- `localParameterKernel` is the actual Weil representation on `ker N`, and
  `localParameterInertiaKernel` the one on `(ker N)^I`. Both carry open inertia
  kernel.
- `localParameterInvariants` is the full pair on `V^I` with the restricted
  monodromy, which may be nonzero. It uses normality of actual inertia and the
  norm certificate above.

## Special blocks

`localSpecialBlock F m` is the uncentered block on `Fin m → ℂ`. The local Weil
group acts on coordinate `j` by `ν^j`, for `j = 0, ..., m - 1`, where `ν` is
the actual norm character. The monodromy sends basis vector `e_j` to
`e_(j+1)` and the last one to zero. Its rank is `m` (`localSpecialBlock_rank`).
For `m = n + 1` the monodromy kernel is the line of the top basis vector
(`localSpecialBlock_kernel`). For `m = n + 2` the monodromy is nonzero
(`localSpecialBlock_monodromy_ne_zero`), so the local parameter objects include
pairs with nonzero monodromy. `localBlock A m` is the tensor product of the
zero-monodromy pair of an open-inertia Weil representation `A` with the special
block of rank `m`. It is a constructor for given block data; it does not choose
a decomposition or a Frobenius semisimplification.

## Operations on classes

`localParameterSumClass`, `localParameterTensorClass`,
`localParameterDualClass`, `localParameterTwistClass`,
`localParameterUnramifiedTwistClass`, `localParameterDeterminantClass` and
`localParameterInvariantsClass` act on genuine local parameter classes.
`localParameterKernelClass` and `localParameterInertiaKernelClass` send them to
genuine classes of open-inertia Weil representations. All reuse the generic
descent through linear isomorphisms of pairs; no representative is chosen.

## Source correspondence

Tate, *Number theoretic background* (1979). Example (4.1.4) defines `Sp(n)`
with `ρ(w) e_i = ‖w‖^i e_i` and `N e_i = e_(i+1)`; this is the uncentered
special block above. Paragraph (4.1.5) states that `ker N` is stable under the
Weil group and gives the tensor rule `(ρ, N) ⊗ (ρ', N') = (ρ ⊗ ρ', N ⊗ 1 + 1 ⊗ N')`. Paragraph
(4.1.6) uses `V_N = (ker N)^I`. These passages are on printed page 20 (PDF
page 29) of the retained Corvallis Part II volume and were read directly.
Literature ID: `tate-1979-number-theoretic-background`; PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The normalization of the norm character and the geometric degree is
documented in `Assembly.md` and `Parameters.md`. The generic constructions and
their proofs are Worker 17's, documented in `WeilDeligne/ParameterOperations.md`,
`WeilDeligne/Invariants.md` and `WeilDeligne/SpecialBlocks.md`. This module is
derived local specialization and proves no classification theorem.
Restriction and induction along finite extensions are not part of it; they use
the local Weil map of `ExtensionWeil`.
