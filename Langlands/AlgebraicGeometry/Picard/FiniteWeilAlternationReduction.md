# Relative finite Weil alternation from multiplication isogenies

Module `Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationReduction`.
This internal construction supplies evaluation as an additive map of
dual-valued homomorphisms, together with its application to relative
alternation. The primary definition is
`Langlands.AbelianScheme.finiteWeilAlongHomEvaluationAddHom`.
The assembly theorem has type

```text
Langlands.GroupScheme.MultiplicationIsogenyStatement ->
Langlands.AbelianScheme.RelativeFiniteWeilAlternationStatement.
```

The first proposition remains an explicit premise. This contribution does
not prove the unconditional relative alternation target. It supplies the
assembly that can be applied once the general multiplication-isogeny
theorem is proved independently.

## Inputs and conventions

The reduction preserves the existing target's nine tensor/Picard
constructor propositions, quasi-separated base `S`, actual abelian
scheme `A/S`, chosen `HasDualScheme` witness, dual geometry, inverse
Poincare bundle `MA` and evaluation isomorphism, and actual homomorphism
`lam` into `dualAbelianSchemeFromEvaluation`. The polarization hypothesis
is exactly `IsPolarization`. No principal-polarization, characteristic
or invertibility restriction is introduced.

Write `e_k^lam(x,y)` for the actual `finiteWeilAlongHomValue` and
`A[k]` for `kernelCommGroupScheme (multiplication A (k : Int))`.
The value is still `beta(lam[k](y))(x)`, with the published argument
order. The root target is the actual group scheme `mu S k`; its
identity is the constant identity-section morphism.

## Implemented proof

`kernelLevelMap_transition`, in namespace `Langlands.GroupScheme.Tate`,
proves that actual torsion maps commute with divisibility transitions:

```text
f[m] ; transition_H = transition_G ; f[n].
```

It composes both sides with the monic actual kernel inclusion into `H`.
The published `kernelLevelMap_ι` and `kernelTransition_ι` reduce the
equation to `multiplication_naturality f (m/n)`.

In namespace `Langlands.AbelianScheme`,
`finiteWeilAlongHomTorsionMap_add` proves that restriction to torsion is
additive in the homomorphism. Composing with the dual torsion inclusion,
which is monic, reduces this to pointwise multiplication of the two
underlying scheme maps. The published `finiteWeilValue_mul_right` then
gives `finiteWeilAlongHomValue_add_hom`.

`finiteWeilAlongHomEvaluationAddHom n x y` bundles this evaluation as
an actual additive homomorphism

```text
(A -> DA) ->+ Additive (Hom_S(T, mu S n)).
```

It sends `lam` to `e_n^lam(x,y)`. Its addition law is the preceding
lemma. Its zero law follows by applying that law to `0 + 0` and
cancelling in the group of root-valued morphisms.
The multiplication of roots is written additively by `Additive`.
Applying `map_nsmul` to this defined additive homomorphism gives
`finiteWeilAlongHomValue_two_nsmul`:

```text
e_k^(2 lam)(x,y) = e_k^lam(x,y)^2.
```

`finiteWeilAlongHomValue_transition_incl` specializes the published
`dualTorsionCharacter_transition` to the points `x` and `lam[m](y)`.
The new torsion-map naturality identifies its transitioned second
argument. For any `n | m` and any test scheme it gives

```text
incl_n(e_n^lam(transition x, transition y))
  = incl_m(e_m^lam(x,y))^(m/n).
```

All these are equations of morphisms from the arbitrary test scheme;
none is a test only on geometric points.

`finiteWeilAlongHomValue_self_sq` applies the published
`polarizationDiagonalMumford` to the exact `IsPolarization` hypothesis.
It obtains normalization data for the actual diagonal Poincare bundle
whose Mumford map is the underlying scheme map of `2 • lam`.
The published `mumfordFiniteWeilAlternation` therefore applies to
`2 • lam`. Its diagonal equation, the pairing point formula and
the new doubling formula give

```text
e_k^lam(id_A[k], id_A[k])^2 = 1
```

for every positive `k`. In particular this is an equality of actual
morphisms from `A[k]`, including its nonreduced structure.

`finiteWeilAlongHom_diagonal_of_doubling_epi` proves the desired level
`n` diagonal identity assuming only, in addition to the original
target's data, that the actual transition
`kappa : A[2*n] -> A[n]` is an epimorphism in `Over S`.
It first cancels `kappa`, then composes with the monic root inclusion
`mu S n -> Gm S`. The transition formula at the universal point of
`A[2*n]`, with `(2*n)/n = 2` because `n > 0`, identifies this composite
with

```text
incl_(2*n)(e_(2*n)^lam(id, id))^2.
```

The inclusion is a group homomorphism, so the square-one equation at
level `2*n` makes this value the identity. The two categorical
cancellations recover the original scheme-morphism equation.

Finally,
`relativeFiniteWeilAlternation_of_multiplicationIsogeny` introduces
the original statement's binders and supplies that epimorphism with
the published `kernelDoubling_epi_of_multiplicationIsogeny`. The latter
uses the general multiplication-isogeny premise to make `[2]` flat
and surjective, identifies `kappa` as its actual pullback, and uses
faithfully flat epimorphy. Thus no finiteness or etaleness of `A[n]`
is needed for the cancellation argument.

## Provenance and remaining boundary

The provenance is internal: the new results compose the named Library
theorems and their actual kernel, Poincare, root-inclusion and
homomorphism constructions. No new external literature assertion is
introduced. The module imports the relative target and all prerequisite
modules unchanged.

The only external mathematical premise of the final assembly is
`MultiplicationIsogenyStatement`. Its proof task is
`77b25bab-7d58-4dc8-91e0-ffe9faebbceb`; this reduction does not discharge
it or add it to the unconditional target. A final exact-target
`lean.proof` submission still requires an independently published
proof of that premise, or another proved way to supply the actual
doubling epimorphism for every polarization in the target.

This unit does not prove Cartier perfectness, nondegeneracy, or any
inverse-limit assertion. It preserves the scheme-morphism diagonal
identity over all bases and in all residue characteristics,
conditionally as stated above.
