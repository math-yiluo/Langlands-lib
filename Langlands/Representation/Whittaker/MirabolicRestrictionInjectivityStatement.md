# Injectivity of restriction to the mirabolic subgroup

Author: Worker 5032. This module defines one proposition,
`Langlands.Whittaker.MirabolicRestrictionInjectivityStatement` (universes `uF`,
`uV`). It is a statement only: nothing here proves it, and no declaration assumes
it.

## Statement

For every field `F : Type uF` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and Mathlib's `IsNonarchimedeanLocalField F`, every
`n : ℕ`, every `ψ : UnitaryAdditiveCharacter F` (a continuous nontrivial
unitary additive character), every complex vector space `V : Type uV` and every
representation `π : Representation ℂ (GeneralLinear (n + 1) F) V` with
`IsGeneric ψ n π`, and every `ℓ : glFunctionals ψ n π` with `ℓ.val ≠ 0`, the
linear map

```
v ↦ (p ↦ ℓ.val (π p.val v)),   V → (mirabolic n F → ℂ)
```

is injective.

- `GeneralLinear (n + 1) F` is the actual matrix group `GL_(n+1)(F)`; positive
  rank is written `n + 1`, so rank one (`n = 0`) is included.
- `mirabolic n F` is the published subgroup of invertible matrices whose last
  row is `(0, …, 0, 1)`. This is the group `P` (`P_r`) of Jacquet–Shalika.
- `glFunctionals ψ n π` is the published space of linear forms `λ` on `V` with
  `λ(π(u)v) = θ(u) λ(v)` for every upper unitriangular `u`, where
  `θ(u) = ψ(Σ_i u_(i,i+1))` is `standardCharacter ψ n`. This is condition (1) of
  Jacquet–Shalika (1.1) with their character `θ` of (10) on printed page 504.
- `IsGeneric ψ n π` is the published conjunction of irreducibility
  (`Representation.IsIrreducible π`), admissibility (`IsAdmissible π`, which
  includes smoothness for the topology of `GL_(n+1)(F)` induced by `F`, and
  finite-dimensional fixed spaces for every open subgroup) and the existence of a
  nonzero functional in `glFunctionals ψ n π`.

The field is an arbitrary nonarchimedean local field, so positive
characteristic is included; there is no restriction to `PadicField`. The
carrier universe `uV` is independent of the field universe `uF`.

### Equivalent forms

Because the map is linear in `v`, injectivity is equivalent to: if
`ℓ.val (π p v) = 0` for every `p ∈ mirabolic n F`, then `v = 0`.

The published coefficient model `coefficientModel π ℓ` (here also
`glCoefficientModel ψ n π ℓ`) consists of the functions
`W_v(g) = ℓ.val (π g v)` on `GL_(n+1)(F)`, and `modelMap π ℓ : v ↦ W_v` maps
`V` onto it. The statement's function is exactly the restriction `W_v|P`. Under
the hypotheses, `modelMap π ℓ` is also injective: its kernel is a
`π`-invariant subspace, it is not all of `V` because `ℓ ≠ 0`, so it is zero by
irreducibility (this is the published `glModelEquiv`). Hence the statement is
equivalent to: the restriction map `W ↦ W|P` from `coefficientModel π ℓ` to
functions on `mirabolic n F` is injective, that is, a vector of the
coefficient model that vanishes on the mirabolic subgroup is zero.

In rank one the mirabolic subgroup is trivial, and the statement says that
`ℓ.val` is injective on `V`, so `V` has dimension at most one.

## Source correspondence

H. Jacquet and J. A. Shalika, *On Euler products and the classification of
automorphic forms I*, Amer. J. Math. 103 (1981), 499–558. Registered source
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
file
`/home/taskhub/pilot/literature/Jacquet-Shalika, On Euler products and the classification of automorphic forms I, Amer. J. Math. 103 (1981), 499-558.pdf`,
SHA-256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`.

- Section 1 (printed page 504, PDF page 6): "In this section `F` is a
  non-archimedean local field." No characteristic restriction is made.
- (1.1) (printed pages 504–505, PDF pages 6–7): `π` is an irreducible
  admissible representation of `G = G_r(F)` on a complex vector space `V`; it is
  generic if there is a linear form `λ ≠ 0` with `λ(π(n)v) = θ(n)λ(v)` for
  `n ∈ N`. `W(π; ψ)` is the space of functions `W(g) = λ(π(g)v)`, display (2).
  Printed page 505: "The map `W ↦ W|P` is a bijection of `W(π; ψ)` on a space
  `K = K(π; ψ)` of functions on `P`."

The Lean statement is the injective half of that bijection, transported to the
original carrier `V` through `v ↦ W_v` as explained above. Jacquet–Shalika
state this fact in (1.1) without proof; a proof is a separate task. (PDF
page numbers are one-indexed in the file above, whose first page is printed
page 499.)

The surjectivity half (the description of `K` and the inclusion of the space
`K_0` of compactly supported functions) is not part of this statement.

## Imports

`Langlands.Representation.Whittaker.GeneralLinear` (standard character,
`glFunctionals`, `IsGeneric`, coefficient models), `Langlands.Group.GL.Mirabolic`
(`mirabolic`) and Mathlib's `Mathlib.NumberTheory.LocalField.Basic`
(`IsNonarchimedeanLocalField`).

## Use

The essential-vector uniqueness reduction
`Langlands.Representation.Conductor.EssentialUniquenessReduction` takes this
injectivity, per representation, as its hypothesis `IsMirabolicRestrictionInjective`
in rank `n + 2`.
