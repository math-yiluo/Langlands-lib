# Local Weil groups mapped into relative global Weil groups

Worker 35 authored this definition unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`.

The module defines a property of a supplied continuous homomorphism

`ι : W_{F_v} →ₜ* RelativeWeilGroup c F E`

from the actual local Weil group of a finite completion `F_v` of `F` into
the published relative Weil group at a supplied class family. It constructs
no such map, and it does not assert that one exists or that it is unique.
Existence and conjugacy are separate statement targets, listed below.

## Objects

Fix number fields `F E : Type u` with `[Algebra F E]`, finite places
`v : Langlands.Global.FinitePlace F` and `w : Langlands.Global.FinitePlace E`,
and `[w.asIdeal.LiesOver v.asIdeal]`. The completed algebra
`v.adicCompletion F → w.adicCompletion E` is the scoped published
`AdelicFunctoriality.FiniteExtension` algebra. The local fields are the
published packages `padicField v` and `towerPadicField v w` over the residue
prime `p` of `v`. Their carriers are `v.adicCompletion F` and
`w.adicCompletion E`.

- `completionPadicAlgHom v w` is the completion embedding `F_v → E_w` as a
  homomorphism of `ℚ_p`-algebras for the two package algebra structures. It
  is `IsScalarTower.toAlgHom`, using the published
  `towerPadicField_isScalarTower`. The two algebra structures are definitions
  rather than instances, so the type installs them with `letI`.
  `completionPadicAlgHom_apply` states, by `rfl`, that it is the completion
  algebra map.
- `completionClosureEmbedding v w : E_w →+* \bar{F_v}`, written `j` below, is
  the published `Weil.Local.extensionFieldEmbedding` for this homomorphism.
  It is the inverse of Mathlib's chosen isomorphism
  `\bar{F_v} ≅ \bar{E_w}` over the completion map, composed with
  `E_w → \bar{E_w}`. `completionClosureEmbedding_algebraMap` proves that
  on `F_v` it is the structure map of `\bar{F_v}`. The proof applies the
  published `extensionFieldEmbedding_comp`.
- `completionWeilMap v w : W_{E_w} →ₜ* W_{F_v}` abbreviates the published
  `Weil.Local.extensionWeilMap` for the same homomorphism:
  `(σ, m) ↦ (extensionGaloisMap σ, m^f)`, where `f` is the residue degree
  of `E_w / F_v`. `extensionGaloisMap` is
  `Field.absoluteGaloisGroup.map`. The published
  `extensionClosureLift_galoisMap` shows that it is compatible with the
  closure isomorphism. Hence the Galois image of every element of
  `W_{E_w}` fixes `j(E_w)` pointwise. The library already proves that
  `extensionWeilMap` is an injective open embedding.
- `C_E = NumberField.IdeleClassGroup (𝓞 E) E`, and
  `i_w = IdeleClassGroup.ofAdicCompletion (𝓞 E) E w : E_wˣ →* C_E` is
  Mathlib's `w`-coordinate map. It is Tate's `η` in (1.6.1).
- `e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)` is a
  continuous isomorphism `W_{E_w}^{ab} ≃ₜ* E_wˣ`, for the canonical topology
  on `E_wˣ`. `LocalFactor.RankOne.reciprocityUnits _ e` is the abelianization
  map followed by `e`.

## The predicate

`IsLocalRelativeWeilMap v w e ι` takes, in addition, `{c}` and
`[IsGalois F E]`. It is the conjunction of the following three conditions.

1. `LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
   (towerPadicField v w).canonicalTopologicalData e`. This is the published
   geometric normalization of local Weil reciprocity for `E_w`. The order of
   `e(y)` is the geometric degree of `y`, and the induced Galois map satisfies
   the geometric norm-residue relations. A uniformizer therefore corresponds
   to a geometric Frobenius.
2. For all `g : W_{F_v}` and `x : E`,

   `j(x_w(projection c F E (ι g) x)) = σ_g(j(x_w(x)))`,

   where `x_w = algebraMap E (w.adicCompletion E)` and `σ_g` is the
   published `Weil.Local.localProjection _ g` in `Gal(\bar{F_v}/F_v)`.
   That is, the image of `ι g` in `Gal(E/F)` acts on `E` as the Galois
   image of `g` does, through the embedding `E → E_w → \bar{F_v}`.
3. For all `y : W_{E_w}`,

   `ι(completionWeilMap v w y) = (inclusion c F E (i_w(e[y])))⁻¹`.

   Here `e[y] = reciprocityUnits _ e y`. On the image of `W_{E_w}`, `ι` is
   the inverse of the geometric reciprocity image followed by the
   `w`-coordinate map into `C_E ⊆ W_{E/F}`. The section on the sign below
   explains the inverse.

Conditions 2 and 3 agree on `W_{E_w}`. If `g = completionWeilMap y`, then
`σ_g` fixes `j(E_w)` pointwise. Condition 2 therefore says that the
projection of `ι g` acts trivially on `E`. Condition 3 gives an element of
the coefficient subgroup, whose projection is the identity.

## Condition 2 and the decomposition group

Condition 2 is stated elementwise on `E`, so it needs no Galois instance for
`E_w / F_v`. Since `E / F` is normal, every `σ ∈ Gal(\bar{F_v}/F_v)` maps
the subfield `j(E)` onto itself. The map `E → \bar{F_v}` is injective, so
there is exactly one `τ ∈ Gal(E/F)` with `j ∘ x_w ∘ τ = σ ∘ j ∘ x_w`.
Condition 2 says that `projection c F E (ι g)` is this `τ` for `σ = σ_g`.

Let `E_w / F_v` be Galois, as follows from the global hypothesis. Then
`σ_g` restricts along `j` to an element `ρ_g ∈ Gal(E_w/F_v)`, and `τ` is the
restriction of `ρ_g` to `E`. Thus condition 2 is equivalent to

`projection c F E ∘ ι = FundamentalClass.decompositionHom v w ∘ ρ`,

which is the form used in Tate (1.6.1). This equivalence is explained here
but not formalized. The module does not construct `ρ`.

## The sign in condition 3

The library's class families and local invariants use the arithmetic
normalization of Artin–Tate. Tate 1979 normalizes reciprocity
geometrically. The inverse in condition 3 converts between the two.

- Tate (1.4.1) normalizes the local reciprocity map `r_E` so that
  uniformizers correspond to geometric Frobenius elements. He notes that
  this is opposite to Artin–Tate. The library candidate `e` in condition 1
  is the inverse of Tate's `r_{E_w}`. It is an isomorphism from the
  abelianized Weil group onto the units.
- In Tate (1.2), the coefficient embedding of the extension `W_{E/F}` of
  `Gal(E/F)` by `C_E` is defined through `r_E`. Tate calls its class
  `a_{E/F}` the canonical class. Cup product with `a_{E/F}` in degree `-2`
  gives the isomorphism `Gal(E/F)^{ab} ≅ C_F / N C_E` of his reciprocity
  law. The arithmetic fundamental class `u_{E/F}` of Artin–Tate XV §1 (W3)
  is characterized in the same way by the arithmetic reciprocity law. The
  two reciprocity isomorphisms are inverse to each other, and cup product is
  linear in the class, so `a_{E/F} = -u_{E/F}`.
- Pushing Tate's extension out along inversion on `C_E`, which is an
  equivariant automorphism, negates its class. Tate's group, with coefficient
  embedding `x ↦ i_T(x⁻¹)`, is therefore an extension with class `u_{E/F}`.
  It is equivalent to `ClassExtension (c F E)` when `c F E = u_{E/F}`. The
  equivalence sends `i_T(x)` to `(inclusion c F E x)⁻¹`.
- Tate's `θ_v` maps `y ∈ W_{E_w}` to `i_T(i_w(r_{E_w}^{-1}(y)))`. Its image
  in `ClassExtension (c F E)` is therefore
  `(inclusion c F E (i_w(e[y])))⁻¹`, which is condition 3.

Equivalently, let `art(x) = e^{-1}(x⁻¹)` be the arithmetic Artin map, which
sends uniformizers to arithmetic Frobenius classes. Condition 3 then says
`ι(y) = inclusion c F E (i_w(art^{-1}[y]))`, with no inverse.

Two independent checks confirm this sign.

- **Global check.** Let `D_w ⊆ Gal(E/F)` be the decomposition group, of
  order `n = [E_w : F_v]`. Assume that `c` satisfies the published
  `Restriction`, `Generates` and arithmetic `LocalCompatibility`
  predicates. Suppose a map satisfies conditions 1 and 2, and condition 3
  without the inverse. It factors through the local relative Weil group
  `W_{F_v} / W_{E_w}^c`, with `E_wˣ` embedded through `e`. By the local form
  of Tate (1.2), the class of this extension is the negative of the
  arithmetic local fundamental class. The map is a morphism of extensions
  to the restriction of `c F E` to `D_w`, with coefficient map `i_w`.
  Comparison with `LocalCompatibility` gives `2 res_{D_w}(c F E) = 0`.
  But `res_{D_w}(c F E)` generates a cyclic group of order `n`, so `n ≤ 2`.
  With the inverse the coefficient map is `i_w ∘ inv`, and the two signs
  cancel.
- **Local model check.** Let `E_w / F_v` be unramified of degree `n`. Write
  `s` for the arithmetic Frobenius and `π` for a uniformizer of `F_v`. The
  arithmetic local class with invariant `1/n` is represented by the carry
  cocycle `(s^i, s^j) ↦ π^{⌊(i+j)/n⌋}` for `0 ≤ i, j < n`. Consider the local
  analogue of the predicate, with target the class extension of
  `Gal(E_w/F_v)` by `E_wˣ` for this cocycle and coefficient map the
  identity. Its multiplication is `(x, s)(y, t) = (x s(y) c(s, t), st)`, as in
  `ClassExtension`, and `Val(x, s^k) = v(x) + k/n` is a homomorphism to
  `(1/n)ℤ`. A geometric Frobenius `Φ` of `W_{F_v}` has degree 1, so the
  analogue of condition 2 sends it to some `(x, s^{n-1})`.
  Then `Φ^n` is the image of some `y ∈ W_{E_w}` of degree 1, so `e[y]` has
  order 1. With the inverse, `n Val(x, s^{n-1}) = Val(e[y]⁻¹)` gives
  `v(x) = -1`. Without the inverse it gives `n v(x) = 2 - n`, which has no
  integral solution for `n ≥ 3`.

Both checks are explanations, not formal proofs. The library does not yet
identify the class of the actual local relative Weil group.

## Parameters and scope

- **Reciprocity candidate.** `e` is an explicit parameter. The published
  target `LocalClassField.WeilReciprocityExistenceUniqueness` is not proved
  in the library. A proof would determine `e` uniquely from condition 1.
  Until then, condition 1 records the normalization, and statements quantify
  over `e`.
- **Class family.** `c` is arbitrary, and no fundamental-class predicate is
  assumed. For a family that is not the arithmetic fundamental class, no map
  with these properties need exist. The predicate is then unsatisfiable,
  and nothing here says otherwise.
- **Topology.** `ι` is a continuous homomorphism for the published
  topologies on `W_{F_v}` and on `RelativeWeilGroup c F E`. The latter is the
  product of the quotient topology on `C_E` and the discrete topology on
  `Gal(E/F)`. Condition 3 is an equality of group elements, so the topology
  chosen on `E_wˣ` does not affect it.
- **Relation to `localToRelative`.** The published
  `RelativeWeilGroup.localToRelative` starts from the class extension
  `CompletionClassExtension v w a` of a local degree-two class, not from the
  actual local Weil group. This module asserts no relation between the two.

## Later targets

These are separate statement candidates.

- **Conjugacy (unconditional).** Let `ι` and `ι'` both satisfy the predicate
  for the same `e`. By condition 2, `a(g) = ι'(g) ι(g)^{-1}` lies in `C_E`.
  It is trivial on `W_{E_w}` by condition 3, and it is a 1-cocycle of `D_w`
  in `C_E`. The library proves `H^1(D_w, C_E) = 0` for `E / E^{D_w}`
  (`ideleClassH1Vanishing`, `H1VanishingProof`). Therefore
  `ι' = b ι b^{-1}` for some `b ∈ C_E`, as in Tate (1.5) and (1.6.1).
- **Existence.** Tate (1.6.1) gives the existence of `ι`. Here it would hold
  when `c` is the arithmetic fundamental class, which means its relative
  class formation and arithmetic normalization together with local
  compatibility, and `e` satisfies condition 1.

## Sources

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  - §1.2, printed pp.4–5 (PDF pp.13–14): `W_{E/F}`, its canonical class,
    and the degree `-2` cup product giving the reciprocity law.
  - (1.4.1), printed p.6 (PDF p.15): geometric normalization of `r_E`,
    opposite to Artin–Tate.
  - §1.5, printed p.8 (PDF p.17): `C_E`-conjugacy from the vanishing of
    `H^1`.
  - (1.6.1) and its proof, printed pp.8–9 (PDF pp.17–18): the map
    `θ_v : W_{F_v} → W_{E/F}`, its compatibility with `η`, and uniqueness up
    to inner automorphism.
- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
  Chapter XV §1, Definition 1 (W3) and Theorem 1, printed pp.167–168
  (PDF pp.176–177): the class of `W_{E/F}` is the arithmetic fundamental
  class.

The predicate is a derived formulation. The three conditions follow
Tate's (1.6.1) and are translated to the arithmetic normalization of the
library's class families. Conditions 2 and 3 are stated elementwise
because the library provides no local relative Weil group and no local
Galois instance.
