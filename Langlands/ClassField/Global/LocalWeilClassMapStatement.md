# Local Weil groups mapped into completed-local class extensions

Worker 1237 authored this statement unit for task
`241e7251-de0b-431f-83a9-5584e974e22b`. The module contains one proposition
definition, `Langlands.ClassField.Global.LocalWeilClassMapExistenceStatement`,
with universe parameter `u`. It returns `Prop`. Nothing is proved here.

The statement is the local half of the existence statement
`LocalRelativeWeilMapExistenceStatement` of the module
`Langlands.ClassField.Global.LocalRelativeWeilMapStatement`. It says that the
actual local Weil group of `F_v` maps to the completed-local class extension at a
local fundamental class. It uses the same completion embedding, Galois projection
and inverse reciprocity convention as the published predicate
`RelativeWeilGroup.IsLocalRelativeWeilMap`.

## `LocalWeilClassMapExistenceStatement`

Fix number fields `F E : Type u` with `[Algebra F E]`, a finite place `v` of `F`,
and a finite place `w` of `E` with `w.asIdeal.LiesOver v.asIdeal`. Write `F_v`
for `(padicField v).Carrier`, the actual completion `v.adicCompletion F`, and
`E_w` for `w.adicCompletion E`. Assume `[IsGalois F_v E_w]`. There is no global
`IsGalois F E` hypothesis.

The hypotheses are:

1. `J : InvariantFamily.{u, u} (residuePrime v)` satisfies
   `J.RelativeClassFormation` and `J.ArithmeticNormalization`.
2. `e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)` satisfies
   `LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
   (towerPadicField v w).canonicalTopologicalData e`. So `e` is a geometrically
   normalized reciprocity candidate for the actual local Weil group of `E_w`.
3. `a : CompletionH2 v w` satisfies
   `IsFundamentalClass F_v E_w (J.relative (padicField v) E_w) a`, that is,
   `J.relative (padicField v) E_w a = reciprocalClass [E_w : F_v]`.

The finite-dimensionality instance needed by `J.relative` and `IsFundamentalClass`
is supplied in the statement by the published `FiniteExtension.local_finite`.
This is the same proof term as the local instance `completionFiniteDimensional` of
`Langlands.ClassField.Global.RelativeWeilGroup`.

The conclusion is that there is a continuous homomorphism

`κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a`

with the following two properties.

The module sets no local topology instances. So `CompletionClassExtension v w a`
carries the product topology built from the Krull topology on
`Gal(E_w/F_v)`, which Mathlib supplies by default. This topology is discrete
because `E_w / F_v` is finite (Mathlib's
`krullTopology_discreteTopology_of_finiteDimensional`). It therefore equals the
published discrete topology `completionGaloisTopology := ⊥`, which
`LocalClassExtension` and `RelativeWeilGroup` use, but only up to
`DiscreteTopology.eq_bot`, not definitionally. The target statement
`LocalRelativeWeilMapExistenceStatement` follows the same convention: it also
sets no local instances.

- **(P) Galois projection.** For every `g` in the local Weil group of `F_v` and
  every `x : E_w`,

  `completionClosureEmbedding v w (CompletionClassExtension.projection v w a (κ g) x)
    = localProjection (padicField v) g (completionClosureEmbedding v w x)`.

  Here `completionClosureEmbedding v w : E_w → \bar{F_v}` is the published
  embedding along which `completionWeilMap` is formed. So the image of `κ g` in
  `Gal(E_w/F_v)` is the restriction of the Galois image of `g` to `E_w`.
- **(R) Reciprocity on `W_{E_w}`.** For every `y` in the local Weil group of `E_w`,

  `κ (completionWeilMap v w y) =
    (CompletionClassExtension.inclusion v w a (reciprocityUnits (towerPadicField v w) e y))⁻¹`.

  So `κ` restricted to `W_{E_w}` is the inverse of `e`, followed by the inclusion
  `E_wˣ → CompletionClassExtension v w a`.

`CompletionClassExtension v w a` is the published product-coordinate group
extension `1 → E_wˣ → X → Gal(E_w/F_v) → 1` built from a chosen normalized
representative of `a`. Its isomorphism class over both ends depends only on `a`
(`CompletionClassExtension.equivOfRepresentative`).

## Conventions and sign

The inverse in (R) is the same as in condition 3 of
`IsLocalRelativeWeilMap`. A geometric `e` sends a geometric Frobenius to an
element of valuation one. Then `y ↦ e(y)⁻¹` is the arithmetic reciprocity
identification of `W_{E_w}^{ab}` with `E_wˣ`. With this identification, Artin–Tate
show that the extension class is the arithmetic fundamental class of invariant
`1/n`. That is the normalization fixed by `IsFundamentalClass` and
`ArithmeticNormalization`.

A direct check in the unramified case confirms the sign. Let `E_w/F_v` be
unramified of degree `n`, let `φ` be the arithmetic Frobenius, and let `χ(φ) = 1`.
By `ArithmeticNormalization`, the class `a` is the cyclic class of a uniformizer
`π` of `F_v`. Its cocycle is `z(φ^i, φ^j) = π` if `i + j ≥ n`, and `1` otherwise.
The published `factorSet` gives `s(σ) s(τ) = z(σ, τ) s(στ)` for the section
`s`. Hence `s(φ)^n = π` in `X`. Let `Φ` be an arithmetic Frobenius lift in
`W_{F_v}`. By (P), `κ(Φ) = b · s(φ)` for some `b ∈ E_wˣ`, so
`κ(Φ^n) = N(b) · π`, which has valuation `n · ord(b) + 1`. Now `Φ^n` lies in
`W_{E_w}` and is an arithmetic Frobenius there. So by (R), `κ(Φ^n) = e(Φ^n)⁻¹`,
which has valuation `1`. These are compatible, with `ord(b) = 0`. With the
opposite class `-a`, the two valuations could not agree when `n > 2`.

## Why the statement holds

The statement is not vacuous, and under its hypotheses it is the classical
theorem. The argument below is described here and not formalized.

- **The class `a` is the actual fundamental class.** `RelativeClassFormation`
  includes `RelativeImages`, so `J.relative` is injective with image the
  denominator subgroup of order `[E_w : F_v]`. It also includes
  `InflationCompatibility`. Let `M/F_v` be unramified of degree
  `n = [E_w : F_v]`, and work in the compositum `E_w M`. Because `J.relative` is
  injective, the relative `H²` of `E_w M / F_v` is cyclic. By inflation
  compatibility both inflations are injective, so their images are the same
  subgroup of order `n`. Inflation compatibility then transfers the invariants
  from `M/F_v` to `E_w/F_v`.
  `ArithmeticNormalization` fixes the invariants on `M/F_v`. Hence `J.relative`
  on `E_w/F_v` is the actual invariant map, and `a` is the actual arithmetic
  fundamental class `u_{E_w/F_v}`.
- **The candidate `e` is the actual reciprocity map.** The candidate is a
  topological isomorphism from the abelianized Weil group of `E_w` to `E_wˣ`.
  The published theorem `geometricWeilReciprocityUniqueness` shows that at most
  one candidate satisfies the geometric relation. The classical one is the
  inverse isomorphism of Tate's reciprocity map `r_{E_w}`, which sends
  uniformizers to geometric Frobenius elements (Tate 1979, (1.4.1)).
- **The local Weil-group extension has the fundamental class.** Let
  `W = W_{F_v}` and `W_E = W_{E_w}`, the image of `completionWeilMap v w`. The
  group `W / W_E^c` is an extension of `Gal(E_w/F_v)` by `W_E^{ab}`. Identify
  `W_E^{ab}` with `E_wˣ` by `y ↦ e(y)⁻¹`. Then the class of this extension is
  `u_{E_w/F_v}`. This is Artin–Tate XV, Theorem 8(b), with the discussion on
  printed pp.184–185 of the case where the Weil group lies inside the Galois
  group; Tate 1979 §1.2 states the same fact for any Weil group. The extensions
  `W / W_E^c` and `CompletionClassExtension v w a` have the same class. So there
  is an isomorphism between them that is the identity on `Gal(E_w/F_v)` and the
  chosen identification on `E_wˣ`. This is the classification of group
  extensions by `H²`, which Artin–Tate use in the proof of XV, Theorem 1.
  Composing it with the quotient map gives `κ`, and (P) and (R) hold by
  construction.
- **Continuity.** `W_E` is open of finite index in `W`, and `κ` on `W_E` is the
  continuous map `y ↦ inclusion (e y)⁻¹`. Hence `κ` is continuous.

## Relation to the target

The statement is a prerequisite of the target
`LocalRelativeWeilMapExistenceStatement`. That target, with `IsGalois F E` and the
published `isGalois_adicCompletion` instance, follows from it as follows.

- Take `J := I (residuePrime v)`. Choose `a` with the fundamental-class property
  from `RelativeImages`: the image is the denominator subgroup, which contains
  `reciprocalClass n`.
- Set `ι := RelativeWeilGroup.localToRelative c v w I h a ha ∘ κ`.
- Condition 2 of `IsLocalRelativeWeilMap` follows from (P), the published
  `projection_localToRelative`, and the fact that
  `FundamentalClass.decompositionHom v w σ` acts on `E` through
  `algebraMap E E_w`.
- Condition 3 follows from (R), `localToRelative_inclusion` and `map_inv`.

Conversely, the local identification cannot be avoided in a proof of the target.
This is a mathematical remark, and nothing in Lean asserts it. Supply the
classical invariant families and fundamental classes, so that the target's
hypotheses hold, and let `ι` be a map given by the target. By condition 3, `ι`
kills `W_{E_w}^c`. So `ι` induces a morphism of extensions from
`W_{F_v} / W_{E_w}^c` to the part of `W_{E/F}` over the decomposition group. On
the kernels it is `E_wˣ → C_E`. Hence the local Weil class and `a` have the same
image in `H²(Gal(E_w/F_v), C_E)`. That map from `H²(Gal(E_w/F_v), E_wˣ)` is
injective by global class field theory. So the local Weil class is `a`, which is
the content of this statement.

The statement is more general than the target needs in two ways. It uses one
local invariant family `J` at the residue prime of `v`, not a family over all
primes. It also uses only the local hypothesis `IsGalois F_v E_w`.

## Provenance

Derived formulation. The statement restates, for the library's actual local Weil
groups, completions and completed-local class extensions, the classical fact that
the local Weil-group extension `W_{F_v} / W_{E_w}^c` has the fundamental class. It
is stated at one finite level, as a map into the product-coordinate extension
rather than as an isomorphism. The sign is the one fixed by the published
`IsLocalRelativeWeilMap`.

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II
  (1979), source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  - (1.1), printed pp.3–4 (PDF pp.12–13): definition of a Weil group;
    `W_{E/F} = W_F / W_E^c` in (1.1.1) is on printed p.4 (PDF p.13).
  - (1.2), printed pp.4–5 (PDF pp.13–14): `W_{E/F}` is an extension of
    `Gal(E/F)` by `W_E^{ab} ≅ C_E`, and its class `α_{E/F}` is the fundamental
    class. The argument compares with a cyclic extension of the same degree by
    inflation.
  - (1.4.1), printed p.6 (PDF p.15): the local nonarchimedean Weil group as the
    subgroup of `G_F` acting on the residue field by integral powers of Frobenius,
    with `r_E` the reciprocity map. Uniformizers correspond to geometric
    Frobenius, which is opposite to the convention of Artin–Tate.
- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
  - Chapter XV §1, Definition 1 and Theorem 1, printed pp.167–168
    (PDF pp.176–177): Weil groups of a normal layer, with condition W3) that
    `U_E / U_L^c` has the fundamental class `α_{L/E}`.
  - Chapter XV, Theorem 8, printed p.182 (PDF p.191): if every normal layer has a
    cyclic layer of the same degree, the reciprocity condition (a) can replace W3).
  - Chapter XV, printed pp.184–185 (PDF pp.193–194): for nonarchimedean local
    fields and global function fields the Weil group lies inside the Galois group.
    The class of `0 → U_K / U_K^c → U_F / U_K^c → G_{K/F} → 0` is then the
    fundamental class by Theorem 8(b). The function-field case is written out.
