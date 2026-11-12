# Berkovich's test relations, continuous actions and `G`-spaces

Author: Worker 21.

Berkovich makes the automorphism group `G(X)` of an analytic space a
topological group by means of a set `E(X)` of "test" data. A `G`-space is an
analytic space with a continuous action of a topological group `G`. This
module transcribes these definitions on the Library's category of analytic
spaces `LocalizedCategory` (`SaturatedStrongLocalization`). It defines:

- the test triples `(U, f, t)` and Berkovich's relation `d(φ, ψ) < (U, f, t)`
  on morphisms of analytic spaces;
- the sets `G_{(U, f, t)}(X)` of automorphisms near the identity;
- continuity of an action of a group `G` on an analytic space;
- the category of `G`-spaces and `G`-morphisms, and restriction along
  continuous homomorphisms.

It does not construct the uniform space structure on `Mor(Y, X)` itself, the
induced spaces `X_{G/H}`, the category `𝒜n^op` of spaces with varying groups,
or the equivariant sites.

## Original sources

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
Berkovich's manuscript below cites it as [Ber3].

- §6, printed p.557 / PDF p.19: "All the analytic spaces considered in this
  section are assumed to be Hausdorff." Further: "Let X be an analytic space.
  We introduce a set 𝔈(X) as follows. An element ε of 𝔈(X) consists of a
  finite family s(ε) = {U_i}_{i∈I} of compact analytic domains in X and, for
  each i ∈ I, of finite sets of analytic functions {f_ij}_{j∈J_i} on U_i and of
  positive numbers {t_ij}_{j∈J_i}. … Given two morphisms φ, ψ : Y → X, we
  write d(φ, ψ) < ε if φ⁻¹(U_i) = ψ⁻¹(U_i) and ρ(φ_i^* f_ij − ψ_i^* f_ij) ≤ t_ij
  for all i ∈ I and j ∈ J_i, where φ_i and ψ_i are the induced morphisms
  φ⁻¹(U_i) → U_i (if φ⁻¹(U_i) is empty, the above inequality is assumed to
  hold)." Here `ρ(f) = max_{x∈X} |f(x)|`. Also: "We endow the group G(X) with
  the topology induced from Mor(X, X). It is easy to see that G(X) is really a
  topological group (not necessarily Hausdorff), and its topology is defined
  by the system of the subgroups G_ε(X) = {σ ∈ G(X) | σ(U_i) = U_i,
  ρ(σ_i^* f_ij − f_ij) ≤ t_ij} for ε ∈ 𝔈(X) as above." For `X` over `T`,
  `G_T(X) := G(X) ∩ Mor_T(X, X)`.
- §6, printed p.558 / PDF p.20: "We remark also that for each ε ∈ 𝔈(X) there
  exists δ ≤ ε such that δ is the infimum of elements defined by the triples
  (U, f, t), where U is an affinoid domain in X, f ∈ 𝒪(U) and t > 0." Here
  `δ ≤ ε` means that `d(φ, ψ) < δ` implies `d(φ, ψ) < ε`, and the infimum takes
  the union of the families.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, is used
for the comparison arguments below.

- §1.1, printed p.14 / PDF p.11: a collection `τ` is a net if it is a
  quasinet and, for any `U, V ∈ τ`, `τ` restricted to `U ∩ V` is a quasinet on
  `U ∩ V`. Lemma 1.1.2(ii): for a net `τ` of compact sets, "if
  V ⊂ V_1 ∪ … ∪ V_n for some V, V_1, …, V_n ∈ τ, then there exist
  U_1, …, U_m ∈ τ such that V = U_1 ∪ … ∪ U_m and each U_i is contained in
  some V_j".
- Proposition 1.2.13(i), printed p.21 / PDF p.18: the collection `τ̂` is a
  net; after the proof, "The sets from τ̂ are said to be Φ-affinoid domains in
  X". The proof of (ii) constructs, "for each pair U, V ∈ τ̂ with U ⊂ V", a
  canonical bounded homomorphism "that identifies (U, 𝒜_U) with an affinoid
  domain in (V, 𝒜_V)".

Berkovich, *Spectral theory and analytic geometry over non-Archimedean
fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`,
Remark 2.2.2, printed p.28 / PDF p.42: (iii) for a morphism of affinoid
spaces `φ : 𝓜(ℬ) → 𝓜(𝒜)` and an affinoid domain `V` in `𝓜(𝒜)`, `φ⁻¹(V)` is an
affinoid domain; (iv) "If U and V are affinoid domains in X, then the
intersection U ∩ V is an affinoid domain", for an affinoid space `X`. In a
general Hausdorff analytic space intersections of affinoid domains need not
be affinoid, so the arguments below only intersect affinoid domains inside
an affinoid space.

Berkovich's unfinished manuscript *Étale equivariant sheaves on p-adic
analytic spaces* (1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`; file
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.1, printed pp.1–2, repeats these definitions and continues: "We say that
the action of a topological group G on an analytic space is continuous if the
induced homomorphism G → G(X) is continuous." On p.2: "An analytic space X
endowed with a continuous action of a topological group G will be called a
G-space. A G-equivariant morphism between two G-spaces will be called a
G-morphism." On p.1: "In what follows all analytic spaces considered are
assumed to be Hausdorff."

## Derived choices

The following choices are derived; each is explained where it is used.

1. Test triples use the charts of the saturated presentation of `X` as
   affinoid domains.
2. The relation `d(φ, ψ) < (U, f, t)` is computed on strong representatives of
   `φ` and `ψ` with a common denominator, with an explicit covering condition.
3. Continuity is stated as: the preimage of every set `G_τ(X)` of a test
   triple `τ` is a neighbourhood of the identity of `G`.
4. Automorphisms are those of `LocalizedCategory`, that is, `K`-linear ones.

## Test triples and nearness of strong maps

All declarations are in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. The field `K` is a complete
ultrametric normed field; its valuation may be trivial.

- `TestTriple B`, for a saturated presentation `B`, consists of a chart index
  `domain` (the affinoid domain `U`), an element `function` of the chart
  algebra (the analytic function `f ∈ 𝒪(U)`), and a real `bound` `t` with
  `bound_pos : 0 < t`. `TestTriple.locus` is the chart range, the subset `U`
  of the space.
- `IsTestPiece τ a b i`, for strong maps `a b : T ⟶ B` with a common source,
  says that both maps send the chart `i` of `T` into `U`.
- `StrongNear τ a b` is Berkovich's relation for strong maps:
  1. `a⁻¹(U) = b⁻¹(U)`;
  2. every point of `a⁻¹(U)` lies in a chart `i` with `IsTestPiece τ a b i`;
  3. for every such chart `i` and every point `p` of its spectrum,
     `p(a_{i,U}(f) − b_{i,U}(f)) ≤ t`, where `a_{i,U}` and `b_{i,U}` are the
     bounded algebra maps of the two strong maps at the pair `(i, U)`.

  A point `p` of the spectrum of the chart algebra is a point `y` of the
  chart, and `p(a_{i,U}(f) − b_{i,U}(f))` is `|(a^*f − b^*f)(y)|`. Conditions
  2 and 3 together say that `|(a^*f − b^*f)(y)| ≤ t` at every point `y` of
  `a⁻¹(U)`, that is, `ρ(a^*f − b^*f) ≤ t` on `a⁻¹(U)`. If `a⁻¹(U)` is empty,
  the conditions hold.
- `StrongNear.symm` (the absolute value of `−x` is that of `x`) and
  `strongNear_id`: the identity is near itself, with the chart `U` itself as
  the covering piece and difference `0`.

Provenance of choice 1. A saturated presentation contains every affinoid
domain that lies in one of its charts (`HasAllLocalDomains`); its charts are
affinoid domains of `X`. By Berkovich's remark on p.558, `E(X)` is generated
by triples whose `U` is an affinoid domain. Such triples are in turn
generated by triples on charts, by the following argument, which uses no
intersection of affinoid domains.

1. Let `U` be an affinoid domain of `X`. The charts form a quasinet and `U`
   is compact, so `U ⊆ V_1 ∪ … ∪ V_n` for finitely many charts `V_k`.
2. The affinoid domains of `X` form a net `τ̂` (Berkovich 1993,
   Proposition 1.2.13(i)), containing `U` and the `V_k`. By Lemma 1.1.2(ii)
   of Berkovich 1993, `U = U_1 ∪ … ∪ U_m` with each `U_j` in `τ̂` and contained
   in some `V_k`.
3. An affinoid domain of `X` contained in the affinoid domain `V_k` is an
   affinoid domain in `V_k` (proof of Proposition 1.2.13(ii)). Hence each
   `U_j` is a chart of the saturated presentation.
4. If `d(φ, ψ) < (U_j, f|_{U_j}, t)` for all `j`, then `φ⁻¹(U) = ψ⁻¹(U)`, as
   both are the union of the `φ⁻¹(U_j) = ψ⁻¹(U_j)`. Every point of `φ⁻¹(U)`
   lies in some `φ⁻¹(U_j)`, where the restrictions of `φ^*f` and `ψ^*f` are
   the pullbacks of `f|_{U_j}`. So `ρ(φ^*f − ψ^*f) ≤ t` on `φ⁻¹(U)`, that is,
   `d(φ, ψ) < (U, f, t)`.

This reduction is a derived argument and is not formalized.

## Nearness of morphisms of analytic spaces

- `presentationOf X` is the saturated presentation underlying an object `X`
  of `LocalizedCategory` (`localizedObjectEquiv.symm X`).
- `IsNear τ φ ψ`, for `φ ψ : Y ⟶ X` and a test triple `τ` of
  `presentationOf X`, holds if there are a saturated presentation `T`, a
  quasi-isomorphism `s : T ⟶ presentationOf Y` and strong maps
  `a b : T ⟶ presentationOf X` with `φ = s⁻¹ a`, `ψ = s⁻¹ b` in the localized
  category and `StrongNear τ a b`. Here `s⁻¹` is the Library's inverse
  `(localizedQuasiIso s hs).inv`.
- `IsNear.symm`.
- `localizedQuasiIso_id_inv`, `localizationFunctor_map_eq_fraction`: a strong
  map is the fraction with identity denominator.
  `isNear_localizationFunctor_map`: near strong maps have near images.
  `isNear_id`: `d(1_X, 1_X) < τ` for every `τ`.
- `preimage_localizedSpaceFunctor_map_fraction` computes the preimage of a set
  under the underlying map of `s⁻¹ a`, which is `a ∘ s⁻¹` by the Library's
  `localizedSpaceFunctor_map_rightFraction`. `IsNear.preimage_eq` follows:
  near morphisms have the same preimage of `U` under their actual underlying
  continuous maps, which is Berkovich's first condition.

Provenance of choice 2. Every morphism of the localized category is a right
fraction (`exists_localizedRightFraction`). Two fractions can be brought to a
common denominator by the right calculus of fractions, so a pair of morphisms
always has representatives of the form required here. On a chart `V` of `T`
with `a(V), b(V) ⊆ U`, the quasi-isomorphism `s` identifies `V` with an
affinoid domain of `Y`, and the restrictions of `φ^*f` and `ψ^*f` to it are
the images of `f` under the pieces of `a` and `b`. So `StrongNear τ a b`
implies Berkovich's `d(φ, ψ) < (U, f, t)`, given the covering condition 2.
Conversely, suppose `d(φ, ψ) < (U, f, t)` and take any common-denominator
representation. Condition 2 holds by the following argument, in which
intersections of affinoid domains are only taken inside an affinoid space.

1. Let `y ∈ a⁻¹(U)`. It lies in a chart `V₀` of `T`, which the strong maps
   `a` and `b` send into charts `W_a` and `W_b` of `X`.
2. `U ∩ W_a` is compact, since `U` is compact and `W_a` is closed in the
   Hausdorff space `X`. As `τ̂` is a net, `τ̂` restricted to `U ∩ W_a` is a
   quasinet on it. So `U ∩ W_a = D_1 ∪ … ∪ D_p` with affinoid domains `D_i`
   of `X` contained in `U ∩ W_a`, which are affinoid domains in `W_a`.
3. The piece of `a` at `(V₀, W_a)` is a morphism of affinoid spaces. By
   Berkovich 1990, Remark 2.2.2(iii), each preimage `a⁻¹(D_i) ∩ V₀` is an
   affinoid domain in `V₀`, and `V₀ ∩ a⁻¹(U)` is their union. In the same way
   `V₀ ∩ b⁻¹(U)` is a finite union of affinoid domains `b⁻¹(E_l) ∩ V₀`.
4. Choose `i` and `l` with `y ∈ a⁻¹(D_i) ∩ b⁻¹(E_l) ∩ V₀`. This is the
   intersection of two affinoid domains in the affinoid space `V₀`, hence an
   affinoid domain in `V₀` (Berkovich 1990, Remark 2.2.2(iv)).
5. `T` is saturated, so this affinoid domain in its chart `V₀` is a chart of
   `T`. It contains `y`, and both `a` and `b` send it into `U`.

Therefore the existential definition agrees with Berkovich's relation for
Hausdorff spaces. This agreement is explained here and is not formalized.
In particular, independence of the chosen representation is not proved.

## Continuous actions

- `nearIdentity τ : Set (Aut X)` is `{σ | d(σ, 1_X) < τ}`, Berkovich's
  `G_τ(X)`: `σ⁻¹(U) = U`, which for an automorphism means `σ(U) = U`, and
  `ρ(σ^*f − f) ≤ t`. `one_mem_nearIdentity`: it contains the identity.
- `IsContinuousAction ρ`, for a group `G` with a topology and a homomorphism
  `ρ : G →* Aut X`, says that `ρ⁻¹(nearIdentity τ)` is a neighbourhood of
  `1 : G` for every test triple `τ`.
- `isContinuousAction_one`: the trivial action is continuous.
- `isContinuousAction_of_discreteTopology`: every action of a discrete group
  is continuous, since every set containing `1` is a neighbourhood.
- `IsContinuousAction.comp`: precomposition with a continuous homomorphism
  `f : H →ₜ* G` preserves continuity, because preimages of neighbourhoods of
  `1 = f(1)` under the continuous `f` are neighbourhoods of `1`.

Provenance of choice 3. By Berkovich, the sets `G_ε(X)` form a basis of
neighbourhoods of the identity of the topological group `G(X)`. For a
homomorphism from a topological group `G`, continuity is equivalent to
continuity at `1`. That is, `ρ⁻¹(G_ε(X))` is a neighbourhood of `1` for all
`ε`. Since `G_ε(X)` is the intersection of the `G_τ(X)` for the triples `τ`
of `ε`, it suffices to consider single triples. By choice 1 and the remark on
p.558, the triples on charts suffice. The definition makes sense for any
group with a topology; it is Berkovich's continuity when `G` is a
topological group.

Provenance of choice 4. Berkovich's `G(X)` allows automorphisms that act on
the ground field by isometric automorphisms. The Library's
`LocalizedCategory` has `K`-linear morphisms only, so `Aut X` here is
Berkovich's group `G_K(X)` of `K`-automorphisms (p.557, `G_T(X)` with
`T = 𝓜(K)`), with the induced topology. Semilinear actions, such as Galois
actions on base changes, are not covered.

## `G`-spaces

- `gSpaceProperty K G` is the property of an object `X` of Mathlib's
  `Action LocalizedCategory G` that its underlying space
  (`localizedSpaceFunctor.obj X.V`) is Hausdorff and that its action, as the
  homomorphism `X.ρAut : G →* Aut X.V`, is continuous.
- `GSpace K G` is the full subcategory. Its morphisms are Mathlib's
  equivariant morphisms of actions, which are Berkovich's `G`-morphisms. This
  is Berkovich's fibre category `G-𝒜n` when `G` is a topological group.
- `GSpace.gSpaceProperty_of_discreteTopology`: every Hausdorff space with an
  action of a discrete group is a `G`-space.
- `GSpace.res f : GSpace K G ⥤ GSpace K H`, for a continuous homomorphism
  `f : H →ₜ* G`, restricts actions by Mathlib's `Action.res` and is lifted to
  the full subcategories by `IsContinuousAction.comp`. `res_obj_obj_V` and
  `res_obj_obj_ρ` record that it keeps the space and acts through `f`.

The universes are `u` for `K`, `v` for the spaces and `w` for the chart
indices of the presentations, as in `LocalizedCategory.{u, v, w}`. The group
universes are independent.

## Scope

Not done here: the uniform structure on `Mor(Y, X)` and the topological group
structure of `G(X)` (this module only uses the neighbourhood conditions);
independence of the representing fractions; compact analytic domains other
than charts; semilinear automorphisms; induced spaces `X_{G/H}`
(Construction 1.1.2); the category `𝒜n^op` of spaces with varying groups; and
the equivariant étale and quasi-étale sites of §1.2.
