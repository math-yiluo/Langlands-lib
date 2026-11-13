# Galois stability of `G(K)^1` and `G(K)^0`, and `G(F)^0 = G(K)^0 ∩ G(F)`

`Langlands.Geometry.Building.UnramifiedZeroDescentStatement` is an unproved
proposition. The module declares nothing else. It is an interface: nothing
here proves the statement or any of the source results cited below.

## The statement

The proposition is universe polymorphic. At each universe `u` it ranges over
every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, in equal and mixed characteristic. It also
ranges over every group scheme `G` over `Spec F` and assumes
`IsConnectedReductive G`. No other premise or instance is assumed. In
particular, nothing is assumed about the data `E` and `Z0` below beyond their
types.

Write `K = UnramifiedClosure F`, the maximal unramified extension of `F`
inside its separable closure. Write `G_K = baseChanged F K G` for the base
change of `G` along `Spec K → Spec F`. Write `v` for
`MaximalUnramified.valuation F`, the normalized `ℤ`-valued valuation of `K`.
Write `σ · x` for `rationalConjugate F K G σ x`, the action of
`σ : K ≃ₐ[F] K` on `G_K(K)` through the `F`-structure of `G`. Write `ι` for
`rationalExtend F K G : G(F) →* G_K(K)`, the inclusion of `F`-points into
`K`-points. The proposition is the conjunction of three clauses.

1. **`G(K)^1` is Galois-stable.** For every `σ : K ≃ₐ[F] K` and every `x` in
   `characterValuationKernel v G_K`, the point `σ · x` is again in
   `characterValuationKernel v G_K`. Here `characterValuationKernel v G_K` is
   the set of `x ∈ G_K(K)` with `v (χ x) = 1` for every `K`-rational
   character `χ` of `G_K`.
2. **`G(K)^0` is Galois-stable.** For every `E : UnramifiedZeroDatum F G_K`,
   every `σ : K ≃ₐ[F] K` and every `x ∈ E.zeroPoints`, the point `σ · x` is
   in `E.zeroPoints`. The datum `E` consists of:
   - a maximally split maximal torus `T` of `G_K`;
   - a finite Galois splitting field of `T` inside the separable closure;
   - the derived subgroup of `G_K` and a simply connected cover of it.

   `E.zeroPoints` is the join of `G(K)^♮` and the image of `T(K)^0`. This is
   KP Definition 2.6.23(1) for the group `G_K`, which is quasi-split.
3. **`G(F)^0 = G(K)^0 ∩ G(F)`.** For every such `E`, every
   `S : CommGroupScheme (Spec F)`, `Z : GroupScheme (Spec F)`,
   `i : S.toGrp ⟶ G`, `j : Z ⟶ G` and `Z0 : ZeroSubgroupDatum i j`,
   `E.zeroPoints.comap ι = Z0.zeroSubgroup`. The datum `Z0` says that `i` is
   a maximal split torus and that `j` represents its centralizer
   `Z = Z_G(S)`. It also supplies a datum of Definition 2.6.23(1) for `Z_K`
   and a simply connected cover of the derived subgroup of `G`.
   `Z0.zeroSubgroup` is the join of `G(F)^♮` and the image of
   `Z(F)^0 = Z(K)^0 ∩ Z(F)`. This is KP Definition 2.6.23(3), with
   Definition 2.6.23(2) for the minimal Levi subgroup `Z`.

## Existence of the data

Data `E` exist for every connected reductive `G`, so clause 2 and the
quantifier over `E` in clause 3 are not vacuous. The Library's proved
`connectedReductiveFieldExtensionStatement` makes `G_K` connected reductive.
The proved `simplyConnectedDerivedCoverExistence` then supplies the derived
subgroup of `G_K` and a simply connected cover of it. From these,
`UnramifiedZeroDatum.ofDerivedCover` (module `KPZeroDatumConstruction`)
chooses the torus and the splitting field and builds `E`.

Clause 3 holds for any `S`, `Z`, `i`, `j`. If no `ZeroSubgroupDatum i j`
exists, it holds vacuously. `ZeroSubgroupDatum.ofDerivedCovers` builds a
datum `Z0` from a maximal split torus `i`, a representing centralizer `j` and
simply connected derived covers of `G` and of `Z_K`.

## Source correspondence

The main source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). From
§2.6(d) on, `k` is a discretely valued Henselian field with perfect residue
field. The opening of Chapter 9 (printed p. 323 / PDF p. 354) fixes:

- `K`, the maximal unramified extension of `k` inside `k^s`;
- `Γ = Gal(K/k)`;
- a connected reductive `k`-group `G`.

A nonarchimedean local field `F` satisfies these hypotheses, with finite
residue field. `K ≃ₐ[F] K` is `Γ`.

* **Notation 2.6.15 and Lemma 2.6.16(4)** (printed pp. 102–103 / PDF
  pp. 133–134). `G(k)^1` is the kernel of
  `ω_G : g ↦ (χ ↦ -ω(χ(g)))` on `X^*(G)^Θ`. By Lemma 2.6.16(4), the
  characters in `X^*(G)^Θ` and those in `X^*(G)` cut out the same group. For
  the field `K`, `X^*(G_K)^Θ` is the group of `K`-rational characters of
  `G_K`. So `characterValuationKernel v G_K` is `G(K)^1`, written
  multiplicatively.
* **Definition 2.6.23 and Lemma 2.6.24** (printed p. 104 / PDF p. 135):
  - Definition 2.6.23(1) defines `G(k)^0 = G(k)^♮ · T(k)^0` for quasi-split
    `G` and a maximally split maximal torus `T`.
  - Definition 2.6.23(2) defines `G(k)^0 = G(K)^0 ∩ G(k)` when `G/Z(G)` is
    anisotropic.
  - Definition 2.6.23(3) defines `G(k)^0 = G(k)^♮ · M_0(k)^0` for a minimal
    Levi subgroup `M_0`.
  - Lemma 2.6.24 says these do not depend on the choices of `T` and `M_0`.

  The Library forms KP's products as joins of subgroups (module
  `KPZeroSubgroups`). Over `K`, the group `G_K` is quasi-split by KP
  Corollary 2.3.8, so Definition 2.6.23(1) applies to it. Corollary 2.3.8 is
  stated as `UnramifiedQuasiSplitStatement` and has conditional reductions,
  but remains unproved; `UnramifiedZeroDatum` carries the torus as data.
* **Remark 2.6.26** (printed p. 105 / PDF p. 136). The inclusion
  `G(k)^0 ⊂ G(K)^0 ∩ G(k)` is obvious from Definition 2.6.23. The converse
  inclusion is Proposition 9.3.24.
* **Proposition 9.3.24** (printed p. 343 / PDF p. 374):
  `G(k)^0 = G(K)^0 ∩ G(k)`. This is clause 3, read through `ι`.

The authors' corrections are *Corrections and additions* (version of
1 November 2024), registered as `kaletha-prasad-2024-corrections`. On PDF
p. 40 they replace the first five lines of the proof of
Proposition 9.3.24 with "Let `S ⊂ G` be a maximal `k`-split torus and let
`Z = Z_G(S)` be its centralizer." The statement is unchanged, so clause 3 is
not affected.

The replaced lines include the printed formulas
`G(k)^0 = [T(K)^0 · Z(K)^♮]^Γ · G(k)^♮` and
`G(K)^0 ∩ G(k) = [T(K)^0 · G(K)^♮]^Γ`. These take `Γ`-fixed points in
`G(K)^0` and so use a `Γ`-action on it. The corrected proof does not use
these formulas.

## Provenance of clauses 1 and 2

Clauses 1 and 2 are not numbered results in KP. They are derived.

KP use both of them without comment in §9.2.5 (printed pp. 327–328 / PDF
pp. 358–359). There, for a `Γ`-stable bounded subset `Ω` of an apartment of
`B(G_K)`, they descend the models `𝒢^1_Ω` and `𝒢^0_Ω` from the integers of
`K` to the integers of `k` by Fact 2.10.16. Their integral points are
`G(K)^1_Ω` and `G(K)^0_Ω`. Fact 2.10.16 needs these groups to be
`Γ`-stable. That follows from the `Γ`-stability of `G(K)^1` and `G(K)^0`
together with the `Γ`-equivariance of the action on `B(G_K)`.

The derivation of each clause is as follows.

* **Clause 1.** Let `σ ∈ Γ` and let `χ` be a `K`-rational character of
  `G_K`. Then `χ(σ · x) = σ(χ'(x))`, where `χ' = σ⁻¹ ∘ χ ∘ σ` is the
  conjugate character. `χ'` is again `K`-rational because `G` is defined
  over `k`. The valuation of `K` is `Γ`-invariant, being the unique
  extension of the valuation of the Henselian field `k`. Hence
  `v(χ(σ · x)) = v(χ'(x)) = 1` for `x ∈ G(K)^1`.
* **Clause 2.** `σ` carries `G(K)^♮` onto itself. This uses KP Fact 2.6.21
  and the uniqueness of the simply connected cover, since `G_sc` is defined
  over `k`. `σ` carries `T(K)^0` onto `(σT)(K)^0`, where the conjugate torus
  `σT` is again a maximally split maximal torus of `G_K`. By Lemma 2.6.24
  (and Lemma 2.5.12 for the splitting field), `G(K)^0` does not depend on
  the torus.

## Why every datum may be quantified

Clauses 2 and 3 range over every datum `E` and every datum `Z0`, not over
chosen ones. This is sound because, by KP Lemma 2.6.24, `G(K)^0` and
`G(k)^0` do not depend on the choices. The other choices also do not change
these groups:

- the splitting field, by Lemma 2.5.12;
- the simply connected cover, which is unique up to unique isomorphism.

So the universally quantified statement says the same as KP's statement for
one choice. Over `K` the Library already states this independence as
`UnramifiedZeroPointsIndependenceStatement` (`E.zeroPoints = E'.zeroPoints`).
Quantifying over every datum makes the statement usable with whatever datum
a consumer holds.

## Provenance and scope

The provenance is derived. The three clauses restate KP Proposition 9.3.24
and the Galois stability that KP use in §9.2.5. They are stated on the
Library's existing carriers:

- `characterValuationKernel`;
- `UnramifiedZeroDatum.zeroPoints`;
- `ZeroSubgroupDatum.zeroSubgroup`;
- `rationalConjugate`;
- `rationalExtend`.

The analogous identity for `G(F)^1` is already proved in the Library as
`MaximalUnramified.characterValuationKernel_comap` (module
`UnramifiedStabilizerDescent`).

The construction of integral models for KP Axioms 4.1.20 and 4.1.22 (task
`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs all three clauses:

- Clauses 1 and 2 make the integral points of the models over the integers
  of `K` Galois-stable, so the models descend to `𝒪[F]` by KP Fact 2.10.16.
- Clause 3 identifies the integral points of the descended connected models
  with `G(F)^0 ∩` (fixer of `Ω`), as Axiom 4.1.20 requires. This is how KP
  use Proposition 9.3.24 in §9.2.5.
