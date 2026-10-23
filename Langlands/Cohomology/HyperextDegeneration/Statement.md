# Degeneration of the hyperext spectral sequence

Author: Worker 3.

Documentation correction: Worker 54, with source and infrastructure audit by
Worker 291.

This module declares one auxiliary definition and one proposition in the
namespace `Langlands.Cohomology`. The proposition
`HyperextDegenerationStatement` is a theorem-statement definition, not a
proof. Bijectivity of the edge map is its conclusion; it is not supplied as
data or as a hypothesis.

The statement is the abstract form of the degeneration step in Harris 1997
(spectral sequence (10) collapsing to the isomorphisms (11)) and in Harris
1999 (spectral sequence (4.10.1) degenerating to (5.2)). In both papers the
`Ext` groups vanish in positive degree because the coefficient
representation is supercuspidal. The spectral sequence then reduces to
isomorphisms between `Hom` from compactly supported cohomology and the
cohomology of the Shimura variety.

## Setting

`C` is an abelian category with objects in `Type u` and morphisms in
`Type v`. Two of Mathlib's existence assumptions are parameters:

- `[HasDerivedCategory.{w} C]` fixes a model of the derived category
  `DerivedCategory C`, with morphisms in `Type w`;
- `[HasExt.{w'} C]` makes the Yoneda-type groups `Abelian.Ext.{w'} X Y i`
  of Mathlib available, with values in `Type w'`.

Both are instances of Mathlib's standard constructions
(`HasDerivedCategory.standard`, `HasExt.standard`). The `Ext` groups do not
depend on these choices up to canonical bijection (`Abelian.Ext.homEquiv`),
so the two universe parameters are independent. The print check below
instantiates the statement with `HasDerivedCategory.standard`.

`DerivedCategory.homologyFunctor C k` is the cohomology functor `H^k` from
the derived category to `C`. `DerivedCategory.singleFunctor C 0` sends an
object `W` to the complex with `W` in degree zero. `ShiftedHom K L n` is
Mathlib's abbreviation for `K ⟶ L⟦n⟧`.

## The edge map

`HyperextDegeneration.edgeMap K W n` sends `f : K ⟶ W⟦n⟧` (with `W` placed
in degree zero) to a morphism `H^{-n}(K) ⟶ W`. It is the composite of:

1. `(homologyFunctor C 0).shiftMap f (-n) 0`, the morphism
   `H^{-n}(K) ⟶ H^0(W)` that `f` induces on cohomology. Mathlib's shift
   sequence on the cohomology functors identifies `(homologyFunctor C 0).shift a`
   with `homologyFunctor C a` by definition (`DerivedCategory.shift_homologyFunctor`
   is `rfl`). `Functor.shiftMap f a a'` with `n + a = a'` is
   `H^a(f)` followed by the canonical isomorphism `H^a(W⟦n⟧) ≅ H^{a+n}(W)`;
   here `a = -n` and `a' = 0`;
2. the component at `W` of `DerivedCategory.singleFunctorCompHomologyFunctorIso C 0`,
   Mathlib's canonical isomorphism `H^0(W) ≅ W` for the single complex.

So the edge map is "take cohomology in degree `-n`". This is the edge
homomorphism `Hom(K, W[n]) → E_2^{0,n} = Hom(H^{-n}(K), W)` of the spectral
sequence `E_2^{p,q} = Ext^p(H^{-q}(K), W) ⇒ Hom(K, W[p+q])`.

## The proposition

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `HyperextDegenerationStatement C` | `K` is an object of the derived category and `b` an integer with `H^i(K) = 0` for all `i > b`. `W` is an object of `C` with `Ext^i(H^k(K), W)` a subsingleton for every integer `k` and every natural number `i > 0`. | For every integer `n`, `edgeMap K W n : Hom(K, W⟦n⟧) → Hom(H^{-n}(K), W)` is bijective. |

The first hypothesis says that `K` is bounded above. By Mathlib's
`DerivedCategory.isLE_iff` it is equivalent to `K.IsLE b` for the standard
t-structure. A subsingleton abelian group is zero, so the second hypothesis
says that `Ext^i(H^k(K), W) = 0` for all `k` and all `i > 0`.

### Why the statement is true and why it assumes boundedness above

The statement is not proved here. The following standard argument shows that
it is correct as stated; it uses only the standard t-structure on the derived
category and holds in every abelian category. For each `m` there is a
distinguished triangle `τ≤(m-1) K → τ≤m K → H^m(K)[-m] →`. Apply
`Hom(-, W[n])`. One has `Hom(H^m(K)[-m], W[n+s]) = Ext^{n+m+s}(H^m(K), W)`.

- If `m < -n`, then `Hom(τ≤m K, W[n]) = 0`, because `τ≤m K` lies in
  `D^{≤ -n-1}` and `W[n]` in `D^{≥ -n}`.
- If `m = -n`, the outer terms `Hom(τ≤(-n-1) K, W[n])` and
  `Hom(τ≤(-n-1) K, W[n-1])` vanish for the same reason. So
  `Hom(τ≤(-n) K, W[n]) ≅ Hom(H^{-n}(K), W)`.
- If `m > -n`, the terms `Ext^{n+m}(H^m(K), W)` and `Ext^{n+m+1}(H^m(K), W)`
  have positive degree and vanish by hypothesis. So restriction gives
  `Hom(τ≤m K, W[n]) ≅ Hom(τ≤(m-1) K, W[n])`.
- For `m ≥ b` one has `τ≤m K ≅ K`.

Composing these finitely many bijections gives
`Hom(K, W[n]) ≅ Hom(H^{-n}(K), W)`. Up to the canonical isomorphisms
`H^{-n}(τ≤(-n) K) ≅ H^{-n}(K)` and `H^{-n}(W[n]) ≅ W`, this bijection is the
edge map, since it is induced by applying `H^{-n}`.

Boundedness above makes the induction finite. Boundedness below alone is not
assumed. Without boundedness above the comparison would need a convergence
argument for the spectral sequence. Such an argument is available, for
example, when `C` has enough injectives; it is not part of this statement.
Harris's complexes are bounded: they compute the compactly supported
cohomology of a space of finite dimension. So the bounded-above case covers
his use.

## Original-source correspondence

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119:

- Lemma 6, p.91, gives a spectral sequence
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M_N, Q_ℓ)(n-1), A(G_J, C^p)) ⇒ H^{i+j}(S_{C^p N}, Q_ℓ)`,
  with `Ext` in the category of smooth `G_J`-modules.
- In the proof, pp.92-94, a complex `P` of smooth projective `G_J`-modules
  represents the compactly supported cohomology of `M_N` ((5), (6)). The Čech
  double complex (7) is rewritten as an isomorphism
  `Rf_* Q_ℓ ≅ RHom(Rp_! Q_ℓ(n-1), A(G_J, C^p))` in the derived category,
  p.94. On p.95 Harris says the spectral sequence is "the spectral sequence
  of composite functors associated to this isomorphism".
- Passing to the limit gives (8), p.95, still with `Q_ℓ` coefficients. From
  p.95 on, Harris takes "étale cohomology with coefficients in `Q̄_ℓ`,
  obtained from `H(·, Q_ℓ)` by extension of coefficients". For a
  supercuspidal `π_v`, (10), p.96, is the spectral sequence with
  `Ext^i_{G_J}(H^j_c(M_N, Q̄_ℓ)(n-1), Π_p^m)` on its `E_2` page. On p.96 Harris shows that the higher `Ext` groups
  vanish: Frobenius reciprocity for compact induction from `G_J^0` and the
  injectivity and projectivity of supercuspidals ([BZ, 2.44], [Cs, 5.4.1]).
  He concludes that "the spectral sequence (10) collapses to a series of
  isomorphisms" (11):
  `Hom_{G_J}(H^j_c(M_N, Q̄_ℓ)(n-1), Π_p^m) ≅ H^j(S_N, Q̄_ℓ)[Π]`, for
  `j = 0, 1, ...`. Here `Π` is Harris's cohomological automorphic
  representation, `Π_p` its local component, and `[Π]` the isotypic
  component for its component away from `p` (p.95); typographical
  decorations of `S_N`, `M_N` and `Π` in the print are omitted.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318:

Harris defines `L_v = L ⊗_ℚ ℚ_v` for a number field `L` (p.306).
Thus `L_ℓ` is a finite-product coefficient algebra over `ℚ_ℓ`, a product
of the completions of `L` at places above `ℓ`; it may be a single field.
Here `O` retains Harris's notation for its ring of integers (p.307), and
`𝒜_ℓ(GJ, ρ, H)` is the space of automorphic forms of section 3, (3.3), with
values in the `L_ℓ`-points of the coefficient representation `W`. It is an
`L_ℓ`-module with a smooth action of `GJ`.

- Proposition 4.10, (4.10.1), printed p.311, is a spectral sequence of
  `O`-modules
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.
  Here "`Ext^i` denotes the `i`-th derived functor of `Hom` in the category
  of smooth `L_ℓ[GJ]`-modules". The sheaf `W̃ = (lim ℒ̃_m) ⊗_O L_ℓ` is the
  characteristic-zero lisse `ℓ`-adic sheaf obtained from the inverse system
  of lattice sheaves `ℒ̃_m` (p.311).
- The proof ends on p.312 with "the stronger (integral) statement" (4.10.4):
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, O(n-1)), 𝒜_ℓ(GJ, ℒ, H)) ⇒ H^{i+j}(S̄_{K(N)}, ℒ̃)`,
  with the lattice `ℒ` in the coefficient representation and the lattice
  sheaf `ℒ̃`. The degeneration below is not asserted for (4.10.4).
- On p.312, below (5.1), Harris writes: "since `π_v` is supercuspidal, the
  higher Ext's vanish and the spectral sequence (4.10.1) degenerates to an
  isomorphism" (5.2):
  `Hom_{GJ}(H_c^{2(n-1)-j}(M̌_N, O(n-1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`.
  Here `[π^v]` selects the isotypic component for `π^v`, the part of `π`
  away from `v` (Harris uses that "knowing `π^v` determines `π_v`", p.312).
  `[JL(π_v)]` selects the isotypic component for the local
  Jacquet–Langlands transfer `JL(π_v)` of `π_v`. On the right, `[π]` is the
  `JL(π_f)`-isotypic component, as defined on p.312. The target is a characteristic-zero
  cohomology group with coefficients in `W̃`.

Coefficients in (5.2). The first argument of `Hom` in (5.2) is printed with
`O(n-1)` coefficients, while the spectral sequence (4.10.1) has `L_ℓ(n-1)`.
The second argument `𝒜_ℓ(GJ, ρ, H)[π^v]` is an `L_ℓ`-module. A
`GJ`-equivariant `O`-linear map from an `O`-module `M` to an `L_ℓ`-module
`V` extends uniquely to an `L_ℓ`-linear map from `M ⊗_O L_ℓ`, so
`Hom_{GJ}(M, V) = Hom_{GJ}(M ⊗_O L_ℓ, V)`. The `L_ℓ`-coefficient complexes
are obtained from the integral ones by tensoring with `L_ℓ` (compare Harris
1997 p.92: "Tensoring with `Q_ℓ`, we obtain our complex"). Since `L_ℓ` is
flat over `O`, for `M` the integral cohomology `M ⊗_O L_ℓ` is then the
`L_ℓ`-coefficient cohomology of (4.10.1). This scalar extension is the
reformulation used here: the Lean statement is applied in
the category of smooth `L_ℓ[GJ]`-modules of (4.10.1). The display (5.2) is a
characteristic-zero statement and does not assert vanishing of integral
`Ext` groups.

Correspondence with the Lean statement. Take for `C` the category of smooth
`Q_ℓ`-representations of `G_J` (Harris 1997) or of smooth `L_ℓ[GJ]`-modules
(Harris 1999, (4.10.1)). Let `K` be the object of its derived category with
`H^{-q}(K) = H_c^{2(n-1)-q}(M_N)(n-1)` (with `Q_ℓ`, respectively `L_ℓ`,
coefficients), that is, compactly supported cohomology shifted by `2(n-1)`
and Tate twisted. Let `W` be the coefficient representation. Then the printed
`E_2` term is `Ext^p(H^{-q}(K), W)`, and Harris's abutment in degree `p+q`
is `Hom(K, W[p+q])`. Under these identifications:

| Source | Statement | Lean |
| --- | --- | --- |
| Harris 1997 p.96, (10) → (11); Harris 1999 p.312, (4.10.1) → (5.2) | When the higher `Ext` groups from every cohomology group into the coefficient representation vanish, the spectral sequence degenerates to isomorphisms `Hom(H^{-j}(K), W) ≅ H^j`. | `HyperextDegenerationStatement`: the edge map `Hom(K, W⟦n⟧) → Hom(H^{-n}(K), W)` is bijective. |
| Harris 1997 pp.94-95, `P` bounded complex of projectives, `RHom(Rp_! Q_ℓ(n-1), A)` | The abutment is `Hom` in the derived category from the complex computing compactly supported cohomology. | `ShiftedHom K ((singleFunctor C 0).obj W) n` in `DerivedCategory C`, with `K` bounded above. |

The source asserts a degeneration of a spectral sequence. The Lean statement
asserts its conclusion directly, for the edge map, without constructing the
spectral sequence. Mathlib has no hyperext spectral sequence for this
setting. The degeneration argument above shows that the conclusion does not
depend on one. This is a derived formulation of the printed step, so the
provenance is `derived`.

Indexing. The printed (10) and (11) write `H^j_c` where (8) and Harris 1999
(4.10.1) write `H_c^{2(n-1)-j}`. The Lean statement follows the indexing of
(8) and (4.10.1): the conclusion pairs `H^{-n}(K)` with `Hom(K, W[n])`. In
Harris's application only the middle degree `j = n-1` contributes
(Proposition 1, p.97), and there the two indexings agree.

## Related results that are not restated

- Vanishing of `Ext` in positive degree from a projective object, or into an
  injective object, is in Mathlib: `Abelian.Ext.eq_zero_of_projective`,
  `Abelian.Ext.eq_zero_of_injective`, `Abelian.Ext.subsingleton_of_injective`.
- The Frobenius-reciprocity step for `Ext`, an adjunction between exact
  functors inducing bijections of `Ext` groups, is Mathlib's
  `Adjunction.extEquiv`.
- A cochain complex `P` of projectives that is strictly bounded above is
  K-projective (`CochainComplex.isKProjective_of_projective`). For such `P`,
  the cohomology classes of the Hom complex from `P` to `L` correspond to
  morphisms from `P` to shifts of `L` after localization at
  quasi-isomorphisms (`HomComplex.CohomologyClass.equivOfIsKProjective`).
  This is the step from Harris's Čech complex (7) to `RHom`.
- The edge map is natural in `K` and `W`. This follows from Mathlib's
  `Functor.shiftMap_comp` and `Functor.shiftMap_comp'` and the naturality of
  `singleFunctorCompHomologyFunctorIso`. So the bijection is equivariant for
  any group acting on `K` and `W` by morphisms, which is the
  `G(A_f^v)`-equivariance of (8). It is not restated.

## Scope

- The statement concerns an arbitrary abelian category. The Library already
  supplies the abelian category of smooth representations in
  [Category/Abelian](../../Representation/Category/Abelian.md), enough
  injectives in
  [SmoothPartAdjunction](../../Representation/Category/SmoothPartAdjunction.md),
  and [SmoothExt](../SmoothExt.md). The latter defines `ext` by right-deriving
  equivariant Hom in the second argument, with `extMap`, `bifunctor`,
  `isoHomologyOfInjectiveResolution`, `extZeroIso`, and positive-degree
  vanishing for injective second arguments. Its scope is an arbitrary
  commutative ring `R` and topological group `G`, with `R`, `G` and
  representation carriers in one universe. This module imports only
  Mathlib, not those companion modules. Their availability does not
  discharge the statement's bounded-above or `Abelian.Ext`-vanishing
  hypotheses. The Harris-specific specialization, identification of the
  relevant Ext constructions, and vanishing from his cohomology objects
  into the supercuspidal coefficient representation remain separate
  obligations; that supercuspidal vanishing is not stated here.
- The spectral sequence itself, its other edge maps and its behaviour without
  the vanishing hypothesis are not stated.
- Only bounded-above `K` are covered (see above).

## Registered sources

- `harris-1997-drinfeld-cohomology`: Harris, Invent. Math. 129 (1997),
  75-119, PDF SHA-256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
  Lemma 6 and its proof, printed pp.91-95 (PDF pp.17-21), and pp.95-96
  (PDF pp.21-22) through (11), read in the text layer. The bars that
  distinguish `Q̄_ℓ` from `Q_ℓ` are drawn separately; they were located in
  the page content of pp.95-96.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  the coefficient conventions of section 3, printed pp.306-307, and Proposition
  4.10 with (4.10.1)-(4.10.4) and section 5 through (5.3), printed
  pp.311-312 (PDF pp.8-9, 13-14), read visually from the page scans.
  Worker 54 rechecked the original coefficient convention and ring of
  integers on pp.306-307 visually for this documentation correction.

## Formal dependencies and checks

The module imports only Mathlib:
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`,
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` and
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The environment
is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Checks `c4aa9962-69a1-4c81-8edb-44817db82a50` (draft),
`60314392-957d-40a7-a686-1a87b44bfb8c` (this module path) and
`84445008-0496-4f79-9ab1-42bfccbb3f72` (after the Markdown correction; same
Lean bytes) built the module with Lake with no errors or warnings. Each inspected `HyperextDegenerationStatement` as a
`Prop`-valued definition with universe parameters `w`, `w'`, `v`, `u`,
depending only on `propext`, `Classical.choice` and `Quot.sound`. Check
`26c638f1-5eee-4068-97ba-fa67b0da00cf` printed `edgeMap` and the statement
with universe annotations, and the output was read. It also compiled an
instantiation of the statement with `HasDerivedCategory.standard`. The prints
show:

- `edgeMap` is the composite of `Functor.shiftMap` of
  `homologyFunctor C 0` at `-n` and `0` with the component at `W` of
  `singleFunctorCompHomologyFunctorIso C 0`;
- the statement quantifies over every `K` and `b`, assumes the vanishing of
  `H^i(K)` for `i > b` and subsingleton `Abelian.Ext.{w'}` groups in positive
  degree, and concludes `Function.Bijective` for every `n`.

Compilation and inspection establish a well-formed statement; they do not
prove it.
