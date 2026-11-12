# Convergence of the hyperext spectral sequence for bounded objects

Author: Worker 16.

This module declares three theorem-statement definitions in the namespace
`Langlands.Cohomology.HyperextConvergence`. They are propositions, not
proofs: the vanishing of the differentials and the isomorphisms with the
graded pieces are their conclusions, and nothing is supplied as data or as a
hypothesis about the spectral sequence. No proof is given here; the truth
argument below explains why the statements hold.

The statements say that Worker 61's hyperext spectral sequence converges to
`Hom(K, B⟦n⟧)` when `K` is bounded for the t-structure. They are the abstract
convergence part of the spectral sequences `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}, 𝒜) ⇒ H^{i+j}`
of Harris 1999, (4.4.1) and (4.10.1). The identification of the abutment
with the cohomology of a Shimura variety is a separate geometric input and is
not stated here.

## Setting

`C` is a category with objects in `Type u` and morphisms in `Type v`. It is
preadditive, has a zero object and a shift by `ℤ` by additive functors, and is
pretriangulated and triangulated (`IsTriangulated C`). These are the
hypotheses under which Worker 61 constructs the spectral sequence. All three
propositions take `C` and these instances as parameters and quantify over the
rest.

The following declarations of other modules are used.

- `HyperextSpectralSequence.hyperextSpectralSequence t K B`
  (module `Langlands.Cohomology.HyperextSpectralSequence`, Worker 61): for a
  t-structure `t : TStructure C` and objects `K` and `B`, Mathlib's
  `E₂CohomologicalSpectralSequence` in `AddCommGrpCat.{v}` of the spectral
  object obtained by applying `Hom(-, B)` to the truncations of `K`. Its
  page `r` is a complex of abelian groups indexed by `ℤ × ℤ` whose
  differential has bidegree `(r, 1 - r)`. Its object in position `(p, q)` on
  page 2 is `Hom(heartPiece t K q, B⟦p + q⟧)` (`secondPageIso`), where
  `heartPiece t K q` lies in degrees `≥ -q` and `≤ -q`; classically it is
  `H^{-q} K` placed in degree `-q`.
- `HyperextAbutment.filtration t K B n p` and `HyperextAbutment.graded t K B n p`
  (module `Langlands.Cohomology.HyperextAbutmentFiltration`, Worker 61):
  `F^p ⊆ Hom(K, B⟦n⟧)` is the subgroup of morphisms that factor through
  `K ⟶ τ_{≥ p - n} K`, equivalently that vanish on `τ_{< p - n} K`, and
  `gr^p = F^p / F^{p+1}`.
- Mathlib: `TStructure.IsGE K a` and `TStructure.IsLE K b` say that `K` lies
  in degrees `≥ a` and `≤ b` for `t`; `SpectralSequence.page`,
  `HomologicalComplex.X` and `HomologicalComplex.d` are the pages, their
  objects and their differentials; `AddCommGrpCat.of` makes an abelian group
  an object of `AddCommGrpCat`.

## Declarations

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `HyperextPageDegenerationStatement C` | `t` is a t-structure on `C`; `K` and `B` are objects; `a` and `b` are integers with `K` in degrees `≥ a` and `≤ b`; `r` is an integer with `2 ≤ r` and `b - a + 2 ≤ r`. | For all `pq pq' : ℤ × ℤ`, the differential `d : E_r^{pq} ⟶ E_r^{pq'}` of page `r` of `hyperextSpectralSequence t K B` is zero. |
| `HyperextStablePageStatement C` | The same. | For all integers `p` and `q`, the object `E_r^{p,q}` of page `r` is isomorphic in `AddCommGrpCat` to `AddCommGrpCat.of (graded t K B (p + q) p)`, the graded piece `gr^p` of the abutment filtration on `Hom(K, B⟦p + q⟧)`. |
| `HyperextConvergenceStatements C` | — | The conjunction of the two. |

`HomologicalComplex.d pq pq'` is zero by definition when `pq'` is not
`pq + (r, 1 - r)`, so the first proposition says that every differential of
page `r` vanishes. The second asserts that an isomorphism exists
(`Nonempty`); it does not name one.

Quantifier order: `t`, `K`, `B`, `a`, `b`, the two boundedness instances,
`r` and the proof of `2 ≤ r` are universally quantified, then the hypothesis
`b - a + 2 ≤ r`, then the positions. The page bound depends only on `a` and
`b`; it is uniform in `B` and in the position.

## Indexing

Mathlib's `E₂`-spectral sequence of a spectral object indexed by
`EInt = WithBotTop ℤ` (`Abelian.SpectralObject.coreE₂Cohomological`) puts in
position `(p, q)` of page `r` the term
`E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` of the spectral object. In the
hyperext spectral object the term `H^n(i ⟶ j)` is `Hom` from a truncation of
`K` in the degrees from `1 - j` to `-i` into `B⟦n⟧`, and `H^n(⊥ ⟶ ⊤)` is
`Hom(K, B⟦n⟧)` (`abutmentIso`). So the row `q` involves `H^{-q} K`, the
abutment in total degree `n` is `Hom(K, B⟦n⟧)`, and the graded piece paired
with `(p, q)` is `gr^p` of `Hom(K, B⟦p + q⟧)`, which involves the truncation
at `p - (p + q) = -q`. This is the pairing recorded in Worker 61's
`HyperextAbutmentFiltration`: `gr^p` corresponds to `E_∞^{p, n - p}`.

## Why the statements are true

The statements are not proved here. The following standard argument shows
that they are correct as stated.

1. If `K` lies in degrees `≥ a` and `≤ b`, then `heartPiece t K q` is zero
   unless `-b ≤ q ≤ -a`. Each `E_r^{p,q}` is a subquotient of
   `E_2^{p,q} = Hom(heartPiece t K q, B⟦p + q⟧)`, because Mathlib defines it
   as the homology of a short complex whose middle term is that group. So
   page `r` is zero outside the `b - a + 1` rows `-b ≤ q ≤ -a`.
2. The differential of page `r` goes from row `q` to row `q + 1 - r`. If
   `r ≥ b - a + 2`, the two rows cannot both lie in `[-b, -a]`, so the
   differential vanishes. This is `HyperextPageDegenerationStatement`.
3. For `q` in `[-b, -a]` and `r ≥ b - a + 2`, one has `q - r + 2 ≤ -b` and
   `q + r - 1 ≥ 1 - a`. Then the truncations of `K` that enter
   `E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` agree with those for
   `⊥ ≤ q ≤ q + 1 ≤ ⊤`, so `E_r^{p,q}` is the term
   `E^{n}(⊥ ≤ q ≤ q + 1 ≤ ⊤)` with `n = p + q`. By the exact sequences of the
   spectral object (Verdier's description, which Mathlib follows), this term
   is the image of the restriction map
   `Hom(τ_{≥ -q} K, B⟦n⟧) → Hom(τ_{≤ -q} K, B⟦n⟧)` along the composite
   `τ_{≤ -q} K → K → τ_{≥ -q} K`.
4. That image is `gr^p`. The map `F^p → Hom(τ_{≤ -q} K, B⟦n⟧)`,
   `f ↦ f ∘ (τ_{≤ -q} K → K)`, has image the image in step 3, because `F^p`
   is the set of composites of `K → τ_{≥ -q} K` with morphisms
   `τ_{≥ -q} K → B⟦n⟧`. Its kernel is `F^p ∩ F^{p+1} = F^{p+1}`, because
   `F^{p+1}` consists of the morphisms that vanish on `τ_{≤ -q} K`. So
   `gr^p` is isomorphic to `E_r^{p,q}`.
5. For `q` outside `[-b, -a]` both sides are zero. If `-q > b`, then
   `τ_{≥ -q} K = 0`, so `F^p = 0`. If `-q < a`, then `τ_{≥ -q} K = K` and
   `τ_{≥ 1 - q} K = K`, so `F^p = F^{p+1}`. And `E_r^{p,q} = 0` by step 1.

When `a > b` the object `K` is zero, both sides are zero, and the hypothesis
`2 ≤ r` alone keeps the page index valid.

## Original sources

Cartan and Eilenberg, *Homological Algebra*, Princeton University Press,
1956, Chapter XVII (registered literature
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`;
printed page `p` is PDF page `p + 22`). Cartan and Eilenberg's complexes are
cochain complexes, with differential of degree `+1`, and they "systematically
use the notation `A_n = A^{-n}`" (Chapter IV §3, p.58, checked visually).

- §2, p.368, formula (4): for a functor `T(A, C)` covariant in `A` and
  contravariant in `C`, and complexes `A` and `C`, the second spectral
  sequence of the hypercohomology of `T(A, C)` has initial terms
  `II_2^{p,q} = Σ_{p₁+p₂=p} R^q T(H^{p₁}(A), H_{p₂}(C))`. "In the notation
  for the second spectral sequence, the second index `q` indicates the
  degree of the filtration."
- §3, p.369 (checked visually): the second filtration is regular in "Case 1.
  The complex `A` is bounded from below (i.e. `A^p = 0` for `p` sufficiently
  small) and the complex `C` is bounded from above (i.e. `C^p = 0` for `p`
  sufficiently large)." Then (4), p.370, is the "second cohomology spectral
  sequence of `T(A, C)`",
  `Σ_{p₁+p₂=p} R^q T(H^{p₁}(A), H_{p₂}(C)) ⇒ ℋ^n T(A, C)`, with `q` the
  filtration degree.

For `T(A, C) = Hom(C, A)` with `A` a module, placed in degree `0`, and `C` a
complex, (4) reads `R^q Hom(H_p(C), A) = Ext^q(H_p(C), A) ⇒ ℋ^{p+q} Hom(C, A)`.
Write `K` for the cochain complex `C`, so `K^i = C^i = C_{-i}`. Then
`H_p(C) = H^{-p}(K)`, and the hypercohomology is `Hom(K, A[n])` in the
derived category. After exchanging the names of the two indices, so that
the filtration degree is the first one as in Mathlib and in Harris, this is `E_2^{p,q} = Ext^p(H^{-q} K, A) ⇒ Hom(K, A[p+q])`. The
Lean statements are a derived reformulation of this convergence:

| Cartan–Eilenberg | Lean |
| --- | --- |
| Modules over a ring; hypercohomology computed from Cartan–Eilenberg resolutions | Any triangulated category with a t-structure; `Hom(K, B⟦n⟧)` filtered by truncations of `K` |
| Initial term `Ext(H_p(C), A)` | `E_2^{p,q} = Hom(heartPiece t K q, B⟦p + q⟧)`; for the standard t-structure on a derived category and `B` an object of the heart this is `Ext^p(H^{-q} K, B)` (Worker 61's `HyperextSecondPage`) |
| Case 1: the complex `C` bounded from above (so `K` is bounded above), and `A` bounded below (a module is bounded) | `K` bounded on both sides for `t`; `B` arbitrary |
| Convergence of a regular filtration (limit term isomorphic to the graded module of the filtered hypercohomology) | The stable pages are isomorphic to `gr^p` from page `max(2, b - a + 2)` on, and the differentials vanish there |

The hypotheses differ from Case 1 in both arguments. Boundedness of `K` from
below is an extra hypothesis compared with Case 1. In exchange, `B` is not
required to be bounded below. Boundedness of `K` on both sides gives a
uniform page bound, and it holds in Harris's application (below).
The statement asserts that isomorphisms exist; it does not assert that they
are the canonical maps of the spectral sequence. The canonical edge map in
the degenerate case is the subject of `HyperextDegenerationStatement`
(module `Langlands.Cohomology.HyperextDegeneration.Statement`), which is
proved in the Library.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318 (registered literature
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`):

- Proposition 4.4, (4.4.1), printed p.309 (checked visually): for a free
  `O/ℓ^m O`-module `ℒ` with constant étale sheaf `ℒ̃` and `O_m = O/ℓ^m O`,
  a spectral sequence of `O_m`-modules
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, O_m(n-1)), 𝒜_ℓ(GJ, ℒ, K(m))) ⇒ H^{i+j}(S̄_{K(N,m)}, ℒ̃)`,
  where "`Ext^i` denotes the `i`-th derived functor of `Hom` in the category
  of smooth `O_m[GJ]`-modules".
- Proposition 4.10, (4.10.1), printed p.311: the same with `L_ℓ`
  coefficients,
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`,
  with `Ext^i` in the category of smooth `L_ℓ[GJ]`-modules.
- Fact 2, printed p.303: the étale cohomological dimension of the
  distinguished domains `U(ẽ)` is at most `D = 2(n - 1)`, and Lemma 2.2 bis,
  p.305, truncates the resolutions in degree `D + 1`. The complexes that
  compute compactly supported cohomology are therefore bounded.

In the notation of the Lean statement, take for `C` the derived category of
smooth `L_ℓ[GJ]`-modules with its standard t-structure, for `K` a complex with
`H^{-j}(K) = H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1))`, and for `B` the coefficient
module `𝒜_ℓ(GJ, ρ, H)` in degree `0`. Then Harris's `E_2^{i,j}` is the
position `(i, j)` on page 2, and `K` lies in degrees `≥ -2(n-1)` and `≤ 0`.
The statements give convergence to `Hom(K, B⟦i + j⟧)` from page
`2(n - 1) + 2 = 2n` on. That `Hom(K, B⟦i + j⟧)` is `H^{i+j}(S̄_{K(N)}, W̃)`
is the comparison Harris derives from the `p`-adic uniformization (4.3) and
the complexes of Harris's §2. It needs the Drinfeld tower and the Shimura
variety as actual objects, which the Library does not yet have, and it is
not part of this module. Harris's printed text uses these spectral sequences
only through the degeneration (5.2); this module supplies the general
convergence that makes the arrows `⇒` precise.

## Nonvacuity and checks

The hypotheses are satisfiable in the intended setting. A private test file,
not part of this module, compiled the following over this module, with
imports of Mathlib's `DerivedCategory.TStructure` and
`ModuleCat.Abelian`:

```lean
example (R : Type) [Ring R] :
    letI := HasDerivedCategory.standard (ModuleCat.{0} R)
    Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{0} R)
  Langlands.Cohomology.HyperextConvergence.HyperextConvergenceStatements
    (DerivedCategory (ModuleCat.{0} R))

example (R : Type) [Ring R] [HasDerivedCategory (ModuleCat.{0} R)]
    (K : DerivedCategory (ModuleCat.{0} R)) (a b : ℤ) [K.IsGE a] [K.IsLE b] :
    DerivedCategory.TStructure.t.IsGE K a ∧ DerivedCategory.TStructure.t.IsLE K b :=
  ⟨inferInstance, inferInstance⟩
```

So the statement applies to derived categories of module categories with
the standard t-structure, and Mathlib's `K.IsGE a` and `K.IsLE b` for
complexes with bounded cohomology give the instances it uses. Objects with
bounded cohomology exist in every such category (for example `0`, or a
module placed in degree `0`, which lies in degrees `≥ 0` and `≤ 0`).

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over Library
commit `18a1f10aef8ea135d90e8474439a5e6d9c130008`: diagnostic
`89a5813f-548c-4369-9c91-d988f8d4488f` compiled the module with no errors or
warnings and inspected `HyperextConvergenceStatements`
(`statement_returns_prop: true`, level parameters `v, u`, axioms `propext`,
`Classical.choice`, `Quot.sound`). Diagnostic
`6b6df0c9-54cc-4e85-a248-444bf34fbf21` printed the elaborated bodies of the
three definitions and compiled the instantiation above.

Revision: Worker 16 later corrected this Markdown. The earlier version
misquoted Case 1 of Cartan and Eilenberg as `C_p = 0` and read it as
boundedness of `K` from below. The Lean file is unchanged. Diagnostic
`9708447a-6ef3-4370-bef2-07b41e6c029b` recompiled the module over Library
commit `003dc092bfd3b226c86f83c40156844905f35c2c` with no errors or warnings
and inspected `HyperextConvergenceStatements` with the same result.

## Dependencies

Library commit `18a1f10aef8ea135d90e8474439a5e6d9c130008`, unchanged in
`003dc092bfd3b226c86f83c40156844905f35c2c`:

- `Langlands.Cohomology.HyperextSpectralSequence` (Worker 61):
  `hyperextSpectralSequence`, `heartPiece`, `secondPageIso`, `abutmentIso`.
- `Langlands.Cohomology.HyperextAbutmentFiltration` (Worker 61):
  `HyperextAbutment.filtration`, `HyperextAbutment.graded`.

No other Library module is imported.

## Not stated here

- The canonical isomorphisms `E_∞^{p,q} ≅ gr^p` and their naturality in `K`
  and `B`.
- Convergence in Cartan–Eilenberg's Case 1 itself, with `K` bounded above
  and `B` bounded below but `K` not bounded below. It is stated in the
  companion module `Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`,
  where the page from which a position is stable depends on the position.
- The identification of the abutment with the cohomology of Harris's Shimura
  varieties, and the spectral sequences (4.4.1) and (4.10.1) as statements
  about actual Drinfeld towers and Shimura varieties.
