# Convergence of the hyperext spectral sequence in Cartan–Eilenberg's Case 1, and its covariant form

Author: Worker 16.

This module declares four theorem-statement definitions in the namespace
`Langlands.Cohomology.HyperextConvergence`. They are propositions, not
proofs. Their conclusions are the vanishing of differentials, the
isomorphisms and the zero objects, and nothing is supplied as data or as a
hypothesis about the spectral sequence. No proof is given here; the truth
arguments below explain why the statements hold.

The first three definitions concern Worker 61's hyperext spectral sequence
of `K` and `B` for a t-structure. They assert its convergence when `K` is
bounded above and `B` is bounded below. These are the boundedness conditions
of Cartan and Eilenberg's Case 1. The companion module
`Langlands.Cohomology.HyperextConvergence.Statement` treats `K` bounded on
both sides and `B` arbitrary, with a page bound that does not depend on the
position. Here the page from which a position is stable depends on the
position.

The fourth definition concerns the covariant form: the same construction in
the opposite of a derived category, applied to `op K` and `op A`. It
identifies the second page with `Ext^p(A, H^q(K))` and the abutment with
`Hom(A, K⟦n⟧)`. The first three statements apply to this form. With the
composite-functor identifications of
`Langlands.Cohomology.EquivariantComposite.Statement`, they yield the
spectral sequence `H^p(G, H^q(X, F)) ⇒ H^{p+q}(X; G, F)` of Grothendieck's
Tohoku, Chapter V, Theorem 5.2.1, and its compactly supported analogue for
compact groups (see "Application").

## Setting

Generic part. `C` is a category with objects in `Type u` and morphisms in
`Type v`, two independent universes. It is preadditive, has a zero object, a
shift by `ℤ` by additive functors, and is pretriangulated and triangulated
(`IsTriangulated`). These are the instances of Worker 61's module
`Langlands.Cohomology.HyperextSpectralSequence`. Declarations of other
modules that are used:

- `HyperextSpectralSequence.hyperextSpectralSequence t K B` (Worker 61): for a
  t-structure `t` on `C` and objects `K` and `B`, Mathlib's
  `E₂`-cohomological spectral sequence of the spectral object obtained by
  applying `Hom(-, B)` to the truncations of `K`. Objects are indexed by
  `ℤ × ℤ`, and the differential of page `r` has bidegree `(r, 1 - r)`. Its
  object in position `(p, q)` on page 2 is `Hom(heartPiece t K q, B⟦p + q⟧)`
  (`secondPageIso`). `heartPiece t K q` lies in degrees `≥ -q` and `≤ -q`;
  classically it is `H^{-q}(K)` placed in degree `-q`.
- `HyperextSpectralSequence.opTStructure t` (Worker 61): the t-structure on
  `Cᵒᵖ` in which `op X` lies in degrees `≤ n` exactly when `X` lies in
  degrees `≥ -n` for `t`, and in degrees `≥ n` exactly when `X` lies in
  degrees `≤ -n` (`opTStructure_isLE_iff`, `opTStructure_isGE_iff`).
- `HyperextAbutment.filtration t K B n p` and `HyperextAbutment.graded`
  (Worker 61, module `Langlands.Cohomology.HyperextAbutmentFiltration`): the
  subgroup `F^p` of `Hom(K, B⟦n⟧)` of morphisms that factor through
  `K ⟶ τ_{≥ p - n} K`, and `gr^p = F^p / F^{p+1}`. The same module proves
  `F^p = Hom(K, B⟦n⟧)` for `p ≤ 0` when `B` lies in degrees `≥ 0`
  (`filtration_eq_top`), and `F^p = 0` when `K` lies in degrees `≤ b` and
  `b < p - n` (`filtration_eq_bot`). The same degree argument gives
  `F^p = Hom(K, B⟦n⟧)` for `p ≤ c` when `B` lies in degrees `≥ c`. So for `K`
  bounded above and `B` bounded below the filtration of each `Hom(K, B⟦n⟧)`
  is finite.
- Mathlib: `TStructure.IsLE`, `TStructure.IsGE`, the pages
  `SpectralSequence.page` with objects `X` and differentials `d`, and
  `AddCommGrpCat.of`.

Covariant part. `C` is an abelian category with objects in `Type u` and
morphisms in `Type v`, with a model `HasDerivedCategory.{w} C` of its derived
category. The proposition quantifies over `HasExt.{w'} C`, so that Mathlib's
`Abelian.Ext.{w'}` groups exist in universe `w'`. It uses:

- `DerivedCategory.TStructure.t`: Mathlib's standard t-structure on the
  derived category, in which `X` lies in degrees `≥ n` (resp. `≤ n`) exactly
  when its cohomology vanishes in degrees `< n` (resp. `> n`)
  (`DerivedCategory.isGE_iff`, `isLE_iff`).
- `DerivedCategory.singleFunctor C 0` (an object placed in degree `0`),
  `DerivedCategory.homologyFunctor C q` (the cohomology `H^q`), `ShiftedHom`
  and `Abelian.Ext`.
- Mathlib's structure on the opposite category, made available by
  `open CategoryTheory.Pretriangulated.Opposite`. Shifting by `n` on
  `D(C)ᵒᵖ` is the opposite of shifting by `-n` on `D(C)`
  (`shiftFunctorOpIso`), the distinguished triangles are the opposites of
  distinguished triangles, and `IsTriangulated` holds for the opposite of a
  triangulated category. So the generic statements of this module apply to
  `D(C)ᵒᵖ`.

## Declarations

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `HyperextHalfBoundedDifferentialStatement C` | A t-structure `t` on `C`; objects `K`, `B`; integers `b`, `c` with `t.IsLE K b` and `t.IsGE B c`; a page `r : ℤ` with `2 ≤ r`; a position `(p, q)` with `p - c + 1 ≤ r` and `q + b + 2 ≤ r` | For every `pq : ℤ × ℤ`, the differentials `d (p, q) pq` and `d pq (p, q)` of page `r` of `hyperextSpectralSequence t K B` are zero |
| `HyperextHalfBoundedStablePageStatement C` | The same | The object of page `r` in position `(p, q)` is isomorphic in `AddCommGrpCat` to `AddCommGrpCat.of (HyperextAbutment.graded t K B (p + q) p)` |
| `HyperextHalfBoundedConvergenceStatements C` | — | The conjunction of the two |
| `CovariantSecondPageStatement C` | `HasExt.{w'} C`; `K : DerivedCategory C`; `A : C` | Write `E` for `hyperextSpectralSequence (opTStructure TStructure.t) (op K) (op A₀)` in `D(C)ᵒᵖ`, with `A₀ = (singleFunctor C 0).obj A`. Then: (i) for `p : ℕ` and `q : ℤ`, the object of page 2 of `E` in position `(p, q)` is additively equivalent to `Ext^p(A, H^q(K))`; (ii) for `p < 0` that object is zero; (iii) for `n : ℤ`, the abutment `op K ⟶ (op A₀)⟦n⟧` is additively equivalent to `ShiftedHom A₀ K n`, that is, to `A₀ ⟶ K⟦n⟧` |

Conventions:

- Mathlib's page differential `d pq pq'` is defined for all pairs of
  positions and is zero unless `pq' = pq + (r, 1 - r)`. So the first
  statement says that the two differentials of page `r` meeting at `(p, q)`
  vanish.
- Only the existence of isomorphisms is asserted (`Nonempty`), not that they
  are the canonical maps of the spectral sequence.
- In the covariant statement the page objects lie in `AddCommGrpCat.{w}` and
  the `Ext` groups in `Type w'`, so the comparisons are additive
  equivalences (`≃+`) between types of possibly different universes.
- Quantifier order of the generic statements: `t`, `K`, `B`, `b`, `c`, the
  two instances, `r` and `2 ≤ r`, then `p`, `q`, then the two bounds.

## The stable range

Mathlib places in position `(p, q)` of page `r` the term
`E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` of the spectral object. Its term
`H^m(i ⟶ j)` is `Hom` from the truncation of `K` in the degrees from `1 - j`
to `-i` into `B⟦m⟧`, and `H^m(⊥ ⟶ ⊤) = Hom(K, B⟦m⟧)` (`abutmentIso`). Each
`E_r^{p,q}` is a subquotient of `E_2^{p,q} = Hom(heartPiece t K q, B⟦p + q⟧)`.

- If `q < -b`, then `heartPiece t K q` is zero because `K` lies in degrees
  `≤ b`.
- If `p < c`, then `heartPiece t K q` lies in degrees `≤ -q` and `B⟦p + q⟧`
  in degrees `≥ c - p - q > -q`, so there are no nonzero morphisms.

So all pages vanish outside the quadrant `p ≥ c`, `q ≥ -b`. The differential
of page `r` leaving `(p, q)` ends in row `q + 1 - r`, which is below `-b`
when `r ≥ q + b + 2`. The differential entering `(p, q)` starts in column
`p - r`, which is below `c` when `r ≥ p - c + 1`. For `b = c = 0` the bound
reads `r ≥ max(2, p + 1, q + 2)`, the usual bound `r > max(p, q + 1)` for a
first-quadrant spectral sequence.

## Why the statements are true

The statements are not proved here. The following argument shows that they
are correct as stated. Let `n = p + q`.

1. Differentials: by the two vanishing ranges above, the target of the
   leaving differential and the source of the entering differential are zero
   on page `r`. This is `HyperextHalfBoundedDifferentialStatement`.
2. Lower end. Let `i = q - r + 2 ≤ -b`. The truncation of `K` in the degrees
   from `1 - j` to `-i` equals the truncation in the degrees from `1 - j` on,
   because `K` lies in degrees `≤ b ≤ -i`. So the terms `H^m(i ⟶ j)` equal
   `H^m(⊥ ⟶ j)`, and `E_r^{p,q} = E^n(⊥ ≤ q ≤ q + 1 ≤ l)` with
   `l = q + r - 1`.
3. Upper end. Mathlib's `E^n(f₁, f₂, f₃)`, for composable arrows `f₁`, `f₂`,
   `f₃`, is the homology of `H^{n-1}(f₃) → H^n(f₂) → H^{n+1}(f₁)`, whose maps
   are connecting morphisms. Only the image of the first map depends on `l`.
   The exact sequence of the spectral object for `q + 1 ≤ l ≤ ⊤` is
   `H^{n-1}(q + 1 ⟶ l) → H^{n-1}(q + 1 ⟶ ⊤) → H^{n-1}(l ⟶ ⊤)`. The last
   group is `Hom(τ_{≤ -l} K, B⟦n - 1⟧)`. It vanishes when
   `-l < c - n + 1`, that is, when `l ≥ p + q - c`. This holds because
   `r ≥ p - c + 1`. Then the first map is surjective. By naturality of the
   connecting morphisms the two images in `H^n(q ⟶ q + 1)` agree. So
   `E_r^{p,q} = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`.
4. As in steps 3 and 4 of the truth argument of
   `HyperextConvergence.Statement`, the term `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` is the
   image of `Hom(τ_{≥ -q} K, B⟦n⟧) → Hom(τ_{≤ -q} K, B⟦n⟧)`, and that image
   is `gr^p` of `Hom(K, B⟦n⟧)`. This uses no boundedness. This proves
   `HyperextHalfBoundedStablePageStatement`. Positions outside the quadrant
   are included. There `E_r^{p,q} = 0`. If `p < c`, then `F^p = F^{p+1}`,
   because `p + 1 ≤ c` and `Hom(τ_{< p + 1 - n} K, B⟦n⟧) = 0` for degree
   reasons. If `q < -b`, then `τ_{≥ -q} K = 0` and `F^p = 0`.
5. Covariant statement. Let `t` be the standard t-structure on `D(C)` and
   `t' = opTStructure t`. The object `heartPiece t' (op K) q` lies in
   `t'`-degrees `-q`. Read in `D(C)`, it is the truncation of `K` in degree
   `q`, isomorphic to `H^q(K)` placed in degree `q`. Shifting by `m` on
   `D(C)ᵒᵖ` is the opposite of shifting by `-m` on `D(C)`. Hence
   `E_2^{p,q} = Hom_{D(C)ᵒᵖ}(heartPiece t' (op K) q, (op A₀)⟦p + q⟧)` is
   `Hom_{D(C)}(A₀⟦-(p + q)⟧, H^q(K)⟦-q⟧) ≅ Hom_{D(C)}(A₀, H^q(K)⟦p⟧)`. For
   `p ≥ 0` this is `Ext^p(A, H^q(K))` (Mathlib's `Abelian.Ext.homAddEquiv`).
   For `p < 0` it is zero, because `A₀` lies in degrees `≤ 0` and
   `H^q(K)⟦p⟧` in degrees `≥ -p > 0`. The abutment is
   `Hom_{D(C)ᵒᵖ}(op K, op (A₀⟦-n⟧)) = Hom_{D(C)}(A₀⟦-n⟧, K)`, which is
   `Hom(A₀, K⟦n⟧)` after shifting by `n`.

In the covariant form the filtration `F^p` of `Hom(A₀, K⟦n⟧)` consists of
the morphisms that factor through `τ_{≤ n - p} K → K`. If `K` lies in degrees
`≥ a`, then `op K` lies in `t'`-degrees `≤ -a`. Also `op A₀` lies in
`t'`-degrees `≥ 0`. So the generic statements apply with `b = -a` and
`c = 0`.

## Application: Tohoku V Theorem 5.2.1 and Berkovich Corollary 1.5.2(i)

Let `R` be a commutative ring and `G` a group acting by homeomorphisms on a
space `X`. Let `F` be an equivariant sheaf of `R`-modules. Take for `C` the
category `Rep R G`, for `K` the derived global section complex
`ι(EquivariantDerivedComplex.globalComplex R G X F)`, and for `A` the trivial
representation `Rep.trivial R G R`. Worker 13's
`isZero_globalComplex_homology` shows that `K` lies in degrees `≥ 0`. So
`op K` lies in degrees `≤ 0` and `op A₀` in degrees `≥ 0` for the opposite
t-structure (the test below proves this). Then:

- page 2 of the covariant spectral sequence is
  `Ext^p_{Rep R G}(R, H^q(X, F))` by `CovariantSecondPageStatement` and
  Worker 13's `globalComplexHomologyIso`. For `R = ℤ` this is the group
  cohomology `H^p(G, H^q(X, F))`;
- by `HyperextHalfBoundedConvergenceStatements` for `D(Rep R G)ᵒᵖ` with
  `b = c = 0`, the position `(p, q)` is stable from page
  `max(2, p + 1, q + 2)` on. It is then isomorphic to `gr^p` of the
  abutment;
- the abutment in degree `n` is `Hom(R, RΓ(X, F)⟦n⟧)` by part (iii) of
  `CovariantSecondPageStatement`. By `EquivariantGlobalCompositeStatement`
  this is `H^n(X; G, F)` for `n ≥ 0`.

This is Tohoku's second spectral sequence `II_2^{p,q} = H^p(G, H^q(X, A))`,
abutting to `H^n(X; G, A)` ((5.2.5), p.200), with the identifications only
asserted to exist. In the same way, with `SmoothRep R G`, Worker 13's
`SmoothSheafDerivedComplex.compactComplex`, the trivial smooth representation
`EquivariantComposite.trivialSmoothRep R G` and
`CompactGroupCompactCompositeStatement`, one obtains Berkovich's
`E_2^{p,q} = H^p(G, H^q_c) ⇒ H^{p+q}_c(X(G), F)` (Corollary 1.5.2(i)) for
compact `G` on ordinary topological spaces. Here `H^p(G, -)` is `Ext^p` in
smooth representations, and `H^q_c` is derived in smooth sheaves. Berkovich
states it for all topological groups, but it fails for noncompact ones. The
counterexample is in the Markdown of `EquivariantComposite.Statement`.

## Original sources

Cartan and Eilenberg, *Homological Algebra*, Princeton University Press,
1956 (registered literature
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`,
file SHA-256
`1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`; printed
page `p` is PDF page `p + 22`). The passages below were checked visually.

- Chapter IV §3, p.58: complexes are cochain complexes ("we are using the
  word 'complex' to denote what is usually called a 'cochain complex'"), and
  "We systematically use the notation `A_n = A^{-n}`".
- Chapter XVII §2, p.368, formula (4): for `T(A, C)` covariant in `A` and
  contravariant in `C`, the second spectral sequence of the hypercohomology
  has `II_2^{p,q} = Σ_{p₁+p₂=p} R^q T(H^{p₁}(A), H_{p₂}(C))`, "the second
  index `q` indicates the degree of the filtration".
- Chapter XVII §3, p.369: "Case 1. The complex `A` is bounded from below
  (i.e. `A^p = 0` for `p` sufficiently small) and the complex `C` is bounded
  from above (i.e. `C^p = 0` for `p` sufficiently large). [...] In this case
  the second filtration of `T(X, Y)` is regular." Formula (4), p.370, is the
  resulting "second cohomology spectral sequence" converging to
  `ℋ^n T(A, C)`.

Correspondence with the Lean statements:

| Cartan–Eilenberg | Lean |
| --- | --- |
| `T(A, C) = Hom(C, A)`, `A` bounded below, `C` bounded above | `Hom(K, B⟦n⟧)` with `K = C` in degrees `≤ b` and `B = A` in degrees `≥ c` (generic statements) |
| `T(A, C) = Hom(C, A)` with `C` a module (bounded) and `A` a complex bounded below | Covariant statement with `A` the module placed in degree `0` and `K` the complex; page 2 is `Ext^p(A, H^q(K))` |
| Regularity of the second filtration and the limit term | Vanishing of the differentials at `(p, q)` and `E_r^{p,q} ≅ gr^p` from page `max(2, p - c + 1, q + b + 2)` on |

For `T(A, C) = Hom(C, A)` with `A` a module in degree `0`, (4) reads
`Ext^q(H_p(C), A) ⇒ ℋ^{p+q}`. With `K = C` and `H_p(C) = H^{-p}(K)`, and
with the two indices exchanged so that the filtration degree comes first,
this is `Ext^p(H^{-q}(K), A) ⇒ Hom(K, A⟦p + q⟧)`. That is Worker 61's spectral
sequence for `B` in the heart (`c = 0`, `B` also in degrees `≤ 0`). The
filtrations agree: a morphism `K → A⟦n⟧` lies in `F^p` exactly when it
vanishes on the part of `K` in degrees `< p - n`, that is, when its
components have `Ext`-degree `≥ p`. Symmetrically, for `C` a module and `A` a
complex, (4) reads `Ext^q(C, H^p(A)) ⇒ ℋ^{p+q}`, which after the exchange of
indices is the covariant page 2.

Changes, all derived reformulations or generalizations:

- An arbitrary triangulated category with a t-structure replaces complexes
  of modules and Cartan–Eilenberg resolutions.
- For `B` not in the heart, Worker 61's spectral sequence filters by
  truncations of `K` only. Its page 2 is then `Hom(H^{-q}(K)[q], B⟦p + q⟧)`.
  Cartan and Eilenberg's second spectral sequence instead resolves both
  variables. The generic statements assert convergence of Worker 61's
  spectral sequence under Case 1 boundedness. They do not compare it with
  Cartan and Eilenberg's sequence in that case.
- The covariant form is obtained by passing to the opposite category,
  rather than by a separate construction.
- Isomorphisms are asserted to exist, not to be canonical.

Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9
(1957), Chapter V §5.2 (registered literature
`provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`,
file SHA-256
`7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`).
(5.2.3) and Theorem 5.2.1, printed p.200 (PDF p.82): two cohomological
spectral functors on `G`-sheaves abutting to `H^n(X; G, A)`. The second has
initial term `II_2^{p,q}(A) = H^p(G, H^q(X, A))`. It comes from Theorem
2.4.1 applied to the composite `Γ^G Γ_X` (5.2.2). The Application section
explains how the statements of this module and of
`EquivariantComposite.Statement` together give this spectral sequence, in
derived form.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996) (registered literature
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`),
Corollary 1.5.2(i), printed pp.11–12: the spectral sequence
`E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⇒ H^{p+q}_c(X(G), F)`. The
transport to ordinary topological spaces, smooth sheaves and compact `G` is
described in the Markdown of `EquivariantComposite.Statement`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999) (registered literature
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), uses
Berkovich's resolutions and group actions on compactly supported cohomology
in §2 (printed pp.302–305). Harris's spectral sequences (4.4.1) and
(4.10.1) have the shape of the generic statements. The relevant complexes are bounded
there, so `HyperextConvergence.Statement` already covers them.

## Nonvacuity and checks

A private test file, not part of this module, compiled the following over
it and over `Langlands.Cohomology.EquivariantComposite.Statement`:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite Opposite
  Langlands.Cohomology Langlands.Cohomology.HyperextConvergence Langlands.Sheaf.Equivariant

example (C : Type) [Category.{0} C] [Abelian C] [HasDerivedCategory.{0} C] : Prop :=
  HyperextHalfBoundedConvergenceStatements (DerivedCategory C) ∧
    HyperextHalfBoundedConvergenceStatements (DerivedCategory C)ᵒᵖ ∧
    CovariantSecondPageStatement.{0, 0} C

theorem tohoku_bounds (R G X : Type) [CommRing R] [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    [HasDerivedCategory.{1} (TopologicalSheaf G X (ModuleCat.{0} R))]
    [HasDerivedCategory.{1} (Rep.{0} R G)]
    (F : TopologicalSheaf G X (ModuleCat.{0} R)) :
    (HyperextSpectralSequence.opTStructure DerivedCategory.TStructure.t).IsLE
      (op (DerivedCategory.Plus.ι.obj ((EquivariantDerivedComplex.globalComplex R G X).obj F))) 0 ∧
    (HyperextSpectralSequence.opTStructure DerivedCategory.TStructure.t).IsGE
      (op ((DerivedCategory.singleFunctor (Rep.{0} R G) 0).obj (Rep.trivial R G R))) 0 := by
  refine ⟨(HyperextSpectralSequence.opTStructure_isLE_iff _ _ _).2 ?_,
    (HyperextSpectralSequence.opTStructure_isGE_iff _ _ _).2 ?_⟩
  · rw [neg_zero]
    exact (DerivedCategory.isGE_iff _ 0).2 fun i hi =>
      EquivariantDerivedComplex.isZero_globalComplex_homology R G X F hi
  · rw [neg_zero]
    exact (inferInstance : ((DerivedCategory.singleFunctor (Rep.{0} R G) 0).obj
      (Rep.trivial R G R)).IsLE 0)

example (R G X : Type) [CommRing R] [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    [HasDerivedCategory.{1} (TopologicalSheaf G X (ModuleCat.{0} R))]
    [HasDerivedCategory.{1} (Rep.{0} R G)] [HasExt.{1} (Rep.{0} R G)]
    (h : HyperextHalfBoundedConvergenceStatements.{1, 1} (DerivedCategory (Rep.{0} R G))ᵒᵖ)
    (h2 : CovariantSecondPageStatement.{1, 1, 0, 1} (Rep.{0} R G))
    (h3 : EquivariantComposite.EquivariantGlobalCompositeStatement.{1, 1, 0})
    (F : TopologicalSheaf G X (ModuleCat.{0} R)) (p q r : ℤ) (hr : 2 ≤ r)
    (hp : p + 1 ≤ r) (hq : q + 2 ≤ r) : True := by
  obtain ⟨hK, hA⟩ := tohoku_bounds R G X F
  have e₁ := h.2 (HyperextSpectralSequence.opTStructure DerivedCategory.TStructure.t)
    (op (DerivedCategory.Plus.ι.obj ((EquivariantDerivedComplex.globalComplex R G X).obj F)))
    (op ((DerivedCategory.singleFunctor (Rep.{0} R G) 0).obj (Rep.trivial R G R))) 0 0 r hr p q
    (by lia) (by lia)
  have e₂ := (h2 (DerivedCategory.Plus.ι.obj ((EquivariantDerivedComplex.globalComplex R G X).obj F))
    (Rep.trivial R G R)).1
  have e₃ := h3 R G X 0
  trivial
```

The test file also proves the analogous bounds for
`SmoothSheafDerivedComplex.compactComplex R G X F` and
`EquivariantComposite.trivialSmoothRep R G` in `D(SmoothRep R G)ᵒᵖ`, for a
compact topological group `G` with `HasStableNeighbourhoods G X`, and checks
that `CovariantSecondPageStatement` elaborates for `SmoothRep R G`.

So the generic statements apply to derived categories and to their
opposites, and the covariant statement applies to representations and smooth
representations. The hypotheses of the Tohoku application hold for every
equivariant sheaf. The three statements can be applied together to it, at
morphism universes `w = w' = 1` over `u = 0`.

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over Library
commit `31e40c5ae36490ae0e69099d9dca183c6e478d98`:

- Diagnostic `eaa71530-dfa0-4e19-8280-ee44b08f4a36` compiled the module with
  no errors or warnings and inspected
  `HyperextHalfBoundedConvergenceStatements`: `statement_returns_prop: true`,
  level parameters `v, u`, axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- Diagnostic `008d034d-0ca0-408e-824f-ceb42f0c2edf` compiled the module and
  the test file with no errors or warnings and inspected
  `CovariantSecondPageStatement`: `statement_returns_prop: true`, level
  parameters `w, w', v, u`, the same axioms.

## Dependencies

Library commit `31e40c5ae36490ae0e69099d9dca183c6e478d98`:

- `Langlands.Cohomology.HyperextSpectralSequence` (Worker 61):
  `hyperextSpectralSequence`, `opTStructure`, `heartPiece`.
- `Langlands.Cohomology.HyperextAbutmentFiltration` (Worker 61):
  `HyperextAbutment.graded`.
- Mathlib `Algebra.Homology.DerivedCategory.Ext.Basic` (`Abelian.Ext`,
  `HasExt`) and `Algebra.Homology.DerivedCategory.TStructure`
  (`DerivedCategory.TStructure.t`).

## Not stated here

- The canonical isomorphisms `E_∞^{p,q} ≅ gr^p`, their naturality, and
  canonical forms of the covariant identifications.
- A comparison of Worker 61's spectral sequence with Cartan and Eilenberg's
  second spectral sequence when `B` is not in the heart, and the first
  spectral sequence.
- Tohoku's edge homomorphisms (5.2.6)–(5.2.7), the five-term exact sequences
  (5.2.8)–(5.2.9), and the spectral sequences through the orbit space.
- The identification of `Ext^p_{Rep R G}(R, -)` with Mathlib's group
  cohomology.
