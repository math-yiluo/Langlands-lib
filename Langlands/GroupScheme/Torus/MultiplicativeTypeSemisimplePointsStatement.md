# Multiplicative type via semisimple geometric points

`Langlands.GroupScheme.MultiplicativeTypeSemisimplePointsStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]` and
`[IsAffineHom G.X.hom]`. Write `kᵃ = AlgebraicClosure k` and
`Kᵃ = CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)`. If
`IsCommMonObj G.X`, then

```text
IsMultiplicativeType G ↔
  ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
    (x : (algSpec (CommRingCat.of k)).obj (op Kᵃ) ⟶ G.X),
    Module.End.IsSemisimple
      (Matrix.toLin' (ρ.affineMatrix Kᵃ x : Matrix (Fin n) (Fin n) kᵃ)).
```

In words: a smooth commutative affine group scheme `G` over `k` is of
multiplicative type if and only if every element of `G(kᵃ)` is semisimple,
in the sense that it acts by a semisimple endomorphism of `(kᵃ)ⁿ` in every
representation of `G` on `kⁿ`.

The ingredients are existing declarations, used without change.

- `Smooth G.X.hom` (Mathlib, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`)
  says that the structure morphism `G → Spec k` is smooth. Mathlib provides
  an instance deriving `LocallyOfFinitePresentation` from `Smooth`, so `G` is
  locally of finite type over `k`.
- `IsCommMonObj G.X` (Mathlib, `Mathlib.CategoryTheory.Monoidal.Mon`) says
  that the multiplication of `G` composed with the swap of the two factors of
  `G × G` is the multiplication again: `G` is commutative.
- `IsMultiplicativeType G` (from
  [`Torus.MultiplicativeType`](MultiplicativeType.md)) says that there are a
  field `K : Type u` with `Algebra k K`, a finitely generated commutative
  group `Λ : Type u` and an isomorphism of group schemes from the base change
  of `G` along `Spec.map (CommRingCat.ofHom (algebraMap k K))` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ` (from
  [`Torus.Diagonalizable`](Diagonalizable.md)), the diagonalizable group
  `D(Λ) = Spec K[Λ]`.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis.
- `algSpec (CommRingCat.of k)` (Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine`)
  is `Spec` as a functor from commutative `k`-algebras to schemes over
  `Spec k`. So `x` ranges over the morphisms `Spec kᵃ → G` over `Spec k`:
  the points of `G` with values in `kᵃ`, that is, the elements of `G(kᵃ)`.
- `ρ.affineMatrix Kᵃ x` (from `MatrixRepresentation`) is the invertible
  matrix with entries in `kᵃ` that corresponds to the point `x ≫ ρ` of
  `GL_n` with values in `kᵃ`. It is the matrix `ρ(x)` by which `x` acts on
  `(kᵃ)ⁿ` in the base change of `ρ` to `kᵃ`.
- `Matrix.toLin'` turns this matrix into a `kᵃ`-linear endomorphism of
  `Fin n → kᵃ`, and `Module.End.IsSemisimple` (Mathlib,
  `Mathlib.LinearAlgebra.Semisimple`) says that `(kᵃ)ⁿ` is a semisimple
  module over the polynomial ring `kᵃ[X]` with `X` acting by this
  endomorphism, equivalently that every invariant subspace has an invariant
  complement. For an endomorphism of a finite-dimensional vector space over a
  field, Mathlib proves that this holds exactly when the minimal polynomial is
  squarefree (`Module.End.IsSemisimple.minpoly_squarefree` and
  `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`). Over the
  algebraically closed field `kᵃ`, a squarefree polynomial is a product of
  distinct linear factors, so this says that `ρ(x)` is diagonalizable.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Corollary 12.21, printed p. 238: "A smooth commutative
algebraic group G is of multiplicative type if and only if G(k^a) consists
of semisimple elements." Its proof is on printed p. 239 and is summarized in
the last section.

Conventions and definitions used:

- Notations, printed p. 3: "The symbol k^a denotes an algebraic closure of
  k". The Lean statement uses Mathlib's algebraic closure
  `AlgebraicClosure k`; any two algebraic closures of `k` are isomorphic over
  `k`, so the condition does not depend on this choice.
- Algebraic groups. Printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k". Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k." Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Smoothness. Printed p. 13: "An algebraic scheme X over an algebraically
  closed field k is said to be smooth if all x ∈ |X| are smooth, and an
  algebraic scheme X over an arbitrary field k is said to be smooth if X_{k^a}
  is smooth." A.56, printed p. 579: "An algebraic scheme X over a field k is
  smooth if and only if, for all k-algebras R and ideals I in R such that
  I² = 0, the map X(R) → X(R/I) is surjective". This is the usual notion of
  smoothness for schemes of finite type over a field, which is Mathlib's
  `Smooth` for the structure morphism.
- Commutative. Definition 1.24, printed p. 12: "An algebraic group (G, m) is
  commutative if m ∘ t = m, where t is the transposition map".
- Multiplicative type. Definition 12.17, printed p. 236: "An algebraic group
  over k is of multiplicative type if it becomes diagonalizable over some
  field containing k." Definition 12.7, printed p. 233: "An algebraic group G
  is diagonalizable if the group-like elements in O(G) span it as a k-vector
  space." Theorem 12.8 (same page): "An algebraic group G is diagonalizable if
  and only if it is isomorphic to D(M) for some commutative group M." Theorem
  12.9(a) (same page): "The functor M ⇝ D(M) is a contravariant equivalence
  from the category of finitely generated commutative groups to the category
  of diagonalizable algebraic groups".
- Semisimple endomorphisms, printed p. 166: "Recall that an endomorphism α of
  a vector space V over k is diagonalizable if V has a basis of eigenvectors
  for α, and that it is semisimple if it becomes diagonalizable after an
  extension of k." and "From linear algebra, we know that α is semisimple if
  and only if no irreducible factor of its minimum polynomial m_α(T) has a
  multiple root".
- Semisimple elements. Theorem 9.18, printed p. 170: "Let G be an algebraic
  group over a perfect field k, and let g ∈ G(k). Then there exist unique
  elements g_s, g_u ∈ G(k) such that, for every representation (V, r_V) of G,
  r_V(g_s) = r_V(g)_s and r_V(g_u) = r_V(g)_u." Then 9.19, printed p. 171:
  "Let G be an algebraic group over a perfect field k. An element g of G(k)
  is said to be semisimple (resp. unipotent) if g = g_s (resp. g = g_u).
  Thus, g is semisimple (resp. unipotent) if r(g) is semisimple (resp.
  unipotent) for one faithful representation (V, r) of G, in which case r(g)
  is semisimple (resp. unipotent) for all representations r of G." For
  `G(kᵃ)`, this is applied to `G_{kᵃ}` over the perfect field `kᵃ`.
- Representations. Chapter 4 opens, printed p. 83, with "Throughout this
  chapter, G is an affine algebraic group over a field k." On the same page:
  "A linear representation of G is a homomorphism r: G → GL_V of group-valued
  functors." and "A linear representation r is faithful if
  r(R): G(R) → Aut_{R-linear}(V_R) is injective for all k-algebras R."
  Theorem 4.9, printed p. 87: "The regular representation has a faithful
  finite-dimensional subrepresentation." Printed p. 41: "If V has finite
  dimension n, then the choice of a basis for V determines an isomorphism
  GL_V → GL_n".

The provenance is derived for these reasons:

- The group. Milne's `G` is a smooth commutative affine group scheme of
  finite type over `k`. The Lean statement assumes `[IsAffineHom G.X.hom]`
  (the affineness convention of Chapter 12) and `[Smooth G.X.hom]`. A smooth
  morphism is locally of finite presentation, and `Spec k` is quasi-compact
  and `G` is affine over it, so `G` is of finite type over `k`; for this
  reason no separate `LocallyOfFiniteType` hypothesis is stated.
  Commutativity is Definition 1.24: `IsCommMonObj G.X` is the equation
  `m ∘ t = m` in the category of schemes over `Spec k`.
- Multiplicative type. `IsMultiplicativeType G` asks that `G_K ≅ D(Λ)` for
  some field `K` containing `k` and some finitely generated `Λ`. For an
  algebraic group, "diagonalizable over `K`" (Definition 12.7) means, by
  Theorems 12.8 and 12.9(a), `G_K ≅ D(Λ)` with `Λ = X(G_K)` finitely
  generated, so asking for finitely generated `Λ` is no restriction.
- Semisimple elements. Milne's condition is that every `g ∈ G(kᵃ)` is a
  semisimple element of `G_{kᵃ}` (9.19 over the perfect field `kᵃ`). The
  Lean condition is that `ρ(g)` is semisimple for every representation `ρ`
  of `G` over `k` on some `kⁿ`, where `ρ(g)` is computed in the base change
  `ρ_{kᵃ}`, a representation of `G_{kᵃ}`. The two agree:
  - If `g` is semisimple in Milne's sense, then `r(g)` is semisimple for all
    representations `r` of `G_{kᵃ}` (9.19), in particular for every `ρ_{kᵃ}`.
  - Conversely, Theorem 4.9 gives a faithful finite-dimensional
    representation of `G`; after a choice of basis it is some
    `ρ : MatrixRepresentation G (Fin n)`. Its base change `ρ_{kᵃ}` is again
    faithful: a `kᵃ`-algebra `R` is also a `k`-algebra, `G_{kᵃ}(R) = G(R)`,
    and `ρ_{kᵃ}(R) = ρ(R)` is injective. If `ρ_{kᵃ}(g)` is semisimple, then
    `g` is semisimple by 9.19 ("for one faithful representation").
- Semisimple endomorphisms. Over the algebraically closed field `kᵃ`,
  Milne's definition (p. 166) says that `ρ(g)` is diagonalizable, and his
  criterion says that its minimal polynomial has no multiple root. Mathlib's
  `Module.End.IsSemisimple` is equivalent to the minimal polynomial being
  squarefree (see the list of ingredients), and over `kᵃ` these conditions
  coincide.
- `k`, `G`, `kᵃ`, `K`, `Λ` lie in one universe `u`. This is a formalization
  convention.

The hypotheses are needed. Commutativity: over a field of characteristic
zero, a finite constant group that is not commutative is smooth, and each of
its points has finite order, so it acts in every representation by a matrix
of finite order, which is semisimple in characteristic zero; but it is not
of multiplicative type, since groups of multiplicative type are commutative.
Smoothness: over a field of characteristic `p > 0`, the group `α_p` (the
kernel of Frobenius on `𝔾ₐ`) is commutative and has only one `kᵃ`-point, the
identity, which acts trivially in every representation; but the inclusion
`α_p → 𝔾ₐ` is a nonzero homomorphism, so by Milne's Theorem 12.18(b)
(printed p. 237: "(a) G is of multiplicative type; (b) G is commutative and
Hom(G, Ga) = 0") `α_p` is not of multiplicative type.

Relation to the Library. The Library has no Lean notion of semisimple
elements of `G(kᵃ)` and, apart from this module, no statement of Corollary
12.21. The Lean condition
follows the pattern of `Lie.IsSemisimpleElement` (in
[`Lie.SemisimpleElement`](../Lie/SemisimpleElement.md)), which tests
semisimplicity of an element of the Lie algebra in every representation
`MatrixRepresentation G (Fin n)` after extension of scalars to
`AlgebraicClosure k`; here the elements are points of `G` itself. Milne
continues after the proof of 12.21: "Later (17.25), we shall show that every
smooth connected algebraic group such that G(k^a) consists of semisimple
elements is a torus." The Library's `NoUnipotentSubgroupTorusStatement` (in
[`Absolute.NoUnipotentSubgroupTorusStatement`](../Absolute/NoUnipotentSubgroupTorusStatement.md))
is a different sentence of Corollary 17.25 (no nontrivial connected
unipotent subgroup variety, over an algebraically closed field).

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Corollary 12.21 on
printed p. 238 and its proof on p. 239 with the same wording, 9.18 and 9.19
on pp. 170–171 with the same wording, and the definition of faithful
representations on p. 83 and Theorem 4.9 on p. 87 with the same wording. On
p. 166 it reads "An endomorphism α of a vector space V over k is
diagonalizable if V has a basis of eigenvectors for α, and it is semisimple
if it becomes diagonalizable after an extension of k." (2017: "Recall
that …").

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 12, corrections on p. 244 (12.41) and p. 249 (proof of 12.57) only;
for Chapter 9, corrections on p. 173 (9.25) and p. 181 (proof of 9.44) only;
for Chapter 4, one correction on p. 95 (proof of 4.29). It has no entry for
printed pp. 3, 6, 12, 13, 41, 83, 87, 166, 170, 171, 230, 233, 234, 235, 236,
237, 238, 239 or 579. The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 12, one entry, on p. 234 (Example 12.10), and for Chapter 4 one
entry, on p. 89 (proof of 4.14); it has no entry for printed pp. 83, 87, 166,
170, 171, 238 or 239.

## For the proof (not part of this module)

The Library proves the statement as
`Langlands.GroupScheme.multiplicativeTypeSemisimplePoints` in
[`MultiplicativeTypeSemisimplePointsProof`](MultiplicativeTypeSemisimplePointsProof.md).

Milne's proof, printed p. 239: "We may suppose that k is algebraically
closed. Choose a faithful finite-dimensional representation (V, r) of G, and
identify G with r(G). If G is of multiplicative type, then there exists a
basis of V for which G ⊂ D_n, from which it follows that the elements of
G(k) are diagonalizable (hence semisimple). Conversely, if the elements of
G(k) are semisimple, they form a commuting set of diagonalizable
endomorphisms of V, and we know from linear algebra that there exists a
basis for V such that G(k) ⊂ D_n(k). Because G is smooth, this implies that
G ⊂ D_n." Here `D_n` is the group of invertible diagonal matrices (printed
p. 234). A proof of the Lean statement can follow these steps.

- Reduction to `kᵃ`. `G` is of multiplicative type if and only if `G_{kᵃ}`
  is diagonalizable: one direction is the definition; for the other, a group
  of multiplicative type splits over `k^s ⊆ kᵃ` (Theorem 12.18(d)). The
  `kᵃ`-points of `G` are the `kᵃ`-points of `G_{kᵃ}`.
- (⇒) If `G_{kᵃ}` is diagonalizable, then for every representation `ρ` of `G`
  the base change `ρ_{kᵃ}` is diagonalizable (Theorem 12.12, printed
  pp. 234–235): `(kᵃ)ⁿ` is the direct sum of the subspaces on which `G_{kᵃ}`
  acts through a character `χ`. A point `x` acts on each of these subspaces
  by the scalar `χ(x)`, so `ρ(x)` is diagonalizable, hence semisimple. This
  direction needs neither smoothness nor commutativity.
- (⇐) Choose a faithful `ρ : MatrixRepresentation G (Fin n)` over `k`
  (Theorem 4.9); its base change `ρ_{kᵃ}` is faithful, as explained in the
  provenance section. The matrices `ρ(x)`, `x ∈ G(kᵃ)`, commute with each other because `G` is
  commutative, and each is diagonalizable by hypothesis, so there is
  `P ∈ GL_n(kᵃ)` with `P ρ(x) P⁻¹` diagonal for all `x ∈ G(kᵃ)`. The
  inverse image of the conjugate `P⁻¹ D_n P` under `ρ_{kᵃ}` is a closed
  subgroup scheme of `G_{kᵃ}` containing every `kᵃ`-point. Since `G_{kᵃ}`
  is smooth over the algebraically closed field `kᵃ`, it is reduced and its
  `kᵃ`-points are dense, so this closed subscheme is all of `G_{kᵃ}` (this
  is the step "Because G is smooth"). As `ρ_{kᵃ}` is a closed immersion
  (faithful, p. 83 and 3.35), `G_{kᵃ}` is isomorphic to an algebraic
  subgroup of `D_n ≅ D(ℤⁿ)`, hence diagonalizable by Theorem 12.9(c)
  (printed p. 233: "Algebraic subgroups and quotient groups of
  diagonalizable algebraic groups are diagonalizable"). So `G` is of
  multiplicative type.
- Milne's Theorem 12.18 is `MultiplicativeTypeCharacterizationStatement` (in
  [`MultiplicativeTypeCharacterizationStatement`](MultiplicativeTypeCharacterizationStatement.md)),
  proved as `multiplicativeTypeCharacterization` in
  [`MultiplicativeTypeCharacterizationProof`](MultiplicativeTypeCharacterizationProof.md).
