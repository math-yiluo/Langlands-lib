# Characterizations of groups of multiplicative type over a field

`Langlands.GroupScheme.MultiplicativeTypeCharacterizationStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `Ks : Type u`
be a field with `[Algebra k Ks]` and `[IsSepClosure k Ks]`. (The `haveI` before
the list only supplies the instance `IsAffine G.X.left`, by
Mathlib's `isAffine_of_isAffineHom`; it is needed to form the coordinate Hopf
algebra in condition (c).) Then the following four conditions are equivalent
(`List.TFAE`):

- (a) `IsMultiplicativeType G`.
- (b) `IsCommMonObj G.X` and
  `Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)`.
- (c) `IsCommMonObj G.X`, and for every element `c` of
  `AffineCoordinates.hopfAlgebra G` there is a subcoalgebra
  `D : Subcoalgebra k (AffineCoordinates.hopfAlgebra G)` with `c ∈ D`,
  `FiniteDimensional k D`, `Coalgebra.IsCocomm k D`, and
  `Algebra.Etale k (WithConv (D →ₗ[k] k))`.
- (d) There are `Λ : Type u` with `AddCommGroup Λ` and `AddGroup.FG Λ` and an
  isomorphism of group schemes over `Spec Ks` from
  `(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ks)))).obj G`
  onto `(Diagonalizable.groupScheme (CommRingCat.of Ks) Λ).toGrp`.

In words: for an affine group scheme `G` of finite type over `k`, the
following are equivalent: (a) `G` is of multiplicative type; (b) `G` is
commutative and `Hom(G, 𝔾ₐ) = 0`; (c) `G` is commutative and `O(G)` is
coétale; (d) `G` becomes diagonalizable over `kˢ`.

The ingredients are existing declarations, used without change.

- `IsMultiplicativeType G` (from [`Torus.MultiplicativeType`](MultiplicativeType.md))
  says that there are a field `K : Type u` with `Algebra k K`, a finitely
  generated commutative group `Λ : Type u` and an isomorphism of group
  schemes from the base change of `G` along
  `Spec.map (CommRingCat.ofHom (algebraMap k K))` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ`. Condition (d) is the
  same condition with `K` fixed to be `Ks`.
- `Diagonalizable.groupScheme R Λ` (from [`Torus.Diagonalizable`](Diagonalizable.md))
  is the diagonalizable group `D(Λ) = Spec R[Λ]` over `Spec R`. `.toGrp`
  forgets that it is commutative.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along a morphism of base schemes.
- `IsCommMonObj G.X` (Mathlib, `Mathlib.CategoryTheory.Monoidal.Mon`) says
  that the multiplication of `G` composed with the swap of the two factors of
  `G × G` is the multiplication again: `G` is commutative.
- `VectorGroup.groupScheme (CommRingCat.of k) 1` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐ¹ = 𝔾ₐ` over `Spec k`. It is the spectrum of the polynomial ring
  `MvPolynomial (Fin 1) k` and has points `Fin 1 → A` with addition over
  each commutative `k`-algebra `A`. A morphism `G ⟶ 𝔾ₐ` in
  `GroupScheme (Spec k)` is a homomorphism of group schemes. The trivial
  homomorphism always exists, so `Subsingleton (G ⟶ 𝔾ₐ)` says that it is
  the only one: `Hom(G, 𝔾ₐ) = 0`.
- `AffineCoordinates.hopfAlgebra G` (from
  [`AffineHopfCoordinates`](../AffineHopfCoordinates.md)) is a commutative
  Hopf `k`-algebra, chosen by the Library, together with an isomorphism of
  group schemes `hopfSpecIso` from its relative spectrum onto `G` that
  preserves the multiplication, identity and inverse. Relative spectrum is an
  anti-equivalence between commutative Hopf algebras and affine group
  schemes, so this Hopf algebra is the coordinate Hopf algebra `O(G)` of `G`
  up to isomorphism of Hopf algebras. Condition (c) is invariant under
  coalgebra isomorphisms, so the choice does not matter.
- `Subcoalgebra k C` (from
  [`RingTheory.Coalgebra.Subcoalgebra.Basic`](../../RingTheory/Coalgebra/Subcoalgebra/Basic.md))
  is a `k`-submodule `D` of a coalgebra `C` with `Δ(D) ⊆ D ⊗ D`. Over a
  field its carrier is a coalgebra with the restricted comultiplication and
  counit (instance `instCoalgebra`).
- `Coalgebra.IsCocomm k D` (Mathlib, `Mathlib.RingTheory.Coalgebra.Basic`)
  says that the comultiplication of `D` followed by the swap
  `D ⊗ D → D ⊗ D` is the comultiplication again. Its condition is a
  proposition; the existential `∃ _ : Coalgebra.IsCocomm k D, …` only states
  it and makes it available as an instance for the next item.
- `WithConv (D →ₗ[k] k)` (Mathlib, `Mathlib.RingTheory.Coalgebra.Convolution`)
  is the linear dual `D^∨` with the convolution product
  `f * g = mul' ∘ (f ⊗ g) ∘ Δ` and unit `ε`, a `k`-algebra; when `D` is
  cocommutative it is a commutative ring (instance `convCommRing`). This is
  Milne's algebra structure (77) on `C^∨`: multiplication
  `C^∨ ⊗ C^∨ ↪ (C ⊗ C)^∨ → C^∨` by the dual of `Δ`, and structure map the
  dual of `ε`.
- `Algebra.Etale k A` (Mathlib, `Mathlib.RingTheory.Etale.Basic`) says that
  `A` is formally étale and of finite presentation over `k`. Over a field
  (Mathlib, `Algebra.Etale.iff_exists_algEquiv_prod`) this holds exactly when
  `A` is a finite product of finite separable field extensions of `k`.
- `IsSepClosure k Ks` (Mathlib, `Mathlib.FieldTheory.IsSepClosed`) says that
  `Ks` is separably closed and separable algebraic over `k`: `Ks` is a
  separable closure of `k`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Theorem 12.18, printed p. 237:

"The following conditions on an algebraic group G over k are equivalent:
(a) G is of multiplicative type;
(b) G is commutative and Hom(G, Ga) = 0;
(c) G is commutative and O(G) is coétale;
(d) G becomes diagonalizable over kˢ."

Conventions used:

- Notations, printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k". Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k."
- Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Definition 1.2, printed p. 7: a homomorphism of algebraic groups is a
  regular map compatible with the multiplications, and "a homomorphism
  G → G′ is trivial if it factors through e′". Definition 1.24, printed
  p. 12: "An algebraic group (G, m) is commutative if m ∘ t = m, where t is
  the transposition map".
- Definition 12.7, printed p. 233: "An algebraic group G is diagonalizable
  if the group-like elements in O(G) span it as a k-vector space." Theorem
  12.8 (same page): "An algebraic group G is diagonalizable if and only if it
  is isomorphic to D(M) for some commutative group M." Theorem 12.9(a) (same
  page): "The functor M ⇝ D(M) is a contravariant equivalence from the
  category of finitely generated commutative groups to the category of
  diagonalizable algebraic groups".
- Definition 12.17, printed p. 236: "An algebraic group over k is of
  multiplicative type if it becomes diagonalizable over some field
  containing k."
- Coalgebras, printed pp. 236–237: "Recall (p. 174) that a coalgebra over k
  is a k-vector space C equipped with a pair of k-linear maps Δ: C → C ⊗ C,
  ε: C → k such that the diagrams (17), p. 65, commute. The linear dual C^∨
  of C becomes an associative algebra over k with the multiplication
  C^∨ ⊗ C^∨ ↪ (C ⊗ C)^∨ → C^∨ (77) and the structure map k ≃ k^∨ → C^∨."
  In the display (77) the first arrow is labelled "can." and the second
  "Δ^∨"; the arrow of the structure map is labelled "ε^∨". Then: "We say
  that C is coétale if it is finite-dimensional and C^∨ is commutative and
  étale. More generally, we say that a coalgebra is coétale if it is a
  directed union of finite-dimensional coétale subcoalgebras."
- Étale algebras, A.57 and A.59, printed p. 579: "A k-algebra A is said to
  be diagonalizable if it is isomorphic to the product algebra kⁿ for some
  n ∈ ℕ, and it is étale if A ⊗ k′ is diagonalizable for some field k′
  containing k." "The following conditions on a finite k-algebra A are
  equivalent: (a) A is étale; (b) A is a product of separable field
  extensions of k; …"

The provenance is derived for these reasons:

- The group. Milne's `G` is an affine group scheme of finite type over `k`.
  The Lean statement assumes `[IsAffineHom G.X.hom]` (the affineness
  convention of Chapter 12) and `[LocallyOfFiniteType G.X.hom]`; since
  `Spec k` is quasi-compact and `G` is affine over it, the two together say
  that `G` is of finite type over `k`.
- (a) and (d). `IsMultiplicativeType G` asks that `G_K ≅ D(Λ)` for some
  field `K` containing `k` and some finitely generated `Λ`; condition (d)
  asks this for `K = Ks`. For a group of finite type, "diagonalizable over
  `K`" (Definition 12.7) means, by Theorems 12.8 and 12.9(a), `G_K ≅ D(Λ)`
  with `Λ = X(G_K)` finitely generated, so asking for finitely generated `Λ`
  is no restriction. `kˢ` is an arbitrary separable closure `Ks`.
- (b). Commutativity is Definition 1.24 (`IsCommMonObj` is the equation
  `m ∘ t = m` in the category of schemes over `Spec k`). `Hom(G, 𝔾ₐ) = 0`
  says that every homomorphism `G → 𝔾ₐ` is the trivial homomorphism, which
  is `Subsingleton` of the hom-set.
- (c). `O(G)` is represented by the Library's coordinate Hopf algebra (see
  above). Milne's "directed union of finite-dimensional coétale
  subcoalgebras" is expressed as "every element lies in a
  finite-dimensional coétale subcoalgebra". A directed union has this
  property. Conversely, if every element lies in such a subcoalgebra, then
  the finite-dimensional coétale subcoalgebras form a directed family with
  union `O(G)`: for two of them `D₁, D₂`, the sum `D₁ + D₂` is a
  finite-dimensional subcoalgebra, it is cocommutative because its
  comultiplication is symmetric on `D₁` and on `D₂`, and restriction makes
  its dual a `k`-subalgebra of `D₁^∨ × D₂^∨`. A subalgebra of a finite étale
  algebra over a field is étale (A.59(c): reducedness after every field
  extension passes to subalgebras), so `D₁ + D₂` is coétale.
- Coétale for a finite-dimensional `D`. Milne asks that `D^∨` be commutative
  and étale. The Lean statement asks that `D` be cocommutative and that
  `D^∨` (with the convolution product, which is Milne's product (77)) be
  étale in Mathlib's sense. For finite-dimensional `D`, `D^∨` is
  commutative if and only if `D` is cocommutative: `(f * g)(d)` and
  `(g * f)(d)` are the values of `f ⊗ g` on `Δ(d)` and on its swap, and
  the functionals `f ⊗ g` separate the points of `D ⊗ D`. Mathlib's
  `Algebra.Etale` on the finite commutative algebra `D^∨` is Milne's
  étaleness, by A.59(a)⇔(b) and `Algebra.Etale.iff_exists_algEquiv_prod`.
- `k`, `Ks`, `G` and `Λ` lie in one universe `u`. This is a formalization
  convention.

Relation to the Library. The Library has (a) ⇒ (d) for a finite Galois
extension in place of `Ks` as `MultiplicativeTypeFiniteGaloisSplittingStatement`
(in [`Torus.MultiplicativeTypeFiniteGaloisSplittingStatement`](MultiplicativeTypeFiniteGaloisSplittingStatement.md),
Milne's Corollary 12.19) and a pure-coalgebra descent step of (c) ⇒ (d) as
`SeparablyClosedGroupLikeSpanningStatement` (in
[`RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningStatement`](../../RingTheory/Coalgebra/SeparablyClosedGroupLikeSpanningStatement.md)).
Apart from this module, it has no statement of the equivalences of Theorem
12.18 and no statement relating multiplicative type to `Hom(G, 𝔾ₐ)` or to
coétale coordinate coalgebras.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Theorem 12.18 on
printed p. 237 with the same wording, and Definition 12.17 on printed
p. 236 and the definition of coétale on printed p. 237, both with the same
wording.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 12, corrections on p. 244 (12.41) and p. 249 (proof of 12.57) only;
none concerns the results used here. It has no entry for printed pp. 3, 6,
7, 12 or 579. The errata snapshot of 2026-11-04 for the 2022 reprint (source
ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 12, one entry, on p. 234: in the last sentence of Example 12.10 the
base field is algebraically closed. It does not concern Theorem 12.18. None of
its other entries concerns the passages quoted here: the nearest are the
p. 7 entry, on the paragraph following Definition 1.3 (algebraic
subgroups), and the Appendix A entries (A.64 on p. 584, and a remark on
sheaves of `k`-algebras).

## For the proof (not part of this module)

The Library proves the statement as
`Langlands.GroupScheme.multiplicativeTypeCharacterization` in
[`MultiplicativeTypeCharacterizationProof`](MultiplicativeTypeCharacterizationProof.md).

Milne's proof (printed pp. 237–238) goes (a) ⇒ (b) ⇒ (c) ⇒ (d) ⇒ (a).

- (d) ⇒ (a): take `K = Ks` in `IsMultiplicativeType`.
- Base change. Homomorphisms `G → 𝔾ₐ` correspond to the primitive
  elements `f ∈ O(G)`, those with `Δ(f) = f ⊗ 1 + 1 ⊗ f`. This is a linear
  condition, so `Hom(G_{k′}, 𝔾ₐ) ≅ Hom(G, 𝔾ₐ) ⊗ k′` for every field `k′`
  containing `k`. Commutativity of `G` can also be checked after a field
  extension.
- (a) ⇒ (b): over `K`, `O(G_K) ≅ K[Λ]` has the basis `Λ` of group-like
  elements, and comparing coefficients in `Δ(f) = f ⊗ 1 + 1 ⊗ f` shows that
  `K[Λ]` has no nonzero primitive element. (Milne instead uses that a
  nontrivial `u : G → 𝔾ₐ` gives the nonsemisimple representation
  `g ↦ [[1, u(g)], [0, 1]]`, contradicting Theorem 12.12.)
- (b) ⇒ (c): `G` is commutative, so `O(G)` and all its subcoalgebras are
  cocommutative. Let `C` be a finite-dimensional subcoalgebra of `O(G)` and
  `kᵃ` an algebraic closure of `k`. Then `kᵃ ⊗ C` is a finite-dimensional
  subcoalgebra of `O(G_{kᵃ})` with dual `kᵃ ⊗ C^∨`, and `G_{kᵃ}` still
  satisfies (b). Over `kᵃ`, the commutative algebra `A = (kᵃ ⊗ C)^∨` is a
  finite product of local artinian rings with residue field `kᵃ`. If one
  factor is not a field, there is a surjection `A → kᵃ[η]` (with `η² = 0`;
  Milne writes `ε`); it has the form `x ↦ ⟨x, a⟩ + ⟨x, b⟩η` with `a, b ∈ kᵃ ⊗ C`, `b ≠ 0`,
  and multiplicativity and unitality give `Δa = a ⊗ a`,
  `Δb = a ⊗ b + b ⊗ a` and `ε(a) = 1`. Then `S(a)a = ε(a) = 1` in
  `O(G_{kᵃ})` (Milne writes "a is a unit in A"; the identity holds in the
  coordinate ring, where `a` lies), and `ba⁻¹` is a nonzero primitive
  element, contradicting (b). So `kᵃ ⊗ C^∨` is a product of copies of `kᵃ`,
  and `C^∨` is étale by A.57. Every element of a coalgebra lies in a
  finite-dimensional subcoalgebra: this is the proved
  `Subcoalgebra.LocalFinitenessStatement` (in
  [`RingTheory.Coalgebra.Subcoalgebra.LocalFinitenessStatement`](../../RingTheory/Coalgebra/Subcoalgebra/LocalFinitenessStatement.md)).
- (c) ⇒ (d): `O(G_{Ks}) = Ks ⊗ O(G)` is the union of the subcoalgebras
  `Ks ⊗ C` for the finite-dimensional coétale subcoalgebras `C` of `O(G)`,
  and the dual `Ks ⊗ C^∨` of `Ks ⊗ C` is étale over the separably closed
  field `Ks`, hence a product of copies of `Ks`. So `Ks ⊗ C` is spanned by
  group-like elements; the Library has this step as
  `span_isGroupLikeElem_eq_top_of_formallyUnramified` (in
  [`RingTheory.Coalgebra.ConvolutionDualGroupLike`](../../RingTheory/Coalgebra/ConvolutionDualGroupLike.md)).
  Hence `O(G_{Ks})` is spanned by its group-like elements, and
  `groupLikeSpecIso` (in [`AffineHopfCoordinates`](../AffineHopfCoordinates.md))
  identifies `G_{Ks}` with the spectrum of the group algebra `Ks[M]` of the
  group `M` of group-like elements. `M` is finitely generated because
  `Ks[M]` is a finitely generated `Ks`-algebra: finitely many generators
  involve only finitely many elements of `M`, and the subgroup they
  generate has the same group algebra.
