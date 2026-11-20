# Isogenies of split reductive groups with the same root characters agree on the torus

`Langlands.GroupScheme.SplitIsogenyTorusRigidityStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing. It is a corrected form of Milne's Proposition 23.8: the source
statement is false in positive characteristic (see "A defect in the source"
below), and the hypothesis on roots is strengthened to the one the source's
proof uses.

## Statement

Let `k : Type u` be a field and put `S = Spec (CommRingCat.of k)`. Let
`G G' : GroupScheme S` with `IsConnectedReductive G` and
`IsConnectedReductive G'`, and assume `IsSemisimple G ∨ IsSemisimple G'`.
Let `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'` (with
`T T' : CommGroupScheme S`) satisfy `IsSplitTorus T.toGrp`,
`IsMaximalTorus i`, `IsSplitTorus T'.toGrp` and `IsMaximalTorus i'`. Let
`φ₁ φ₂ : G ⟶ G'` and `t₁ t₂ : T ⟶ T'` satisfy, for `m = 1, 2`,

- `Surjective φₘ.hom.hom.left`,
- `IsFinite (kernel φₘ).X.hom`, and
- `CommGroupScheme.groupHom tₘ ≫ i' = i ≫ φₘ`.

If `t₁ ≫ α' = t₂ ≫ α'` for every `α' ∈ roots i'`, then `i ≫ φ₁ = i ≫ φ₂`.

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` (from [`Reductive.Basic`](Basic.md)) says that
  `G` is smooth, affine and connected over `k`, with trivial geometric
  unipotent radical. `IsSemisimple G` (from
  [`Reductive.Semisimple`](Semisimple.md)) says that `G` is connected
  reductive with finite scheme-theoretic centre; that module records Milne's
  Proposition 19.10 as the source of this characterization.
- `IsSplitTorus T.toGrp` (from [`Torus.Split`](../Torus/Split.md)) says that
  `T` is isomorphic to a split torus `splitTorus S I` for a finite index
  type `I`. `IsMaximalTorus i` (from [`Torus.Maximal`](../Torus/Maximal.md))
  says that `i` is a closed subgroup, `T` is a torus, and whenever `i`
  factors as `f ≫ j` through a closed torus `j`, the map `f` is an
  isomorphism.
- `roots i'` (from [`Torus.Weights`](../Torus/Weights.md)) is the set of
  nonzero characters `α' : T' ⟶ Gm S` of `T'` whose weight space in the Lie
  algebra of `G'` is nonzero.
- A character of `T` is a morphism `T ⟶ Gm S` of commutative group schemes
  (`characterLattice T`, from [`Torus.Lattice`](../Torus/Lattice.md)), so
  `tₘ ≫ α'` is the character of `T` obtained by composing `α'` with `tₘ`.
  `CommGroupScheme.groupHom tₘ` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is
  `tₘ` viewed as a morphism of group schemes.
- `kernel φ` (from [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md))
  is the scheme-theoretic kernel of `φ`. `IsFinite` and `Surjective` are
  from Mathlib: the kernel is finite over `k`, and the underlying map of
  schemes of `φ` is surjective.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 23.8, p.487: "Let φ₁, φ₂: (G, T) → (G′, T′) be isogenies of
  split reductive groups. If one of G or G′ is semisimple and φ₁ and φ₂
  induce the same correspondence α ↔ α′ on the roots, then φ₁|T = φ₂|T."
- Its proof, p.487: "Let f₁ = X(φ₁|T) and f₂ = X(φ₂|T). We are given that
  for some one-to-one correspondence α ↔ α′: Φ ↔ Φ′, f₁(α′) = q₁(α)α and
  f₂(α′) = q₂(α)α. Because Φ is reduced, q₁(α) = q₂(α). Therefore f₁ and f₂
  agree on ZΦ′. If G′ is semisimple, then ZΦ′ has finite index in X(T′), and
  so f₁ and f₂ agree on X(T′). This implies that φ₁ and φ₂ agree on T (see
  12.9a). The proof when G is semisimple is similar."
- Section 23a, p.485: "An isogeny of split reductive groups (G, T) →
  (G′, T′) is an isogeny φ: G → G′ such that φ(T) ⊂ T′. We write φ_T for
  φ|T: T → T′."
- Proposition 23.5, p.485: "If φ: (G, T) → (G′, T′) is an isogeny of split
  reductive groups, then f ≝ X(φ_T): X(T′) → X(T) is an isogeny of root
  data. Roots α ∈ Φ and α′ ∈ Φ′ correspond if and only if φ(U_α) = U_α′, in
  which case φ(u_α(a)) = u_α′(c_α a^q(α)), all a ∈ G_a(k), (145) where c_α ∈ k^×
  and q(α) is such that f(α′) = q(α)α." Its proof says: "By definition,
  f(χ′) = χ′ ∘ φ|T for χ′ ∈ X(T′)", and it shows that q(α) is "a constant in
  p^N" and that f^∨(α^∨) = q(α)α′^∨.
- Example 23.6, p.486: "We say that an isogeny φ: G → G′ is a Frobenius
  isogeny if its kernel is equal to the kernel of the Frobenius homomorphism
  F_G: G → G^(q) for some q (see 2.28)."
- 2.23, p.46: "A homomorphism φ: G → H of connected group varieties is an
  isogeny if it is surjective (i.e., |φ| is surjective) and its kernel is
  finite."
- Chapter 21 opening, p.424: "The field k is arbitrary." and "Recall also
  that G is split if some maximal torus T is split, in which case we refer
  to the pair (G, T) as a split reductive group."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Proposition 23.8 and its
proof on p.488 with the same words, the definition of isogenies of split
reductive groups and Proposition 23.5 on p.486, Example 23.6 on p.487, 2.23
on p.46 and the quoted Chapter 21 sentences on p.424, each with the same
words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for Proposition 23.8 or 23.5,
Example 23.6, or pp.46, 424, 485, 486 or 487. The 2017 errata's nearest
Chapter 23 entry concerns the proof of 23.11 on p.488. The 2022 errata have
no entry for pp.486–488.

## A defect in the source

The source statement is false whenever `k` has characteristic `p > 0`. Take
`G = G' = SL₂` with `T = T'` the diagonal torus, `φ₁` the identity and `φ₂`
the Frobenius map `(a b; c d) ↦ (a^p b^p; c^p d^p)`. Since `x ↦ x^p` is a
ring homomorphism in characteristic `p`, `φ₂` is a homomorphism. It is
finite, hence closed, and bijective on `k̄`-points, hence surjective. Its
kernel, cut out by `a^p = d^p = 1` and `b^p = c^p = 0`, is finite. This is the
Frobenius isogeny in the sense of Example 23.6 (with q = p). Both maps send `T` into `T`, and `SL₂` is
semisimple. With `α(diag(t, t⁻¹)) = t²`, the character maps are
`X(φ₁|T)(α) = α` and `X(φ₂|T)(α) = pα`. So both isogenies induce the same
correspondence `α ↔ α`, `-α ↔ -α`, with `q₁ = 1` and `q₂ = p`. But
`φ₁|T(t) = t` and `φ₂|T(t) = t^p` differ. The failing step of the proof is
"Because Φ is reduced, q₁(α) = q₂(α)": the correspondence does not determine
the exponents `q(α)`.

The proof is correct once `f₁` and `f₂` are assumed to agree on the roots,
that is, once the correspondence and the exponents `q(α)` both agree. The
Lean statement makes exactly this assumption: `t₁ ≫ α' = t₂ ≫ α'` for every
root `α'` of `T'`. In the example the hypothesis fails, since
`t₁ ≫ α = α ≠ pα = t₂ ≫ α`. Under it, the source's argument reads as follows.

- If `G'` is semisimple, `f₁` and `f₂` agree on `ZΦ′`, which has finite index
  in `X(T′)`. As `X(T)` is torsion-free, `f₁ = f₂`, and so `t₁ = t₂` by 12.9a.
- If `G` is semisimple, write `f₁(α′) = q₁α₁` and `f₂(α′) = q₂α₂` as in 23.5,
  with `q₁, q₂ > 0`. Then `q₁α₁ = q₂α₂`. So `α₁` and `α₂` are proportional,
  and since `Φ` is reduced, `α₂ = ±α₁`. The sign `-` would give
  `(q₁ + q₂)α₁ = 0`, which is impossible because `X(T)` is torsion-free and
  roots are nonzero. So `α₁ = α₂` and `q₁ = q₂`. By 23.5, `f₁^∨` and `f₂^∨`
  then agree on every coroot `α^∨`. The coroots span a subgroup of finite
  index in the cocharacter lattice of `T` when `G` is semisimple, and the
  cocharacter lattice of `T′` is torsion-free. So `f₁^∨ = f₂^∨`, hence
  `f₁ = f₂` and `t₁ = t₂`.

In both cases `i ≫ φ₁ = groupHom t₁ ≫ i' = groupHom t₂ ≫ i' = i ≫ φ₂`.

## Derivation from the source

- **Split reductive groups.** A reductive group over `k` is
  `IsConnectedReductive`, and "`(G, T)` split" means that `T` is a maximal
  torus of `G` that is split: `IsMaximalTorus i` and `IsSplitTorus T.toGrp`.
  The same holds for `(G', T')`. The field is arbitrary. "One of `G` or `G′`
  is semisimple" is `IsSemisimple G ∨ IsSemisimple G'`.
- **Isogenies.** By 2.23 an isogeny is a homomorphism that is surjective on
  underlying spaces with finite kernel: `Surjective φₘ.hom.hom.left` and
  `IsFinite (kernel φₘ).X.hom`. The condition `φ(T) ⊂ T′` of Section 23a is
  given with an explicit restriction: `tₘ : T ⟶ T'` with
  `CommGroupScheme.groupHom tₘ ≫ i' = i ≫ φₘ`. Because `i'` is a closed
  immersion, `tₘ` is the map `φₘ|T: T → T′`.
- **Characters.** By the proof of 23.5, `X(φₘ|T)(α′) = α′ ∘ φₘ|T`. In Lean
  this is `tₘ ≫ α'`. The roots `Φ′` of `(G', T')` are `roots i'`.
- **The root hypothesis.** The source assumes that `φ₁` and `φ₂` induce the
  same correspondence `α ↔ α′`. As explained above, this is not enough. The
  Lean statement assumes instead that `X(φ₁|T)` and `X(φ₂|T)` agree on every
  root of `T′`: `t₁ ≫ α' = t₂ ≫ α'` for all `α' ∈ roots i'`. This is the
  equality "f₁ and f₂ agree on ZΦ′" that the source's proof derives and then
  uses. By 23.5 it says that the two isogenies induce the same
  correspondence with the same exponents `q(α)`.
- **Conclusion.** "`φ₁|T = φ₂|T`" is `i ≫ φ₁ = i ≫ φ₂`, equality of the two
  composites `T → G → G'`.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
