# Root data of split maximal tori, and the root datum of `GL_n`

Worker 274.

This module defines the predicate saying that a Mathlib root datum is the root
datum of a homomorphism `i : T ⟶ G` from a commutative group scheme over a field.
It also builds the `GL_n` data: the diagonal torus, the standard root datum on its
lattices, and the permutation action of `S_n` on characters.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- §21.c with Theorem 21.11, printed pp.428–429 (PDF 444–445): the root datum
  `(X(T), Φ(G, T), α ↦ α^∨)` of a split reductive group. The reflection `s_α` of
  21.11(e) is represented by a point `n_α ∈ N_G(T)(k)` (21.11(d)) and satisfies
  `s_α(x) = x − ⟨x, α^∨⟩ α`.
- Appendix C, Definition C.28, printed p.613 (PDF 629): root data
  `(X, R, α ↦ α^∨)` with `⟨α, α^∨⟩ = 2`, `s_α(R) ⊆ R` and finite Weyl group.
- Example 17.88, printed p.380 (PDF 396): the diagonal torus `D_n` of `GL_n`.
- Example 21.6, printed p.426 (PDF 442): `X(D_n) = ⨁ ℤ χᵢ` with
  `χᵢ(diag(t₁, …, tₙ)) = tᵢ`, and the roots of `(GL_n, D_n)` are
  `eᵢ − eⱼ` for `i ≠ j`.
- Example 21.40, printed p.436 (PDF 452): permutation matrices normalize `D_n`
  and act by permuting the diagonal entries, and `W(GL_n, D_n) ≅ S_n`.

The target structure is Mathlib's `RootDatum` (`RootPairing ι ℤ X^* X_*`), which
packages the roots and coroots as embeddings indexed by a type, a perfect
pairing, and the reflection permutations. The bridge from Milne's root datum to
this structure is **derived**. So are the definition of `diagonalTorus` over an
arbitrary base ring `R`, with its point formula over every test scheme, and its
compatibility with the published `diagonalCocharacter`.

## The root-datum predicate

For a field `k`, `T : CommGroupScheme (Spec k)`, `G` with
`IsAffineHom G.X.hom`, `i : T.toGrp ⟶ G` and
`P : RootDatum J (characterLattice T) (cocharacterLattice T)`,
`IsRootDatumOf i P` is the conjunction of three conditions:

- `P.toLinearMap = latticePairing T`;
- `Set.range P.root = roots i`, the roots defined through the actual adjoint
  representation (module `Langlands.GroupScheme.Torus.Weights`);
- for every `α : J` there are a base point `n` and an automorphism `σ : T ≅ T`
  with `IsNormalizingPoint i n σ` and `characterAut σ = P.reflection α`, that is,
  the induced map `χ ↦ σ⁻¹ ≫ χ` is the reflection of `α`.

## The diagonal torus

Let `n : Type` be finite with decidable equality, and let `R : CommRingCat.{u}`.

- `isAffineHom_groupScheme_of k` restates the published instance
  `isAffineHom_groupScheme` for the base `Spec (CommRingCat.of k)`, where
  instance search does not find the generic instance.
- `diagonalTorusUnits n A : (ULift n → Aˣ) →* GL n A` sends `t` to
  `diag(t ⟨i⟩)` (`coe_diagonalTorusUnits`). It is compatible with ring
  homomorphisms (`map_diagonalTorusUnits`).
- `diagonalTorusPoints n R T` sends a point `x` of the split torus over a test
  scheme `T` to the point of `GL_n` whose matrix is `diag(tᵢ)`, where
  `(tᵢ) = splitTorus.pointsEquiv x`. It is natural in `T`
  (`diagonalTorusPoints_naturality`).
- `diagonalTorus n R : (splitTorus.commGroupScheme (Spec R) (ULift n)).toGrp ⟶
  groupScheme n R` is the homomorphism with these points (published
  `homOfPoints`). The point formula is `pointsEquiv_diagonalTorus`, and
  `pointsEquiv_diagonalTorus_val` gives it as an equality of matrices.
- The instances `mono_diagonalTorus_hom` and `mono_diagonalTorus_left` say that
  `diagonalTorus` is a monomorphism over `Spec R` and that its underlying
  morphism of schemes is a monomorphism. The first holds because a diagonal
  matrix determines its diagonal entries. The second follows by
  `Over.mono_left_of_mono`. This is the hypothesis of `weylAction`.
- `comp_diagonalTorus_eq_diagonalCocharacter`: a cocharacter `ν` of the split
  torus acting on points by `s ↦ (s^{eᵢ})ᵢ`, followed by `diagonalTorus`, is the
  published `diagonalCocharacter n R e`. Over a domain `k`, the special case
  `cocharacterLatticeEquiv_symm_comp_diagonalTorus` says that the cocharacter
  `(cocharacterLatticeEquiv k (ULift n)).symm e`, followed by `diagonalTorus`,
  is `diagonalCocharacter n k e`.

## Coordinates, roots and the root datum

Over a field `k`, write `𝔻` for `splitTorus.commGroupScheme (Spec k) (ULift n)`.

- `characterCoordEquiv n k : characterLattice 𝔻 ≃ₗ[ℤ] (n → ℤ)` and
  `cocharacterCoordEquiv n k` are `characterLatticeEquiv` and
  `cocharacterLatticeEquiv` (indexed by `ULift n`) followed by reindexing along
  `ULift n ≃ n` (`characterCoordEquiv_apply`, `characterLatticeEquiv_eq` and
  their cocharacter versions). In these coordinates `latticePairing` is the dot
  product over `n` (`latticePairing_coord`).
- `rootCoord (i, j) = eᵢ − eⱼ ∈ ℤ^n`. The lemmas `sum_rootCoord_mul` and
  `sum_mul_rootCoord` compute its dot products. `rootCoord_injective` says it is
  injective on pairs with `i ≠ j`. `sub_smul_rootCoord` gives, for `i ≠ j`,
  `x − (xᵢ − xⱼ)(eᵢ − eⱼ) = x ∘ (i j)`, and `rootCoord_swap` describes how the
  transposition `(i j)` acts on the vectors `eₐ − e_b`.
- `reflectionPermEquiv p` is the permutation of `{(a, b) | a ≠ b}` induced by
  the transposition of the two entries of `p`.
- `rootDatum n k : RootDatum {p : n × n // p.1 ≠ p.2} (characterLattice 𝔻)
  (cocharacterLattice 𝔻)` has three components:
  - pairing `latticePairing 𝔻`, perfect by `splitTorus.isPerfPair_latticePairing`
    (`rootDatum_toLinearMap`);
  - root of `(i, j)` equal to `eᵢ − eⱼ` and coroot equal to `eᵢ^∨ − eⱼ^∨`, in
    the coordinates of `characterLatticeEquiv` and `cocharacterLatticeEquiv`
    (`characterLatticeEquiv_rootDatum_root`,
    `cocharacterLatticeEquiv_rootDatum_coroot`; also in the `n`-coordinates by
    `characterCoordEquiv_rootDatum_root` and
    `cocharacterCoordEquiv_rootDatum_coroot`);
  - `⟨eᵢ − eⱼ, eᵢ^∨ − eⱼ^∨⟩ = 2`, with the reflection permutations given by
    `reflectionPermEquiv`, since the reflection along `eᵢ − eⱼ` swaps the
    coordinates `i` and `j`.

## The permutation action

`permutationAction n k : Equiv.Perm n →* (characterLattice 𝔻 ≃ₗ[ℤ]
characterLattice 𝔻)` sends `w` to the automorphism whose coordinates are
`m ↦ m ∘ w⁻¹`, a left action (`characterCoordEquiv_permutationAction`). Under
`characterLatticeEquiv` it permutes the coordinates:
`c ↦ m ⟨w⁻¹ c.down⟩` (`characterLatticeEquiv_permutationAction`).
`rootDatum_reflection` shows that the reflection of the root `eᵢ − eⱼ` is
`permutationAction n k (Equiv.swap i j)`.
