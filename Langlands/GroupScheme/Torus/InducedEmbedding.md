# Every torus over a field maps monomorphically into an induced torus

This module proves `IsTorus.exists_mono_inducedTorus`. Let `k` be a field and `T` a
commutative group scheme over `Spec k` with `IsTorus T.toGrp`. Then there are a commutative
group scheme `S` over `Spec k` and a homomorphism `φ : T ⟶ S` such that

* `S` is an induced torus (`IsInducedTorus S`), and
* the underlying morphism `(CommGroupScheme.groupHom φ).hom.hom : T.X ⟶ S.X` is a monomorphism
  in `Over (Spec k)`. Equivalently, `φ` is injective on `U`-points for every test object `U`
  over `Spec k`, so its scheme-theoretic kernel is trivial.

The module does not claim that `φ` is a closed immersion. Its consumer
(`Langlands.GroupScheme.ZExtensionPushout`) needs only the monomorphism property.

## Auxiliary declarations (namespace `InducedEmbedding`)

These use the permutation-lattice notation of the published
`Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof` (namespace
`GaloisLatticeRealization`). For a finite Galois extension `E/k` and an index type `J`, a
coordinate `c : Coord k E J` is a pair `(i, τ)` with `i : J` and `τ` a `k`-embedding of the top
intermediate field into `E`. `permRep J` is the permutation representation of `Gal(E/k)` on
`Coord k E J → ℤ`. `permTorus k E J` is the permutation torus `Res_{(∏_{i ∈ J} E)/k} 𝔾ₘ`.

* `actCoord σ c` is the coordinate `(i, σ ∘ τ)` for `c = (i, τ)`.
* `permRep_single`: `permRep J σ` sends the standard basis vector at `c` to the standard
  basis vector at `actCoord σ c`. The proof evaluates both sides with `permRep_apply`, checking
  coordinates equal to and different from `actCoord σ c` separately.
* `permTorus_isInduced`: for finite `J`, `permTorus k E J` is an induced torus. The proof
  applies the published `isInducedTorus_of_equivariant_basis` to the following data:
  * the splitting field `E`, using `permTorus_isSplit`;
  * the lattice `Coord k E J → ℤ` with the representation `permRep J`;
  * its standard basis `Pi.basisFun`;
  * the inverse of the character identification `WeilGm.productEmbeddingCharacterEquiv`.

  Equivariance of that identification is `permTorus_equiv_symm_galois`. Galois elements
  permute the basis by `permRep_single`.

## Proof of `IsTorus.exists_mono_inducedTorus`

1. **Splitting.** The published `torusFiniteGaloisSplitting` gives a finite Galois extension
   `E/k` over which `T` is split. The base change `T_E` is then isomorphic to a split torus
   with a finite index type `J`. Transporting the standard basis of `J → ℤ` gives a basis `b`
   of the character lattice `X^*(T_E)`. Write `ρ` for the Galois action on `X^*(T_E)`
   (`characterLattice.galoisRepresentation`).
2. **An equivariant surjection of lattices.** Put `R := permTorus k E J` and let `eR` identify
   `X^*(R_E)` with `Coord k E J → ℤ`. Define `F : X^*(R_E) →+ X^*(T_E)` as `sumMap ρ b ∘ eR`.
   It sends the basis vector at the coordinate `(i, τ)` to `gal(τ) · b i`.
   * `F` is Galois-equivariant, by `permTorus_equiv_galois` and `sumMap_permRep`.
   * `F` is surjective, by `sumMap_surjective_of_basis`.
3. **Descent of the dual map.** `R_E` is split (`permTorus_isSplit`), so the published
   `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap` applies to `F`. It gives a
   `k`-homomorphism `φ : T ⟶ R` whose base change pulls back every character `χ` of `R_E` to
   `F χ`.
4. **`φ` is a monomorphism.** Let `x y : U ⟶ T.X` with `x ≫ φ = y ≫ φ`. Pullback along
   `Spec E → Spec k` is faithful (`GaloisCocharacterDescent.faithful_algebraPullback`), so it
   suffices to show that the base changes `x_E` and `y_E` agree. Characters of the split
   torus `T_E` separate points (`IsSplitTorus.point_ext_characters`). Every character of `T_E`
   has the form `F χ'`, by surjectivity of `F`, and `F χ'` is the composite of the base change
   of `φ` with `χ'`. Since `x ≫ φ = y ≫ φ`, the points `x_E` and `y_E` agree after composing
   with every character, so `x_E = y_E`.
5. `R` is induced by `permTorus_isInduced`.

## Provenance

This is internal derived content. Mathematically it is the dual of a standard lattice fact:
the Galois module `X^*(T)` is a quotient of a permutation module, so `T` embeds into an
induced torus. The same device appears in Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Construction 11.4.1 (printed p. 428). There the character module of the
finite kernel `μ` is presented as a quotient of a free `Gal(ℓ/k)`-module, giving an embedding
of `μ` into an induced torus. Here the presentation is applied to a torus rather than to `μ`,
because the Library has no finite Galois splitting theorem for groups of multiplicative type.
The proof uses only the published results named above.
