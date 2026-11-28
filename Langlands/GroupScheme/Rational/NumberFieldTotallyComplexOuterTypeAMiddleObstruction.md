# The middle Tits class of anisotropic outer type `A_{2m+1}` over totally complex fields

Module: `Langlands.GroupScheme.Rational.NumberFieldTotallyComplexOuterTypeAMiddleObstruction`.

The module states one proposition and proves nothing.

## Lean statement

```lean
def NumberFieldTotallyComplexOuterTypeAMiddleObstructionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
      [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H) (m : ℕ)
      (e : d.Vertex ≃ Fin (2 * m + 1)) (hsc : IsSimplyConnected H),
      IsAbsolutelyAlmostSimple H →
      (∀ a b, d.cartan a b = CartanMatrix.A (2 * m + 1) (e a) (e b)) →
      (∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex), d.star σ a ≠ a) →
      IsAnisotropic H →
      ∀ w : d.pinning.starFixedWeights,
        w.val = d.absoluteFundamentalCharacter hsc (e.symm ⟨m, by omega⟩) →
        d.pinning.titsObstruction hsc w ≠ 0
```

In words: let `K` be a totally complex number field and `H` an affine, locally
finite-type, simply connected, absolutely almost-simple group over `K` of outer type
`A_{2m+1}`. If `H` is anisotropic, the Tits obstruction of `H` at its middle fundamental
weight is a nonzero element of the Brauer group of `K`.

## Conventions

- **Type.** `d : TitsIndexData H` is actual Tits index data (module
  [`Reductive.TitsIndex`](../Reductive/TitsIndex.md)) and `e` numbers its simple vertices so
  that every Cartan entry is that of Mathlib's `CartanMatrix.A (2 * m + 1)`: vertices `i` and
  `i + 1` are joined, and there are `2m + 1` vertices. So `H` has absolute type
  `A_{2m+1}`, and it is a form of `SL_{2m+2}`.
- **Outer form.** The hypothesis that some element `σ` of the absolute Galois group of `K`
  moves a simple vertex under the star action `d.star` says that `H` is an outer form. The
  only nontrivial automorphism of the `A_{2m+1}` diagram is the reversal `i ↦ 2m - i`, so the
  star action then factors through the Galois group of a quadratic extension `L/K`. For
  `m = 0` the diagram has one vertex, no element moves it, and the statement is vacuous.
- **Middle weight.** `d.absoluteFundamentalCharacter hsc a` is the integral fundamental
  weight at the simple vertex `a`, defined through the simple-coroot basis of the
  cocharacter lattice of the simply connected group (module
  [`SimplyConnected.TypeD4CentralCharacters`](../SimplyConnected/TypeD4CentralCharacters.md)).
  The vertex numbered `m` is the unique vertex fixed by the reversal, so its fundamental
  weight is fixed by the full star action and lies in `d.pinning.starFixedWeights`. The
  statement quantifies over the element `w` of that group with this value.
- **Tits obstruction.** `d.pinning.titsObstruction hsc` is the Library's homomorphism from the
  star-fixed weights to the Brauer group of `K` (module
  [`Reductive.TitsObstruction`](../Reductive/TitsObstruction.md)). On a dominant star-fixed
  weight it is the class of the Tits algebra of the irreducible representation with that
  highest weight (J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur
  un corps quelconque*, J. reine angew. Math. 247 (1971), Corollary 3.5).
- **Anisotropy.** `IsAnisotropic H` is the Library's convention: split rank zero.

## Mathematical content

The statement is derived from the following classical results (provenance: derived). The
sources are M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*,
AMS Colloquium Publications 44, 1998, registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions` (cited as KMRT), and V. Platonov and
A. Rapinchuk, *Algebraic Groups and Number Theory*, 1994, registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory` (cited as PR). Since the outer
hypothesis is vacuous for `m = 0`, assume `m ≥ 1`.

1. *Outer forms of type `A`.* By KMRT, Theorem (26.9), printed p. 366, `H ≅ SU(B, τ)` for a
   central simple algebra `B` of degree `2m + 2` over the quadratic extension `L` of `K` that
   splits the star action, with an involution `τ` of the second kind. Write `B ≅ M_r(D)`
   with `D` a central division algebra of degree `d` over `L`, so `rd = 2m + 2`. Then `D`
   carries an involution `σ` of the second kind, and `τ` is adjoint to a nondegenerate
   hermitian form `h` of rank `r` over `(D, σ)` (KMRT, §4.A, printed p. 41, and
   Theorem (4.2), printed p. 43). We take `B = M_r(D)`. By PR,
   Proposition 2.15, printed p. 86, the split rank of `SU(h)` is the Witt index of `h`; so
   `H` is anisotropic exactly when `h` is anisotropic.
2. *Its middle Tits algebra.* The character group of the centre of `H` is `ℤ/(2m + 2)ℤ`,
   on which the nontrivial element of `Gal(L/K)` acts by `x ↦ -x`. By KMRT, §27.B, printed
   p. 378, its only nonzero fixed element is `m + 1`, the class of the middle fundamental
   weight, and the corresponding Tits algebra is the discriminant algebra `D(B, τ)`, a
   central simple `K`-algebra (KMRT, Definition (10.28), printed p. 128). By KMRT,
   Proposition (10.30), printed p. 129, and (10.4)(a), printed p. 116, after extending scalars
   to `L` it is isomorphic to the `(m + 1)`-st `λ`-power of `B`, whose Brauer class is
   `(m + 1)[B] = (m + 1)[D]`.

The statement is the contrapositive of the following: if `D(B, τ)` is split, then `h` is
isotropic.

3. *Commutative `D`.* If `D = L`, then `h` is an ordinary hermitian form of dimension
   `2m + 2 ≥ 4` over `L/K`. It represents `0` over `K_v` at every place `v`: at a place split
   in `L` the norm form of `L ⊗_K K_v ≅ K_v × K_v` is isotropic, and at the other places by
   PR, Claim 6.2(A), printed p. 343. By Claim 6.2(B) it represents `0` over `K`. This case
   does not need the hypothesis on `D(B, τ)`.
4. *Even matrix size.* Suppose that `D(B, τ)` is split and `D ≠ L`. Then `(m + 1)[D] = 0` in
   the Brauer group of `L`. Over the number field `L` the exponent of `D` equals its index
   `d` (PR, §1.4.1, printed p. 28, and §1.5.1, printed p. 38). So `d` divides
   `m + 1 = rd/2`, and `r` is even, in particular `r ≥ 2`. Let `h₀` be the hyperbolic
   hermitian form of rank `r` over `(D, σ)`.
5. *Landherr's theorem.* Let `F` and `F₀` be the Gram matrices of `h` and `h₀`, and write
   `τ` on `B = M_r(D)` as in PR, §6.7, printed p. 359, as `τ(X) = F σ(X)^t F⁻¹`. The element
   `y = F₀ F⁻¹` is a `τ`-symmetric unit, and an element `x` of `B ⊗_K K_v` solves
   `y = x τ(x)` exactly when `F₀ = x F σ(x)^t`, that is, when the two Gram matrices are
   congruent over `K_v`, so that `h ⊗ K_v ≅ h₀ ⊗ K_v`. Landherr's theorem (PR, Theorem 6.27,
   printed p. 359, stated there for a noncommutative `D`, as here) says that if this
   equation has a solution at every place `v` of `K`, it has a solution in `B`. It therefore suffices to show `h ⊗ K_v ≅ h₀ ⊗ K_v` for every `v`.
6. *Local isometry with `h₀`.* Let `v` be a place of `K`.
   - If `v` splits in `L`, then `L ⊗_K K_v ≅ K_v × K_v`, and `(B ⊗_K K_v, τ)` is isomorphic
     to `(B' × B'^op, ε)` with the exchange involution `ε(a, b^op) = (b, a^op)` (KMRT,
     Proposition (2.14), printed p. 21). Every symmetric unit is `(a, a^op) = x ε(x)` with
     `x = (a, 1)`, so the equation of step 5 has a solution at `v`. Because `K` is totally
     complex, every archimedean place is complex and is of this kind.
   - If `v` does not split in `L`, it is finite, `L_w = L ⊗_K K_v` is a quadratic field
     extension of `K_v`, and `B ⊗_K K_v ≅ M_{2m+2}(L_w)` with `τ` adjoint to an ordinary
     hermitian form `h_v` of dimension `2m + 2` over `L_w/K_v` (PR, proof of Lemma 6.24,
     printed p. 361; in particular `D ⊗_L L_w` is split). The discriminant algebra is
     the algebra of invariants of an automorphism defined over `K`, so it commutes with
     scalar extension, and KMRT, Corollary (10.35), printed p. 131, gives
     `D(B, τ) ⊗_K K_v ∼ (L_w, disc h_v)`, where `disc h_v` is the signed determinant (KMRT,
     §10, printed p. 114). As `D(B, τ)` is split, `disc h_v` is a norm from `L_w`. Hence
     `h_v` is hyperbolic. Indeed, a hermitian form of dimension at least `3` over `L_w/K_v`
     is isotropic (PR, Claim 6.2(A)), so it splits off a hyperbolic plane. A hyperbolic
     plane has trivial signed determinant, and the signed determinant is multiplicative on
     orthogonal sums of even-dimensional forms, so splitting off hyperbolic planes leaves a
     binary form with the same signed determinant, diagonal as `⟨a, b⟩` with
     `a, b ∈ K_v^×`. Its signed determinant `-ab` is a norm, hence so is `-b/a = -ab/a²`,
     and the binary form represents `0` and is hyperbolic. So `τ ⊗ K_v` is hyperbolic,
     and by KMRT, Proposition (6.7), printed pp. 74–75, every hermitian form over
     `D ⊗_K K_v` with adjoint involution `τ ⊗ K_v` is hyperbolic. In particular
     `h ⊗ K_v ≅ h₀ ⊗ K_v`, both being hyperbolic of rank `r`.

By steps 5 and 6, `h ≅ h₀` is hyperbolic of rank `r ≥ 2`, hence isotropic.

By step 1, `H` is then isotropic. So an anisotropic `H` has `D(B, τ)` nonsplit: its
middle Tits obstruction is nonzero.

The hypothesis that `K` is totally complex is used only at the archimedean places, in
steps 3 and 6: at a real place not split in `L`, hermitian forms are not determined by their
dimension and discriminant. Platonov–Rapinchuk record the background on anisotropic groups
over totally complex fields in Theorem 6.25 and the remark following it (printed p. 352):
such groups are of type `A`, and over these fields, unlike over local fields, outer forms
can be anisotropic.
