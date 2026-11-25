# Torsion points are dense in a diagonalizable group

Module `Langlands.GroupScheme.Torus.DiagonalizableTorsionDensity`. This is an internal
helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDensityStatement`
([statement](MultiplicativeTypeTorsionDensityStatement.md),
[proof](MultiplicativeTypeTorsionDensityProof.md)). It imports
[`TorsionDensityLattice`](TorsionDensityLattice.md). It adds no axioms and no `sorry`.
Every declaration is in the namespace `Langlands.GroupScheme.TorsionDensity`.

## Setting

`R : CommRingCat.{u}` is a commutative ring and `Λ : Type u` is an abelian group.
`Diagonalizable.groupScheme R Λ` (module [`Torus.Diagonalizable`](Diagonalizable.md)) is
the diagonalizable group `D(Λ) = Spec R[Λ]` over `Spec R`, where
`R[Λ] = AddMonoidAlgebra R Λ`. Its underlying scheme `(…).toGrp.X.left` is the spectrum
of `R[Λ]`. The group of `T`-points `T ⟶ D(Λ)` uses the scoped `MonObj` notation, as in
the statement.

## Declarations

- `isIso_of_forall_ne_zero z hz h`. Let `A : CommRingCat.{u}` and let `z : Z ⟶ Spec A` be a
  closed immersion. Suppose that for every nonzero `a ∈ A` there are a ring `B`, a ring
  map `φ : A ⟶ B` with `φ a ≠ 0`, and a morphism `y : Spec B ⟶ Z` with
  `y ≫ z = Spec.map φ`. Then `z` is an isomorphism.
  *Proof.* Mathlib's `IsClosedImmersion.isIso_of_injective_of_isAffine` reduces this to
  injectivity of `z.appTop : Γ(Spec A, ⊤) → Γ(Z, ⊤)`. Suppose `z.appTop a₁ = z.appTop a₂`
  and `a₁ ≠ a₂`. Apply the hypothesis to the image of `a₁ - a₂` under
  `Scheme.ΓSpecIso A`, which is nonzero. Then `(y ≫ z).appTop (a₁ - a₂) = 0`. Since
  `y ≫ z = Spec.map φ`, naturality of `Scheme.ΓSpecIso` turns this into `φ a = 0`, a
  contradiction.

- `quotientMap R n : R[Λ] ⟶ R[Λ ⧸ nΛ]` (an `abbrev`) is the `R`-algebra map
  `AddMonoidAlgebra.mapDomainAlgHom` induced by the quotient map
  `Λ → Λ ⧸ multiples Λ n`.

- `quotientPoint R n` (an `abbrev`) is the morphism of `R`-schemes
  `Spec R[Λ ⧸ nΛ] ⟶ D(Λ)` given by `(algSpec R).map (quotientMap R n).op`. It is a point
  of `D(Λ)` with values in the `R`-scheme `Spec R[Λ ⧸ nΛ]`.

- `quotientPoint_pow R n : quotientPoint R n ^ n = 1`.
  *Proof.* The Library equivalence `Corepresented.affinePointsEquiv` (module
  `Langlands.GroupScheme.Corepresented`) identifies, multiplicatively, the points of
  `D(Λ)` on an affine `R`-scheme `Spec S` with the group of characters
  `Multiplicative Λ →* Sˣ`. By `Corepresented.affinePointsEquiv_map` and
  `Diagonalizable.corepresentation_homEquiv_apply`, `quotientPoint R n` corresponds to the
  character `m ↦ [m]`, the image of `single m 1`. Its `n`-th power is
  `m ↦ single (n • [m]) 1 = single 0 1 = 1`, because `n • m ∈ nΛ`. The proof uses
  `set_option backward.isDefEq.respectTransparency false`, as other Library files on
  scheme points do.

- `isIso_of_torsion_factors R hN P hP z h` (**torsion density in `D(Λ)`**). Let `N : ℕ`
  satisfy the separation property `hN` of
  [`exists_separating`](TorsionDensityLattice.md): every nonzero `f ∈ R[Λ]` has nonzero
  image in `R[Λ ⧸ nΛ]` for every multiple `n` of `N` larger than some `M` depending on
  `f`. Let `P : ℕ → Prop` be a set of exponents that contains arbitrarily large multiples
  of `N` (`hP`). Let `z : Z ⟶ D(Λ)` be a closed immersion of schemes. Suppose that for
  every `n` with `P n`, every `R`-scheme `T`, and every point `x : T ⟶ D(Λ)` with
  `x ^ n = 1`, the morphism `x.left` factors through `z`. Then `z` is an isomorphism.
  *Proof.* Apply `isIso_of_forall_ne_zero` with `A = R[Λ]`. Let `f ≠ 0`. Choose `M` from
  `hN`, and `n` with `P n`, `N ∣ n` and `M < n` from `hP`. The point `quotientPoint R n`
  is `n`-torsion (`quotientPoint_pow`), so it factors through `z` by some `y`. Take
  `B = R[Λ ⧸ nΛ]` and `φ = quotientMap R n`; then `φ f ≠ 0` by the choice of `n`.

The exponent set `P` is left abstract. The main proof uses `P n := 0 < n` for part 1 and
`P n := (n : k) ≠ 0` for part 2.

## Source

This is the diagonalizable case of Milne, *Algebraic Groups* (2017), Theorems 12.32 and
12.33 (source ID `milne-2017-algebraic-groups`, pp. 242–243). Milne's proof checks that a
function on `G` vanishing on every `G_n` is zero. Here this becomes the closed-immersion
criterion `isIso_of_forall_ne_zero`, applied to the family of `n`-torsion points
`Spec R[Λ ⧸ nΛ] → D(Λ)`. The ring `R` is an arbitrary commutative ring, not necessarily
an algebraically closed field.
