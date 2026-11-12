# Involutions of the first kind

Authors: Worker 5197.

Module `Langlands.GroupScheme.Quaternionic.Involution`, namespace
`Langlands.GroupScheme.Quaternionic`. This module defines involutions of the first kind of an
algebra and three constructions derived from them. They are the involution data used for the
quaternionic forms of family (iii) of Prasad–Raghunathan (see the paired Markdown of
`Langlands.GroupScheme.Quaternionic.Forms`). Universes are arbitrary.

## Definitions

- `FirstKindInvolution K A`, for a commutative ring `K` and a `K`-algebra `A`, is a structure.
  Its field `toLinearMap : A →ₗ[K] A` is a `K`-linear map `σ` with
  `σ 1 = 1` (`map_one'`), `σ (x * y) = σ y * σ x` (`map_mul'`) and `σ (σ x) = x`
  (`involutive'`). An involution of `A` is an anti-automorphism of order two. It is *of the
  first kind* when it is the identity on the centre. Our algebras are central over `K`, so
  "first kind" means that `σ` fixes the scalars `K`, which is exactly `K`-linearity of an
  additive anti-automorphism. The theorem `map_algebraMap` records `σ (algebraMap K A c) =
  algebraMap K A c`. The structure coerces to a function `A → A`. The simp lemmas `map_one`,
  `map_mul`, `apply_apply`, `map_add`, `map_zero`, `map_neg`, `map_sub`, `map_smul` and
  `map_sum` restate the axioms and linearity, and `injective` records injectivity.
- `σ.symmetricSubspace : Submodule K A` is the space `A^σ = {x | σ x = x}` of symmetric
  elements (`mem_symmetricSubspace`). It is defined as the kernel of `σ - id`.
- `σ.alternatingSubspace : Submodule K A` is the space `{a - σ a | a ∈ A}`
  (`mem_alternatingSubspace`, `sub_mem_alternatingSubspace`). It is defined as the range of
  `id - σ`.
- `σ.matrix n : FirstKindInvolution K (Matrix n n A)`, for a finite index type `n` with
  decidable equality, is the `σ`-conjugate transpose `x ↦ ᵗx^σ`. Its entries are
  `(ᵗx^σ) i j = σ (x j i)` (`matrix_apply`). The construction proves that it is `K`-linear,
  fixes `1`, reverses products (`(x y)ᵗ^σ = ᵗy^σ ᵗx^σ`, computed entrywise from the
  anti-multiplicativity of `σ`) and is involutive.
- `σ.baseChange R : FirstKindInvolution R (R ⊗[K] A)`, for a commutative `K`-algebra `R`, is
  the extension of scalars `id_R ⊗ σ`. It is `LinearMap.baseChange R σ`, with
  `σ.baseChange R (r ⊗ a) = r ⊗ σ a` (`baseChange_tmul`). The proofs check
  anti-multiplicativity and involutivity on pure tensors, using commutativity of `R`.
  `map_baseChange` shows that it commutes with every change of coefficients `R →ₐ[K] S`.

## Sources

The notions are those of the cited sources, formalized here for arbitrary algebras.

- G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment. Math. Helv. 60
  (1985), 107–121 (`prasad-raghunathan-1985-kneser-tits`), §2 (iii), printed p. 111 / PDF
  p. 6: "σ is an involution of the quaternion central division algebra D over K such that the
  dimension of D^σ, the space of symmetric elements, is 3." `D^σ` is
  `σ.symmetricSubspace`. The dimension is over `K`, so `σ` is `K`-linear, that is, of the
  first kind.
- J. Tits, *Groupes de Whitehead de groupes algébriques simples sur un corps*, Séminaire
  Bourbaki 505 (1977) (`tits-1977-whitehead-bourbaki-505`), 1.1.6, printed p. 220 / PDF p. 4:
  "une involution σ de première espèce dont l'espace des points fixes est de dimension
  ½d(d + 1) sur K". The same paragraph defines `T = {x − ᵗx^σ | x ∈ E}` for
  `E = M_m(D)`. Its `ᵗx^σ` is our `σ.matrix (Fin m) x`, and its `T` is
  `(σ.matrix (Fin m)).alternatingSubspace`.
- J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos. Pure Math. 9 (1966),
  33–62 (`tits-1966-classification-algebraic-semisimple`), Table II, type `C_n`, printed
  p. 56 / PDF p. 61: "an involution σ of the first kind such that D^σ (the space of
  symmetric elements) has dimension ½d(d + 1)". For a quaternion algebra (`d = 2`) this is
  dimension 3.

The extension of scalars `σ.baseChange R` has no counterpart in the sources. It is internal:
it gives the `R`-points of the group schemes defined in
`Langlands.GroupScheme.Quaternionic.GroupSchemes`.

## Remark on characteristic 2

When `2` is invertible in `K`, an involution of the first kind of a quaternion algebra has
symmetric space of dimension 3 (orthogonal type) or 1 (the canonical, symplectic involution).
In characteristic 2 every involution of the first kind of a quaternion algebra has a symmetric
space of dimension 3. The sources' condition `dim_K D^σ = 3` is used unchanged in all
characteristics. This module asserts no such classification; the remark only explains why no
characteristic restriction is imposed.
