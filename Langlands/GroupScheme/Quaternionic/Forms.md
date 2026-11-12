# Antihermitian and quadratic forms over a division algebra with involution

Authors: Worker 5197.

Module `Langlands.GroupScheme.Quaternionic.Forms`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`. Throughout, `K : Type u` is a field,
`D : Type v` is a division ring with `[Algebra K D]`, `σ : FirstKindInvolution K D` is an
involution of the first kind (module `Langlands.GroupScheme.Quaternionic.Involution`), and
`n : Type w` is a finite index type with decidable equality. Forms "of rank `m`" are forms on
`D^m`, that is, `n = Fin m`. Nothing here requires `D` to be quaternion or central; the
statements specialize to that case.

## Convention: row vectors and Gram matrices

Mathlib's `D`-modules are left modules, so `D^n = n → D` is a left `D`-vector space of row
vectors. A matrix `H ∈ M_n(D)` is the Gram matrix of the form

`σ.sesqForm H x y = ∑ i, ∑ j, x i * H i j * σ (y j)`,

which satisfies `h(a x, b y) = a h(x, y) σ(b)`. A matrix `g` acts by `x ↦ x g`.

The sources write forms on right vector spaces of column vectors, with
`h_r(x, y) = ᵗx^σ H y`; Tits's notation `ᵗx^σ` appears in the definition of `T` below. The two
conventions use the same Gram matrix. The bijection `x ↦ ᵗx^σ` from columns to rows is
`σ`-semilinear, it maps right subspaces to left subspaces of the same dimension, and
`h_r(x, y) = σ.sesqForm H (ᵗx^σ) (ᵗy^σ)`. So totally isotropic subspaces, totally singular
subspaces and Witt indices agree. The matrix `g` is a right-convention isometry,
`ᵗg^σ H g = H`, exactly when `ᵗg^σ` is a left-convention isometry, `g' H ᵗg'^σ = H`. The same
holds modulo `T` for quadratic forms. Composing `g ↦ ᵗg^σ` with inversion therefore
identifies the two isometry groups. These remarks justify the convention and are not
formalized.

`map_sesqForm_self` proves `σ (h(x, x)) = h'(x, x)`, where `h'` is the form with Gram matrix
`ᵗH^σ = σ.matrix n H`.

## Antihermitian forms

- `σ.IsAntihermitian H` means `σ.matrix n H = -H` and `H i i ∈ σ.alternatingSubspace` for
  every `i`. The first condition is `ᵗH^σ = -H`, equivalently `h(y, x) = -σ(h(x, y))`. The
  second says that the diagonal entries have the form `a - σ a`. It makes the form
  *trace-valued*: `h(x, x) ∈ {a - σ a}` for all `x`, because the off-diagonal terms pair up as
  `c - σ c`. When `2` is invertible in `K` the second condition follows from the first, since
  `σ (H i i) = -H i i` gives `H i i = H i i / 2 - σ (H i i / 2)`. In characteristic 2 it is the
  extra condition that makes antihermitian forms alternating: for `D = K` and `σ = id` the
  isometry group is then `Sp_{2n}`, as the sources require (below).
- Nondegeneracy of the form is invertibility of its Gram matrix. The statements write it as
  `IsUnit H` in `M_n(D)`.
- `σ.IsTotallyIsotropic H W` means `h(x, y) = 0` for all `x y ∈ W`, for a left `D`-subspace
  `W ≤ D^n`.
- `σ.wittIndex H : ℕ` is the supremum (`sSup`) of `Module.finrank D W` over the totally
  isotropic subspaces `W`. The set contains `0` (for `W = ⊥`) and is bounded by `card n`, so
  the supremum is the largest dimension of a totally isotropic subspace.

## Quadratic forms in the sense of Tits

- `σ.quadraticKernel n : Submodule K (M_n(D))` is Tits's `T = {x - ᵗx^σ | x ∈ M_n(D)}`,
  defined as `(σ.matrix n).alternatingSubspace`.
- `σ.QuadraticForms n` is the `K`-vector space `M_n(D) ⧸ T`. Its elements are the
  `σ`-quadratic forms on `D^n`. A matrix `Q` represents the form whose value at `x` is the
  class of `∑ i j, x i * Q i j * σ (x j)`.
- `σ.polar : σ.QuadraticForms n →ₗ[K] M_n(D)` sends the class of `Q` to `Q + ᵗQ^σ`
  (`polar_mk`). It is well defined because `(x - ᵗx^σ) + ᵗ(x - ᵗx^σ)^σ = 0`. Its value is
  the Gram matrix of the polar hermitian form `h_q`: `q(x + y) - q(x) - q(y)` is the class of
  `h_q(x, y)` modulo `{a - σ a}`.
- `σ.evalLinear x : M_n(D) →ₗ[K] D` is `Q ↦ ∑ i j, x i * Q i j * σ (x j)`.
- `σ.quadraticValue x : σ.QuadraticForms n →ₗ[K] D ⧸ σ.alternatingSubspace` is the value
  `q(x)`, the class of `evalLinear x Q` modulo `{a - σ a}` (`quadraticValue_mk`). It is well
  defined because, by `map_sesqForm_self`, the representative `x - ᵗx^σ` of zero has value
  `c - σ c` with `c = evalLinear x x`.
- `σ.IsNondegenerateQuadratic q` means that `σ.polar q` is invertible.
- `σ.IsTotallySingular q W` means `q(x) = 0` for every `x ∈ W`.
- `σ.quadraticWittIndex q : ℕ` is the supremum of `Module.finrank D W` over the totally
  singular subspaces `W`, that is, the largest such dimension.

## Sources and comparison of conventions

**Prasad–Raghunathan.** G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*,
Comment. Math. Helv. 60 (1985), 107–121 (`prasad-raghunathan-1985-kneser-tits`), §2 (iii),
printed p. 111 / PDF p. 6: "the spin group of a σ-quadratic form of Witt index 1 and rank 4
or 5, or the symplectic group of a σ-antihermitian form of rank 2 or 3 and Witt index 1;
where σ is an involution of the quaternion central division algebra D over K such that the
dimension of D^σ, the space of symmetric elements, is 3". The source does not define these
forms; it uses Tits's conventions, recalled next. "Rank" is the number of variables `m` of a
form on `D^m`.

**Tits 1966, antihermitian forms.** J. Tits, *Classification of algebraic semisimple groups*,
Proc. Sympos. Pure Math. 9 (1966), 33–62 (`tits-1966-classification-algebraic-semisimple`),
Table II, type `C_n`, printed p. 56 / PDF p. 61: the groups of type `C_n` are "SU_{2n/d}(D,
h), where D is a division algebra of degree d over k, and h is a nondegenerate antihermitian
sesquilinear form of index r relative to an involution σ of the first kind such that D^σ (the
space of symmetric elements) has dimension ½d(d + 1). When d = 1, the group becomes simply
Sp_{2n}(k)." For `d = 2` this is PR's condition `dim D^σ = 3`. The index `r` is the Witt index.
The remark on `d = 1` is the reason for the trace-valued condition in characteristic 2.

**Tits 1977, quadratic forms.** J. Tits, *Groupes de Whitehead de groupes algébriques simples
sur un corps*, Séminaire Bourbaki 505 (1977) (`tits-1977-whitehead-bourbaki-505`), 1.1.6,
printed p. 220 / PDF p. 4: for `D` of degree `d` with an involution σ of the first kind whose
fixed space has dimension `½d(d + 1)`, and `E = M_m(D)` with `md` even, "posons T = {x − ᵗx^σ
| x ∈ E} et Q = E/T. Les éléments de Q sont appelés formes quadratiques". Our
`σ.QuadraticForms (Fin m)` is this `Q`. Tits continues: "si D = K, on reconnaît la notion
usuelle de forme quadratique". Indeed for `σ = id`, `T` is the space of alternating matrices,
and `E/T` is the space of ordinary quadratic forms `x ↦ x Q ᵗx`, in every characteristic.
Nondegeneracy and the Witt index ("q non dégénérée et isotrope, c'est-à-dire d'indice de Witt
strictement positif", printed p. 221 / PDF p. 5) are referred to Tits's 1968 paper [41], which
is not available here.

- *Nondegeneracy.* Every quaternionic form has `md = 2m` even. We take nondegeneracy to mean
  invertibility of the polar Gram matrix `Q + ᵗQ^σ`. When `2` is invertible this is
  nondegeneracy of the associated hermitian form. In characteristic 2 it also excludes a
  defect, matching Tits 1966, Table II, type `¹D_n`, printed p. 57 / PDF p. 62: "if char k =
  2, ... h is a nondegenerate and nondefective 'quadratic form'".
- *Witt index.* The Witt index is the largest dimension of a totally singular subspace. When
  `2` is invertible, `q(x) = 0` in `D ⧸ {a - σ a}` is equivalent to `h_q(x, x) = 0`.

**A slip in Tits 1977.** The same paragraph of Tits 1977 says: "si car K ≠ 2, on voit
immédiatement qu'une forme quadratique est la même chose qu'une forme antihermitienne
(relative à σ)". With `T` as displayed and `dim D^σ = ½d(d + 1)`, the map `Q ↦ Q + ᵗQ^σ`
identifies `E/T` with the `σ`-*hermitian* matrices when `2` is invertible (inverse
`h ↦ h/2`), not with the antihermitian ones. Tits's own remark on `D = K` (where `σ = id` and
antihermitian forms would be alternating) and Tits 1966, Table II, type `¹D_n`, printed p. 57 /
PDF p. 62 confirm the hermitian reading. The latter reads, in characteristic not 2,
"SU_{2n/d}(D, h) where ... h is a nondegenerate hermitian form ... relative to an involution σ
of the first kind such that D^σ ... has dimension ½d(d + 1)". The word "antihermitian" is
correct only for Tits 1966's equivalent description with an involution whose symmetric space
has dimension `½d(d − 1)`. We follow the displayed definition of `T`. So PR's two families use
the same `σ`: antihermitian forms give type `C`, and quadratic forms (hermitian when `2` is
invertible) give type `D`.

## Provenance

The definitions formalize the cited notions with the conventions above. `sesqForm`,
`evalLinear` and the well-definedness lemmas are internal.
