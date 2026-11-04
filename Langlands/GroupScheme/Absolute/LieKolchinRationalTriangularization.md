# Lie–Kolchin on rational points

Worker 277.

This module proves `lieKolchinRationalTriangularization :
LieKolchinRationalTriangularizationStatement.{u}`. The proposition is defined in
`Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularizationStatement`. The
setting is a smooth connected affine group scheme `H` over an algebraically closed field
`k`, with solvable group of rational points. Every matrix representation
`ρ : MatrixRepresentation H (Fin N)` becomes upper triangular at all rational points
after conjugation by one `k`-point of the general linear group scheme. The proof equips
the rational points with a Zariski-type topology, checks the hypotheses of the abstract
theorem `Langlands.LieKolchin.exists_triangularizing`, and converts the resulting matrix
`Q` into a base point of `GeneralLinear.groupScheme`.

Throughout, a rational point is a morphism `x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X`.

## The topology on rational points (`RationalZariski`)

- `location H x = x.left (closedPoint k)`: the image in `H.X.left` of the unique point
  of `Spec k`.
- `topology H`: the topology on rational points induced by `location H`. It is a
  definition, not a global instance; the final theorem installs it locally.
- `evaluation H x : Γ(H.X.left, ⊤) →+* k`: pull a global function back along `x.left`
  and identify `Γ(Spec k, ⊤)` with `k` through `Scheme.ΓSpecIso`.
- `const H : k →+* Γ(H.X.left, ⊤)`: constant functions, pulled back along the structure
  morphism. `evaluation_const` shows `evaluation H x (const H c) = c`, because
  `x.left ≫ H.X.hom = 𝟙`.
- `location_comp` and `continuous_comp`: postcomposition `y ↦ y ≫ φ` with any
  endomorphism `φ : H.X ⟶ H.X` over `Spec k` is continuous. Its effect on locations is
  `φ.left`, which is continuous.
- `range_location`: if `k` is algebraically closed and `H.X` is locally of finite type,
  the locations of rational points are exactly the closed points of `H.X.left`. This
  uses the published `isClosed_singleton_rationalPoint` and
  `rationalPointEquivClosedPoint`.
- `preconnectedSpace`: if moreover `H.X.left` is connected, the rational points form a
  preconnected space. Proof: a clopen set `s` of rational points is `location⁻¹ U` and
  its complement is `location⁻¹ V`, with `U`, `V` open. `H.X.left` is a Jacobson space
  (finite type over a field). So a nonempty locally closed subset contains a closed point,
  which is a location by `range_location`. Applying this to `U ∩ V` and to
  `(U ∪ V)ᶜ` shows that `U` and `V` are complementary. Hence `U` is clopen, so it is
  `∅` or everything by connectedness, and `s` is empty or everything.
- `isClosed_evaluation_eq_zero s`: the zero set of `x ↦ evaluation H x s` is closed. It
  is the preimage under `location` of the complement of the basic open set `D(s)`. A
  point of `Spec k` lies in `D(t)` exactly when `t ≠ 0`, since `k` is a field.

## Matrix entries

- `MatrixRepresentation.rationalMatrixMonoidHom ρ`: the published rational matrices
  `ρ.rationalMatrix`, composed with the coercion from units, as a monoid homomorphism
  from rational points to `Matrix (Fin N) (Fin N) k`.
- `rationalMatrixMonoidHom_apply_apply`: its `(i, j)` entry at `x` is the evaluation at
  `x` of the global function `ρ.hom.hom.left.appTop (entrySection i j)`.
- `isClosed_rationalMatrix_linear ρ Λ c`: `{x | Λ (ρ x) = c}` is closed. Expanding
  in the basis of matrix units, `Λ (ρ x) - c` is the evaluation at `x` of the
  global function `∑ i j, s i j * const (Λ (single i j 1)) - const c`, where `s i j`
  is the entry function. Closedness follows from `isClosed_evaluation_eq_zero`.

## The final theorem

Install `topology H`. The rational points are preconnected by `preconnectedSpace`; this
uses smoothness (hence local finite type), algebraic closedness and connectedness. The
separate continuity hypotheses come from the published lemmas
`exists_comp_eq_mul_left` and `exists_comp_eq_commutator_left`. They express
`x ↦ a * x` and `x ↦ ⁅a, x⁆` as postcomposition with endomorphisms of `H.X`, so
`continuous_comp` applies. Inversion is postcomposition with the inverse morphism
`(𝟙 H.X)⁻¹`. `Langlands.LieKolchin.exists_triangularizing` then gives `P`, `Q` with
`P * Q = 1` and every `Q * ρ x * P` upper triangular.

Let `e : Γ(Spec k, ⊤) ≃+* k` be the ring equivalence from `ΓSpecIso`. Let
`C = ⟨Q, P⟩ : GL (Fin N) k`. The chosen point is
`g = (GeneralLinear.pointsEquiv …).symm A` with `A = GL.map e.symm C`. By the published
`conjugate_pointMatrix` and `constantPoint_self`, the point matrix of `ρ.conjugate g`
at `x` is `A * ρ.pointMatrix x * A⁻¹`, computed over `Γ(Spec k, ⊤)`. Mapping entries
through `e` gives `Q * ρ x * P`, because `e` is a ring hom and `e ∘ e.symm = id`. An
entry below the diagonal maps to zero, so it is zero, as `e` is injective.

Note the convention: `MatrixRepresentation.conjugate` multiplies by `g` on the left and
`g⁻¹` on the right, so the point `g` corresponds to `Q = P⁻¹`. In the source convention
`P⁻¹ A P` the basis matrix is `P`.

## Provenance

This is the rational-point consequence of J. S. Milne, *Algebraic Groups* (2017),
Theorem 16.30 and Corollary 16.32, printed pp. 334–335 (`milne-2017-algebraic-groups`).
It is proved without the source's induction on dimension: the algebraic-group
structure is used only through the closedness and continuity properties above. The
topology is the subspace topology on the closed points of `H.X.left`. It plays the role
of the Zariski topology on `G(k)` in the source's proof. The relation between the hypothesis on rational points and solvability of the
group scheme is explained in the statement module's Markdown.
