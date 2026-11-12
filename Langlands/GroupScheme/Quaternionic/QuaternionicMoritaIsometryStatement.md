# The quaternionic Morita isometry statement

Authors: Worker 5198.

Module `Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryStatement`, namespace
`Langlands.GroupScheme.Quaternionic`. It contains one Prop-valued definition,
`QuaternionicMoritaIsometryStatement`, and proves nothing. Its proof is a separate task.

## The statement

`QuaternionicMoritaIsometryStatement` says the following, at an arbitrary universe `u`.

- Let `K D : Type u` with `[Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D]` and `Module.finrank K D = 4`. So `D` is a quaternion division
  algebra over `K`.
- Let `σ : FirstKindInvolution K D` be an involution of the first kind (published module
  `Langlands.GroupScheme.Quaternionic.Involution`) with
  `Module.finrank K σ.symmetricSubspace = 3`.
- Let `m : ℕ` and let `q : σ.QuadraticForms (Fin m)` be a `σ`-quadratic form on `D^m` in the
  sense of Tits (published module `Langlands.GroupScheme.Quaternionic.Forms`:
  `M_m(D) ⧸ {x - ᵗx^σ}`) with `σ.IsNondegenerateQuadratic q`, that is, with invertible polar
  Gram matrix `Q + ᵗQ^σ`.
- Write `L = AlgebraicClosure K`. Then there is
  `Q : (FirstKindInvolution.scalar L).QuadraticForms (Fin (2 * m))` with
  `(FirstKindInvolution.scalar L).IsNondegenerateQuadratic Q`, together with an isomorphism

  `(GroupScheme.baseChange (toAlgebraicClosure K)).obj (σ.isometryGroup q) ≅
  (FirstKindInvolution.scalar L).isometryGroup Q`.

The objects are the published ones.

- `σ.isometryGroup q` is the isometry group scheme `O(q)` of
  `Langlands.GroupScheme.Quaternionic.GroupSchemes`, an actual affine group scheme over
  `Spec K`. Its points with values in a commutative `K`-algebra `R` are the units `u` of
  `R ⊗[K] M_m(D)` with `u Q ᵗu^σ - Q ∈ R ⊗ {x - ᵗx^σ}`.
- `toAlgebraicClosure K` is the morphism `Spec L ⟶ Spec K` induced by `algebraMap K L`
  (module `Langlands.GroupScheme.Reductive.Basic`). `GroupScheme.baseChange` is the Library's
  base-change functor of group schemes along a morphism of bases.
- `FirstKindInvolution.scalar L` is the identity involution of `L` (module
  `Langlands.GroupScheme.Quaternionic.ScalarInvolution`). With it,
  `(scalar L).QuadraticForms (Fin (2 * m)) = M_{2m}(L) ⧸ {a - ᵗa}` is the space of ordinary
  quadratic forms `x ↦ x Q ᵗx` on `L^{2m}`. `IsNondegenerateQuadratic` means that the polar
  matrix `Q + ᵗQ` is invertible (`isNondegenerateQuadratic_scalar_mk_iff`). The group
  `(scalar L).isometryGroup Q` is the ordinary orthogonal group scheme `O(Q)` over `Spec L`.

The isomorphism `≅` is taken in the category of group schemes over `Spec L`. It identifies the
points of the two groups with values in every commutative `L`-algebra, compatibly with the
group laws, not only their `L`-rational points. The statement asserts only that some `Q` and
some isomorphism exist. It does not fix a splitting `L ⊗[K] D ≅ M_2(L)`, a representative of
`q`, or a formula for the isomorphism. No hypothesis on the characteristic of `K`, on local
fields or on Witt indices is made, and every `m` is allowed. For `m = 0` both groups are
trivial.

The conventions are the same in every characteristic, including 2. On both sides a quadratic
form is a class in Tits's quotient `B/A` (bilinear forms modulo the image of `b ↦ b − π(b)`),
not a hermitian or symmetric bilinear form. Nondegeneracy always means that the polar Gram
matrix is invertible, which is Tits's notion because the reduced degree `2m` is even. The
section "Characteristic 2" below explains why this needs no extra hypothesis.

## Correspondence with the source

The source is J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de Clifford*,
Invent. Math. 5 (1968), 19–41 (`tits-1968-formes-quadratiques-clifford`; PDF page = printed
page − 17). Tits works with a central simple algebra `E` of degree `n` over `k`.

- **Type of an involution** (§2.1, printed p. 20 / PDF p. 3). An involution of the first kind
  `σ` of `E` has symmetric space of dimension `½n(n + 1)` or `½n(n − 1)`, "et seul le premier
  cas peut se présenter si n est impair ou car k = 2". Tits calls `σ` of type `1` in the first
  case. A "space of bilinear forms" for `E` is a pair `(B, π)` with `B ≅ E_d` as a right
  `E`-module and `π(s e) = s e^σ` for a generator `s` and an involution `σ` of type `1`. Such
  a pair is unique up to isomorphism.
- **Quadratic forms** (§2.2, printed p. 21 / PDF p. 4). `S = {b | b = π(b)}`,
  `A = {b − π(b) | b ∈ B}` and `Q = B/A`. The elements of `Q` are the quadratic forms, and the
  bilinearization is `β(b̄ + A) = b̄ + π(b̄)`. A form `q` is nondegenerate in Tits's sense
  when its radical conditions hold; "si car k ≠ 2 ou si n est pair, cela signifie simplement
  que β(q) est non dégénérée". A form `b ∈ B` is nondegenerate when it generates the
  `E`-module `B`.
- **Extension of scalars** (§2.2, printed p. 22 / PDF p. 5). For a field extension `k'/k`,
  `(B ⊗ k', π ⊗ id)` is a space of bilinear forms for `E ⊗ k'`, and the corresponding spaces
  of symmetric, alternating and quadratic forms are `S ⊗ k'`, `A ⊗ k'` and `Q ⊗ k'`.
- **The scalar case** (§2.3, printed pp. 22–23 / PDF pp. 5–6). For `D = k`, `δ = id`, the
  space `Q` is in bijection with the ordinary quadratic forms. This is the case
  `σ = FirstKindInvolution.scalar L` of the target.
- **The groups** (§3, printed p. 30 / PDF p. 13). A `k`-group is a group scheme of finite
  type over `Spec k`, and a `k`-form of a `k̄`-group `H` is a `k`-group that becomes
  isomorphic to `H` after extension of scalars from `k` to `k̄`. For `f ∈ Q`, `U(f)` is the
  `k`-subgroup of `GL(E)` defined by the equation `f^x = f`. Here `GL(E)` has as points with
  values in a `k`-algebra `Y` the invertible elements of `E ⊗_k Y`. Over an algebraically
  closed field and for nondegenerate `q`, Tits writes `U(q) = O_n`. He justifies this by the
  fact that the group "ne dépend pas, à isomorphisme près, de l'algèbre E et des formes a et
  q, mais seulement de n et du corps k". Then Proposition 6 reads: "Quel que soit le corps
  k, si a ∈ A et q ∈ Q désignent des formes non dégénérées, les groupes U(a) = SU(a), U(q)
  et SU(q)⁰ sont des k-formes de k̄Sp_n, k̄O_n et k̄SO_n⁰ respectivement."

The Lean statement is the `U(q)` part of Proposition 6 for `E = M_m(D)`, `n = 2m`,
`B = E_d`, `s = 1` and `π = σ.matrix (Fin m)`, the conjugate transpose `x ↦ ᵗx^σ`.

- **The hypothesis on `σ` is Tits's type-1 condition.** The symmetric matrices for
  `x ↦ ᵗx^σ` have diagonal entries in `D^σ`, and their entries below the diagonal are
  determined by those above it. So their dimension is `m·dim D^σ + 4·½m(m − 1)`. For
  `m ≥ 1` this equals `m(2m + 1) = ½n(n + 1)` exactly when `dim D^σ = 3`, which is also the
  type-1 condition for `σ` on `D` itself (`½·2·3 = 3`). Hence `(M_m(D), σ.matrix (Fin m))` is
  a space of bilinear forms for `M_m(D)` in Tits's sense exactly under the hypothesis
  `Module.finrank K σ.symmetricSubspace = 3`. Tits 1977, 1.1.6 (below) imposes the same
  condition `dim D^σ = ½d(d + 1)` with `d = 2`.
- **Quadratic forms and nondegeneracy.** With `B = M_m(D)` and `π = σ.matrix (Fin m)`, Tits's
  `A` is `{x − ᵗx^σ} = σ.quadraticKernel (Fin m)`, and `Q = B/A` is
  `σ.QuadraticForms (Fin m)`. Tits's `β` is the published `polar`. Here `n = 2m` is even, so
  Tits's nondegeneracy means that `β(q)` generates the free rank-one module `B = E_d`, that
  is, that `polar q` is invertible. This is `σ.IsNondegenerateQuadratic q`.
- **The groups agree.** Tits's `U(q)` is the isometry group of `q` inside `GL(M_m(D))`, with
  points in every `k`-algebra. For `E = End V`, Tits's action of `E` on forms works out to
  `b^e(x, y) = b(e x, e y)` on the right `D`-space `V` of column vectors (§2.2 (1), (2) and
  §2.3 (2), (3)). The published `isometryGroup` uses row vectors and the condition
  `u Q ᵗu^σ ≡ Q`. As explained in the published `Forms` Markdown, `g ↦ (ᵗg^σ)⁻¹` identifies
  the two isometry groups.
- **The target.** By extension of scalars and the uniqueness of spaces of bilinear forms,
  over `k̄ = L` the algebra `M_m(D) ⊗ L ≅ M_{2m}(L)` carries the space of bilinear forms of
  `L^{2m}`. Its quadratic forms are the ordinary ones (the scalar case above), and Tits's
  `k̄O_n` is `U(Q)` for any nondegenerate ordinary `Q` on `L^{2m}`. "A `k`-form of `k̄O_n`"
  therefore says exactly that the base change of `U(q)` to `L` is isomorphic to `O(Q)` for
  some nondegenerate ordinary quadratic form `Q` on `L^{2m}`. Since Tits's `O_n` does not
  depend on the chosen `Q`, the existential formulation loses nothing.

Tits states Proposition 6 with "Il est clair que". The proof successor must establish the
comparison of actual group schemes. An informal route, which is not formalized here, follows.
The algebra `L ⊗[K] D` is split, `L ⊗[K] D ≅ M_2(L)`. By Skolem–Noether, `σ_L(x) = u ᵗx u⁻¹`
with `ᵗu = ±u`. The hypothesis `dim D^σ = 3` forces `ᵗu = u` when `2 ≠ 0`, and `ᵗu = −u = u`
holds automatically in characteristic 2. Put `U = diag(u, …, u) ∈ M_{2m}(L)`. Right
multiplication by `U` maps `{X − U ᵗX U⁻¹}` onto the alternating matrices `{Y − ᵗY}`. It
sends `q` to the class of `QU`, with polar matrix `(Q + ᵗQ^σ)U`, which is invertible. It also
turns the isometry condition `g Q U ᵗg U⁻¹ − Q ∈ T` into `g (QU) ᵗg − QU ∈ {Y − ᵗY}`.

Context. Tits, Bourbaki exposé 505 (1977), 1.1.6, printed p. 220 / PDF p. 4
(`tits-1977-whitehead-bourbaki-505`), defines `Q = M_m(D)/{x − ᵗx^σ}` for `σ` with
`dim D^σ = ½d(d + 1)` and attaches to a nondegenerate `q` the simply connected group
`Spin q`, "une forme de D_n avec n = ½md". Tits 1966, Table II, type `¹D_n`, printed p. 57 /
PDF p. 62 (`tits-1966-classification-algebraic-semisimple`), describes the same groups. The
present statement is the comparison underlying "form of `D_{md/2}`" for quaternionic `D`.
These two sources motivate the statement but do not print the isomorphism above.

## Characteristic 2

- In characteristic 2 every involution of the first kind is of type `1` (Tits 1968, §2.1,
  quoted above). For quaternionic `D`, the hypothesis `dim D^σ = 3` therefore holds for every
  first-kind involution of `D` when `char K = 2`. After splitting, the matrix `u` above may
  then be alternating or not; in other terminologies these are the symplectic and orthogonal
  involutions. The statement covers both kinds. It assumes no type beyond the stated
  dimension, which is the only condition Tits's construction uses. The informal route above
  needs only `ᵗu = u`, which holds for both.
- In characteristic 2 the quotient `B/A` is still Tits's space of quadratic forms. It is not
  a space of hermitian forms, since `β` is not injective there. For `σ = id` it is the space
  of ordinary quadratic forms (`ScalarInvolution`), and nondegeneracy of `Q` means that the
  alternating polar matrix `Q + ᵗQ` of even size `2m` is invertible, as in Tits's convention
  for even `n`.
- When `2 ≠ 0` the hypothesis cannot be dropped. If `dim D^σ = 1`, then `ᵗu = −u`, and right
  multiplication by `U` identifies `{X − U ᵗX U⁻¹}` with the symmetric matrices. `O(q)` then
  becomes the group of an alternating form, a form of `Sp_{2m}` rather than of `O_{2m}`. This
  remark is explanatory and is not used.

## Lean details

- The binders appear in the order of the task specification. The instances
  `[Algebra.IsCentral K D]` and `[FiniteDimensional K D]` and the equation
  `Module.finrank K D = 4` make `D` a central division algebra of degree 2.
- `AlgebraicClosure K : Type u`, so both sides are group schemes over
  `Spec (CommRingCat.of (AlgebraicClosure K))` in universe `u`. The index types `Fin m` and
  `Fin (2 * m)` live in `Type`, as the published `GroupSchemes` module requires.
- The conclusion is `∃ Q, IsNondegenerateQuadratic Q ∧ Nonempty (_ ≅ _)`.

## Provenance

Source-derived. The statement is the isometry-group part of Tits 1968, Proposition 6 (§3,
printed p. 30 / PDF p. 13), specialized to `E = M_m(D)` with `D` quaternionic. It is
expressed with the published `FirstKindInvolution`, `QuadraticForms`, `IsNondegenerateQuadratic`
and `isometryGroup` objects and with the scalar involution of `ScalarInvolution`. The
identification of the hypotheses with Tits's type-1 and nondegeneracy conditions is the
computation given above.
