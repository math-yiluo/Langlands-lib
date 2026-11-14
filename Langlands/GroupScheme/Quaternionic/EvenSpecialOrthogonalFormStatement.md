# Forms of the split even special orthogonal group

Author: Worker 349.

`Langlands.GroupScheme.Quaternionic.EvenSpecialOrthogonalFormStatement.{u}` is an
**unproved** statement. It is the case `SO⁰_{2n}`, `n ≥ 4`, of Tits's realization of the
forms of the orthogonal groups (Tits 1968, §3, Théorème 1). There is no characteristic
hypothesis.

## Hypotheses

- `K : Type u` is a field and `H` is a group scheme over `Spec K` that is affine and locally
  of finite type (`IsAffineHom H.X.hom`, `LocallyOfFiniteType H.X.hom`);
- `n : ℕ` with `4 ≤ n`;
- there is an isomorphism of group schemes over `Spec K^s`, with `K^s = SeparableClosure K`,

  `(GroupScheme.baseChange (algebraBaseMap K K^s)).obj H ≅
    identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K^s))`.

  Here `OrthogonalMatrix.groupScheme (Fin n) R` is the Library's split orthogonal group
  `O_{2n}` of the hyperbolic quadratic form `∑ a, x (inl a) * x (inr a)` on `R^(Fin n ⊕ Fin n)`,
  in every characteristic. `identityComponent` is the Library's identity component of a smooth
  affine group scheme over a field; the needed smoothness instance is
  `OrthogonalMatrix.smooth_groupScheme_of`. So the hypothesis says that `H` becomes isomorphic
  to the split `SO⁰_{2n}` over `K^s`.

## Conclusion

There exist a central finite-dimensional division algebra `D : Type u` over `K`, natural
numbers `degree` and `m`, an involution `σ : FirstKindInvolution K D` and a form
`q : σ.QuadraticForms (Fin m)` such that

- `0 < degree`, `Module.finrank K D = degree ^ 2` and `m * degree = 2 * n`;
- `Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2` (natural-number
  division), i.e. `σ` has Tits's type 1;
- `σ.IsNondegenerateQuadratic q` (the polar form of `q` is invertible);
- the isometry group `σ.isometryGroup q = O(q)` is smooth over `Spec K`, and, with that
  smoothness instance, `H ≅ σ.connectedIsometryGroup q`, the identity component `O(q)⁰`.

The conclusion has the same shape as the algebra, involution and form in
`ClassicalTypeDAlignedSpinCoverStatement`.

## Source and comparison

J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de Clifford*, Invent. Math. 5
(1968), 19–41. Registered source `tits-1968-formes-quadratiques-clifford`, PDF SHA-256
`f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782` (PDF page = printed
page − 17).

- §2.1, printed p.20 / PDF p.3: an involution `σ` of the first kind of a central simple algebra
  `E` of degree `N` has type 1 when `dim E^σ = ½N(N + 1)`; every `E` with an involution of the
  first kind has one of type 1. The space of bilinear forms is `(B, π)`, `B ≅ E_d`, with
  `π(se) = s e^σ` for a type-1 `σ`.
- §2.2, printed p.21 / PDF p.4: `A = {b − π(b)}`, quadratic forms `Q = B/A`, and
  nondegeneracy; for `N` even, `q ∈ Q` is nondegenerate exactly when its bilinearization
  `β(q)` is nondegenerate.
- §3, printed p.30 / PDF p.13: the groups `U(f)` and `SU(f)` in `GL(E)`, the notation
  `SU(q)⁰ = SO⁰_N` over an algebraically closed field, Proposition 6 (for nondegenerate
  `q ∈ Q`, `U(q)` and `SU(q)⁰` are `k`-forms of `O_N` and `SO⁰_N`) and Remarque 2 (`U(f)` is
  absolutely reduced unless `char k = 2` and `f` is defective).
- §3, Théorème 1, printed p.31 / PDF p.14: for a `k`-form `G` of `SO⁰_N` there are a central
  simple algebra `X` over `k` isomorphic to its opposite and a `k`-immersion `ρ : G → GL(X)`
  that is a form of the standard immersion; if `X = E`, then `ρ(G) = SU(f)⁰` for the nonzero
  points `f` of a unique line `L ⊂ Q`, and these `f` are nondegenerate. Remarque 3 on the same
  page notes that trialitarian forms of `D₄` need not be excluded, since they are simply
  connected or adjoint, so Théorème 1 covers every form of `SO⁰_8`.

Correspondence with the Lean statement (`N = 2n`):

- Tits's `k`-form means a group that becomes isomorphic to `SO⁰_N` over `k̄`. The Lean
  hypothesis asks for an isomorphism over `K^s ⊆ k̄`, which implies Tits's hypothesis. The Lean
  statement is therefore the special case of Théorème 1 with `N = 2n ≥ 8`.
- Take `D` the division algebra Brauer equivalent to `X`, so `X ≅ M_m(D)` with
  `m · deg D = 2n`. Since `X ≅ X^op`, `D` has an involution of the first kind and hence one of
  type 1 (§2.1); for `σ` of type 1 on `D`, the conjugate transpose `σ.matrix (Fin m)` on
  `E = M_m(D)` again has type 1 (`m·½d(d + 1) + ½m(m − 1)d² = ½md(md + 1)` with `d = deg D`).
  With `B = E` and `π = σ.matrix (Fin m)`, Tits's `Q = E/{x − ᵗx^σ}` is the Library's
  `σ.QuadraticForms (Fin m)`, his nondegeneracy (for even `N`) is
  `σ.IsNondegenerateQuadratic`, and his `U(q)` is `σ.isometryGroup q` (row-vector conventions,
  see `Quaternionic/Forms.md` and `Quaternionic/GroupSchemes.md`).
- `SU(q)⁰ = U(q)⁰`: `SU(q)` is the kernel of the reduced norm `U(q) → μ₂`; in characteristic
  not 2 it is open and closed in `U(q)`, and in characteristic 2 it equals `U(q)` for even
  `N` (Tits, p.30). So `ρ(G) = SU(q)⁰` gives `H ≅ O(q)⁰ = σ.connectedIsometryGroup q`.
- Smoothness of `O(q)` follows from Proposition 6 (it is a form of `O_{2n}`, which is smooth)
  together with Remarque 2: a nondegenerate form in even dimension is not defective.

The Lean formulation uses the Library's group schemes and functor-of-points isomorphisms,
which Tits does not; the mathematical content is that of Théorème 1 as explained above.
