# Forms of the split `SO_{2n}` from the automorphism theorem

## Statement

`evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism` derives the
Library proposition `EvenSpecialOrthogonalFormStatement` from the Library
proposition `SpecialOrthogonalAutomorphismStatement`, at the same universe `u`:

```
theorem evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism
    (hS : SpecialOrthogonalAutomorphismStatement.{u}) :
    EvenSpecialOrthogonalFormStatement.{u}
```

`EvenSpecialOrthogonalFormStatement` says: let `K` be a field, `n ≥ 4`, and
`H` an affine group scheme of locally finite type over `K` that becomes
isomorphic to the split `SO_{2n}` (the identity component of
`OrthogonalMatrix.groupScheme (Fin n)`) over the separable closure `K^s`.
Then there are a central division `K`-algebra `D` of degree `d`, an integer
`m` with `m d = 2n`, an orthogonal involution of the first kind `σ` of `D`
(`dim Sym(σ) = d(d+1)/2`) and a nondegenerate `σ`-quadratic form `q` on
`D^m`. The isometry group `O(q)` is smooth and `H ≅ O(q)⁰`.

`SpecialOrthogonalAutomorphismStatement` says that every automorphism of the
split `SO_{2n}` over a field (`n ≥ 2`) is conjugation by a similitude `g`
(`g Q gᵀ − μ Q` alternating). It is a published statement; its proof is the
separate Task 6568. This module only assumes it.

## Proof

The proof chains the theorems of `EvenOrthogonalForm/*` and
`OrthogonalInnerForm/*`. Write `O_{2n}` for the split orthogonal group scheme
`OrthogonalMatrix.groupScheme (Fin n) K`.

1. `exists_galois_localIso` (`GaloisStage`): the isomorphism over `K^s`
   descends to a finite Galois extension `N / K`. This gives local
   isomorphisms `φ` from `H` to the split `SO_{2n}` along
   `Spec N ⟶ Spec K`.
2. `exists_similitude_cocycle φ hS` (`SimilitudeCocycle`, needs `n ≥ 3`):
   by `hS`, the Galois twists of `φ` are conjugations by similitudes `g_σ`
   (`hconj`). The twisted maps `x ↦ g_σ⁻¹ σ(x) g_σ` compose like the Galois
   group (`hcoc`).
3. `exists_twistedChart g hcoc hsim` (`SplitChart`, needs `n ≠ 0`): the fixed
   algebra `A` of this twisted action is a finite-dimensional central
   simple `K`-algebra. The involution `x ↦ J xᵀ J` descends to an involution `τ` of
   `A`, and `e : N ⊗[K] A ≅ M_{2n}(N)` satisfies `e(τ_N x) J = J e(x)ᵀ`.
   The base point `a₀ = Σ_σ θ_σ(c p)` (trace average of `p = diag(1, 0)`,
   with `Tr(c) = 1`) has `a₀ + τ a₀ = 1`. Local isomorphisms `χ` go from the
   isometry cut of `(A, τ, a₀)` to `O_{2n}`, and the values of `χ` at
   `s ≫ σ*` and at `s` differ by conjugation by `g_σ` (`hχ`).
4. `orthogonalInvolutionHermitian τ e he` (`OrthogonalInvolutionHermitian`)
   gives `D`, `d`, `m`, `σ` with the dimension conditions, an invertible
   hermitian `H_m ∈ M_m(D)`, and `φ_A : A ≅ M_m(D)` carrying `τ` to the
   adjoint involution of `H_m`.
5. `q := [φ_A(a₀) H_m]` is nondegenerate (`isNondegenerateQuadratic_mk_mul`).
   `isometryCutAlgEquivIso` identifies the isometry cut of `(A, τ, a₀)` with
   `O(q)` (`QuadraticTransport`).
6. Smoothness: the isometry cut is affine (it is a `Spec`). It is smooth
   because it has local isomorphisms `χ` to the smooth group `O_{2n}`
   (`smooth_of_localGroupIso`). So `O(q)` is smooth (`smooth_of_groupIso`).
7. `nonempty_iso_identityComponent φ g hconj χ hχ` (`FormDescent`): the
   comparison `s ↦ χ⁰(s)⁻¹ ∘ φ(s)` is Galois invariant, since both `φ` and
   `χ` twist by the same `g_σ`. It descends to `H ≅ (isometry cut)⁰`.
   Composing with `IdentityComponent.mapIso` of the isomorphism of step 5
   gives `H ≅ O(q)⁰ = σ.connectedIsometryGroup q`.

No characteristic hypothesis is used.

## Provenance

Derived. This is the classification of forms of `SO_{2n}` by central simple
algebras with quadratic pair (M.-A. Knus, A. Merkurjev, M. Rost and
J.-P. Tignol, *The Book of Involutions*, 1998, source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`: §29.D, printed p.399 /
PDF p.422, and §29.F, printed p.408 / PDF p.431). It is combined with
the description of a quadratic pair on `M_m(D)` by a `σ`-quadratic form
(KMRT §5.B, printed p.55 / PDF p.78; J. Tits, *Formes quadratiques, groupes
orthogonaux et algèbres de Clifford*, Invent. Math. 5 (1968), §2.2). The
automorphism theorem `Aut(SO_{2n}) = PGO_{2n}` (KMRT (26.15)–(26.16),
printed p.371 / PDF p.394) enters as the hypothesis `hS`. The
implementation does not construct quadratic pairs: the quadratic class is
the class of the base point `a₀` modulo the alternating elements of `τ`,
which the twisted-descent unit obtains by trace averaging.
