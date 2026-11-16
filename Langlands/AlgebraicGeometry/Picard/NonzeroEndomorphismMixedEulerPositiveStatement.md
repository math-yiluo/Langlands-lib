# Mixed Euler positivity for nonzero endomorphisms

`Langlands.AbelianScheme.NonzeroEndomorphismMixedEulerPositiveStatement` is a proof target over every algebraically closed characteristic-zero field `k : Type u`. It quantifies an actual abelian scheme `A` over `Spec k`, a natural number `g > 0` and the property `A.HasRelativeDimension g`, which is the existing `SmoothOfRelativeDimension g A.X.hom`. It then quantifies every actual ample line bundle `L` on `A.X.left` and every nonzero actual abelian-scheme endomorphism `f`.

The conclusion is strict positivity of

`mixedLineBundleEulerCoefficient A.X.hom L ((LineBundle.pullback (hom f)).obj L) g`.

Here `hom f` is the underlying scheme morphism, and `LineBundle.pullback` is the actual sheaf pullback functor on locally free rank-one sheaves. The mixed coefficient is the coefficient at `g - 1` of the canonical coherent Euler polynomial of `f*L` twisted by powers of `L`, minus the canonical pure Euler polynomial of `L`. Thus its evaluations, under the resulting dimension bound, are `χ(f*L ⊗ L^n) - χ(L^n)`. No trace, Rosati operation, supplied intersection pairing or supplied positive form occurs in this statement.

This is a derived reformulation of the geometric positivity used in Milne, *Abelian Varieties*, author revision January 2, 2022, Theorem 17.3, printed and one-based PDF pp.35–36, with the normalization supplied by Theorem 13.3(b), p.25 (registered source `milne-abelian-varieties-1986-author-2022`). Writing `L = O(D)`, Riemann–Roch identifies the selected difference coefficient with `(D^(g-1) · f*D)/(g-1)!`. The term from the pure Euler polynomial cancels the contribution independent of the coefficient bundle. For a nonzero endomorphism the pullback class has positive intersection with `g - 1` copies of an ample class, as in Milne's geometric argument preceding Lemma 17.4. The theorem must justify this actual geometric positivity and its passage to the canonical Euler polynomial; it cannot assume the Rosati positivity theorem that this input is intended to support. The registered errata snapshot says its corrections are incorporated in the cited author revision.

The positive-dimensional scope is explicit because this statement isolates that step of the geometric proof. It makes no assertion for `g = 0`; the final Rosati positivity target still includes dimension zero. This file only defines the proposition and supplies no proof.
