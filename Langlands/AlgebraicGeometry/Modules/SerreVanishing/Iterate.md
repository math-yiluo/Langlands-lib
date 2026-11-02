# Iterated twisting by a line bundle, and the twist-killing statement

Internal infrastructure for the proof of `SectionKillingStatement` (module
`SerreVanishing.Twist`), which is the section-killing input of the Serre vanishing
theorem for two ample line bundles.

For an `𝒪_X`-module `N` and a global section `s : GlobalSections N`:

- `twistMul_naturality`: multiplication by `s`, `twistMul N s A : A ⟶ A ⊗ N`, is natural
  in `A`: `twistMul N s A ≫ (g ⊗ 𝟙 N) = g ≫ twistMul N s B` for `g : A ⟶ B`.
- `twistIter N k : X.Modules ⥤ X.Modules` is tensoring `k` times on the right with `N`:
  `twistIter N 0 = 𝟭`, `twistIter N (k + 1) = twistIter N k ⋙ tensorBy N`, so
  `(twistIter N k).obj Z = (⋯((Z ⊗ N) ⊗ N)⋯) ⊗ N`.
- `stepNat N s k : twistIter N k ⟶ twistIter N (k + 1)` has components
  `twistMul N s ((twistIter N k).obj Z)`.
- `twistPow N s k : 𝟭 ⟶ twistIter N k` is multiplication by `s ^ k`:
  `twistPow N s 0 = 𝟙`, `twistPow N s (k + 1) = twistPow N s k ≫ stepNat N s k`
  (`twistPow_succ_app`).

`TwistKillingStatement` is the proposition: for every field `K`, every proper
`f : X ⟶ Spec K`, every locally free rank-one `N` with a global section `s` whose
trivialization locus `trivializationOpen N s` is affine, every quasi-coherent `Z`, every
`p` and every class `ξ ∈ H^{p+1}(X, Z)` (`DerivedSections.relativeCohomology f (p + 1)`),
there is `k` with `H^{p+1}((twistPow N s k).app Z) ξ = 0`.

## Provenance

This is Stacks Project, Lemma 30.17.4, tag
[01XR](https://stacks.math.columbia.edu/tag/01XR): for `X` quasi-compact and
quasi-separated, `s` a section of an invertible module with `X_s` affine, and `F`
quasi-coherent, every class in `H^p(X, F)`, `p > 0`, is killed by a power of `s`. Here it
is specialized to a proper scheme over a field, which is quasi-compact and separated, and
written with the explicit right-nested twists `twistIter`. The statement is
derived for internal use: it is the form proved by dimension shifting through the Čech
term of an affine cover; `SectionKillingStatement` is then deduced from it.
