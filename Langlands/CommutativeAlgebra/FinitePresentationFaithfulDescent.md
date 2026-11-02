# Faithfully flat descent, localization spreading and presentations of modules

Author: Worker 766.

This module is `Langlands.CommutativeAlgebra.FinitePresentationFaithfulDescent`.
It imports only Mathlib. All declarations are in the namespace
`Langlands.CommutativeAlgebra`.

## Purpose and provenance

The module collects three pieces of commutative algebra used by the scheme
module `Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent`. That
module proves that local finite presentation of a module sheaf descends along a
flat, locally finitely presented surjection of schemes. The results here are
standard facts of commutative algebra. Their statements and proofs were written
for this development from the Mathlib API, and no literature theorem is cited.

## Declarations

### Descent of finite presentation

- `finitePresentation_of_finitePresentation_tensorProduct`: let `S` be a
  faithfully flat `R`-algebra and `M` an `R`-module. If `S ⊗[R] M` is finitely
  presented over `S`, then `M` is finitely presented over `R`.

  Proof. Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`
  shows that `M` is finite, so there is a surjection `π : Rⁿ → M`
  (`Module.Finite.exists_fin'`). Let `K` be its kernel. Since `S` is flat, the
  base change `S ⊗ K → S ⊗ Rⁿ` is injective, and `S ⊗ K → S ⊗ Rⁿ → S ⊗ M → 0`
  is exact (`lTensor_exact`). So `S ⊗ K` is isomorphic to the kernel of the
  surjection `S ⊗ π`. That kernel is finitely generated, because `S ⊗ M` is
  finitely presented (`Module.FinitePresentation.fg_ker`). Finiteness descends
  again from `S ⊗ K` to `K`, and `Module.finitePresentation_of_surjective`
  concludes.

### Spreading bijectivity from a prime

- `bijective_map_of_bijective_away`: let `l : A →ₗ[R] B` and `g : R`. Suppose
  the map `LocalizedModule.map (Submonoid.powers g) l` of localizations at the
  powers of `g` is bijective. Then for every prime `p` with `g ∉ p`, and for
  every choice of localization maps `fA : A → Ap` and `fB : B → Bp` at
  `p.primeCompl` (as `IsLocalizedModule` instances), the induced map
  `IsLocalizedModule.map p.primeCompl fA fB l` is bijective.

  Proof. From bijectivity away from `g`, two elementwise facts follow. If
  `l a = 0`, then some power of `g` kills `a`. Every `b` satisfies
  `t • b = l a` for some `a` and some power `t` of `g`. Powers of `g` lie
  outside `p`. Injectivity and surjectivity at `p` then follow by writing
  elements of `Ap` and `Bp` as fractions (`IsLocalizedModule.mk'_surjective`,
  `mk'_eq_zero'`, `map_mk'`, `mk'_cancel_left`).
- `exists_notMem_forall_bijective`: let `A` be finite and `B` finitely
  presented over `R`, and `l : A →ₗ[R] B`. If the localized map is bijective at
  one prime `p₀`, for some localization maps at `p₀`, then there is `g ∉ p₀`
  such that the localized map is bijective at every prime `p` with `g ∉ p`, for
  every choice of localization maps at `p`. The proof combines Mathlib's
  `Module.FinitePresentation.exists_notMem_bijective`, which gives bijectivity
  after inverting `g`, with the previous lemma.

### Presentations

- `bijective_of_presentation`: let `P` and `B` be modules over a commutative
  ring `O`, let `x : Fin n → P` span `P`, and let `ρ : Fin m → Fin n → O` be
  relation vectors with `∑ k, ρ j k • x k = 0` for every `j`. Let
  `ℓ : P →ₗ[O] B` be such that the family `ℓ ∘ x` spans `B`. Suppose every
  coefficient vector `c` with `∑ k, c k • ℓ (x k) = 0` lies in the span of the
  vectors `ρ j`. Then `ℓ` is bijective.

  Proof. The linear combination map `L : Oⁿ → P` of `x` is surjective and
  kills the span of the `ρ j`. If `ℓ (L c) = 0`, the hypothesis puts `c` in that
  span, so `L c = 0`. This gives injectivity. Surjectivity holds because the
  range of `ℓ` contains the spanning family `ℓ ∘ x`.
- `span_eq_top_of_surjective`: let `σ : O → O'` be a surjective ring map and
  let `P` be a module over both rings with `o • z = σ o • z`. A set that spans
  `P` over `O'` also spans `P` over `O`. The proof is by induction on span
  membership.
