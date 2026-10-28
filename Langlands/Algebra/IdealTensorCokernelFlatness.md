# Flatness of a cokernel from ideal-quotient tensor injectivity

`Langlands.Algebra.idealTensorCokernelFlatness` proves the published
proposition `Langlands.Algebra.IdealTensorCokernelFlatnessStatement.{u, v, w}`
(module `Langlands.Algebra.IdealTensorCokernelFlatnessStatement`) exactly,
with its three independent universes and every hypothesis unchanged.

Worker 678 wrote the Lean proof as a prototype in the draft of the parent
proof task `90c1db03-0049-445e-9845-423d7fb17ea0`. Worker 281 submits it
unchanged against the published statement; Worker 666 drafted that
statement.

## Statement proved

Let `R : Type u` be a commutative ring, `A : Type v` and `B : Type w` be
`R`-modules, and `f : A →ₗ[R] B` be `R`-linear. Assume that `B` is flat
over `R`, that `f` is injective, and that for every ideal `I : Ideal R`
the actual tensor map `LinearMap.lTensor (R ⧸ I) f` is injective. Then the
actual quotient `B ⧸ LinearMap.range f` is flat over `R`.

## Implemented proof

Write `M = B ⧸ LinearMap.range f` and `q : B →ₗ[R] M` for the quotient
map `(LinearMap.range f).mkQ`. Then `q` is surjective and the sequence
`A → B → M` is exact at `B`, because the kernel of `q` is the range of
`f`. The proof uses tensor right exactness and Mathlib's ideal criterion
for flatness. It does not use Tor.

By `Module.Flat.iff_rTensor_injective'`, it suffices to show that for
every ideal `I` the map `rTensor M I.subtype : I ⊗ M → R ⊗ M` is
injective. Let `x ∈ I ⊗ M` map to zero in `R ⊗ M`.

1. *Lift to `I ⊗ B`.* `LinearMap.lTensor_surjective` makes `I ⊗ q`
   surjective, so `x = (I ⊗ q)(y)` for some `y ∈ I ⊗ B`.
2. *Pass to `R ⊗ B`.* The tensor maps commute:
   `(R ⊗ q) ∘ (ι ⊗ B) = (ι ⊗ M) ∘ (I ⊗ q)`, where `ι : I → R` is the
   inclusion. This is proved by `ext; simp`. So `(ι ⊗ B)(y)` is in the
   kernel of `R ⊗ q`. Right exactness of `R ⊗ -` (the root-namespace
   lemma `lTensor_exact`) writes `(ι ⊗ B)(y) = (R ⊗ f)(a)` for some
   `a ∈ R ⊗ A`.
3. *Use the hypothesis on `R ⧸ I`.* `(I.mkQ ⊗ B)(R ⊗ f)(a)` equals
   `(I.mkQ ∘ ι ⊗ B)(y)`, and this is zero because `I.mkQ ∘ ι = 0`. The
   naturality square
   `((R ⧸ I) ⊗ f) ∘ (I.mkQ ⊗ A) = (I.mkQ ⊗ B) ∘ (R ⊗ f)` (again
   `ext; simp`) then gives `((R ⧸ I) ⊗ f)((I.mkQ ⊗ A)(a)) = 0`. The
   assumed injectivity of `LinearMap.lTensor (R ⧸ I) f` yields
   `(I.mkQ ⊗ A)(a) = 0`.
4. *Lift `a` to `I ⊗ A`.* Right exactness of `- ⊗ A` applied to
   `I → R → R ⧸ I → 0` (the root-namespace lemma `rTensor_exact` with
   `LinearMap.exact_subtype_mkQ`) gives `c ∈ I ⊗ A` with
   `(ι ⊗ A)(c) = a`.
5. *Use flatness of `B`.* By naturality,
   `(ι ⊗ B)((I ⊗ f)(c)) = (R ⊗ f)((ι ⊗ A)(c)) = (R ⊗ f)(a) = (ι ⊗ B)(y)`.
   Since `B` is flat, `ι ⊗ B` is injective
   (`Module.Flat.rTensor_preserves_injective_linearMap`), so
   `(I ⊗ f)(c) = y`.
6. *Conclude.* `x = (I ⊗ q)(y) = (I ⊗ (q ∘ f))(c) = 0`, because
   `q ∘ f = 0`.

The injectivity hypothesis on `f` itself is not used; the binder is named
`_hf`. The proof adds no hypotheses. It needs no locality, Noetherian,
finiteness, finite-presentation, flatness-of-`A` or nonzero-module
assumptions. It works with the actual maps `LinearMap.lTensor` and
`LinearMap.rTensor` and the actual range quotient, and it proves every
naturality equality directly. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The proposition is a derived interface for the final paragraph of the
proof of Stacks Project, Commutative Algebra, Lemma 10.99.1
([00ME](https://stacks.math.columbia.edu/tag/00ME)), registered source
`stacks-algebra-flatness-criteria-2026-10-22`, file `00MD.html`,
Section 10.99, the paragraph beginning "To show that `M/u(N)` is flat
over `R`". Stacks reduces to the vanishing of `Tor_1^R(M/u(N), R/I)`
(Lemma 10.75.8). It then uses the long exact Tor sequence (Lemma 10.75.2)
and the flatness of `M` to embed that Tor group into the kernel of
`N/IN → M/IM`. The Lean proof follows the same idea without Tor. Steps 1
to 6 are an element-level diagram chase. They show directly that the
kernel of `I ⊗ M → R ⊗ M` vanishes once every `(R ⧸ I) ⊗ f` is
injective.
