# A split Cartan subalgebra and a parabolic element of the complexified Lie algebra of `G(F_∞)`

Module `Langlands.Global.InfiniteAdelicSplitCartanStatement` contains one `Prop`-valued
definition and no theorems.

```lean
def InfiniteAdelicSplitCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine M'.X.left]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ M'),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    IsMaximalTorus t →
    ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      ... ∃ H : LieSubalgebra ℂ 𝔤,
        H.toSubmodule = tangentSpan (Set.range (T(F_∞) → G(F_∞) along t ≫ l' ≫ q)) ∧
        IsSplitCartan H ∧
        ∃ X ∈ H,
          (∀ c : ℂ, (LieAlgebra.ad ℂ _ X).eigenspace c ≠ ⊥ → ∃ n : ℤ, c = n) ∧
          LinearMap.ker (LieAlgebra.ad ℂ _ X) = tangentSpan (Set.range (M'(F_∞) → G(F_∞))) ∧
          positiveEigenSubmodule X = tangentSpan (Set.range (V(F_∞) → G(F_∞)))
```

The elided part `...` introduces `Ainf = F_∞` (`InfiniteAdeleRing F` as an `F`-algebra), the
Library's archimedean Lie group structure on `G(F_∞)` for `hsmooth` (`smoothChartedSpace`,
`smoothLieGroup`, the `RCLike` structures of the archimedean completions), and the abbreviation

```lean
tangentSpan S = Submodule.span ℂ ((fun X => (1 : ℂ) ⊗ₜ[ℝ] X) '' curveTangents F hsmooth S).
```

The point maps are `GroupScheme.affinePointsTarget` at `Ainf` along `t ≫ l' ≫ q`, `l' ≫ q` and
`iV ≫ q`.

## Meaning

- `G` is a connected reductive group over the number field `F`, `q : Q → G` is a parabolic
  subgroup, `iV : V → Q` its geometric unipotent radical and `l' : M' → Q` a rational Levi
  subgroup. `t : T → M'` is a maximal torus of `M'` defined over `F` (`IsMaximalTorus`: `T` is a
  torus, `t` is a closed subgroup, and `t` factors through no strictly larger closed torus).
- `𝔤 = ℂ ⊗_ℝ 𝔤_ℝ`, where `𝔤_ℝ = GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`
  is the real Lie algebra of the real Lie group `G(F_∞)`, with Mathlib's extension of scalars.
- `curveTangents F hsmooth S` (module `InfiniteAdelicLeviEnveloping`) is the set of velocities
  `c'(0)` of smooth curves `c : ℝ → G(F_∞)` with `c(0) = 1` and values in `S`. So
  `tangentSpan S` is the complexified tangent space at `1` of `S` when `S` is the image of a
  closed subgroup. The three subspaces in the statement are the complexified Lie algebras of
  `T(F_∞)`, `M'(F_∞)` and `V(F_∞)`, embedded in `𝔤`.
- `IsSplitCartan` (module `Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement`) says:
  `𝔥` is abelian, the weight spaces `𝔤_χ = {x | [h, x] = χ(h) x for all h ∈ 𝔥}` of the functions
  `χ : 𝔥 → ℂ` span `𝔤`, and the zero weight space is `𝔥`. A root is a function `α ≠ 0` with
  `𝔤_α ≠ 0`. Every root space `𝔤_α` is a line. Every root `α` has `e ∈ 𝔤_α`, `f ∈ 𝔤_{-α}` and
  `h ∈ 𝔥` with `[e, f] = h` and `α(h) = 2`. For a root `α` and `c ≠ 0` with `𝔤_{cα} ≠ 0` one
  has `c = ±1`.
- `positiveEigenSubmodule X` (same module) is the sum of the eigenspaces of `ad X` for the
  eigenvalues `1, 2, 3, …`.

The statement asserts: the complexified Lie algebra `𝔥` of `T(F_∞)` is a Lie subalgebra of `𝔤`
with these properties, and it contains an element `X` such that `ad X` has only integer
eigenvalues, its kernel is the complexified Lie algebra of `M'(F_∞)`, and its positive
eigenspaces span the complexified Lie algebra of `V(F_∞)`.

## Provenance

Derived. The source facts are the structure of parabolic subgroups through cocharacters and the
root theory of split reductive groups. They are combined through the decomposition of the
complexified Lie algebra over the complex embeddings of `F`.

*The element `X`.* A parabolic subgroup `Q` with Levi subgroup `M'` is `P_G(ψ)` for a cocharacter
`ψ` of the center of `M'`, with `M' = Z_G(ψ)` and `V = U_G(ψ)` (Milne, *Algebraic Groups* (2017),
Theorem 25.1, printed p. 544). The Lie algebras of `Z_G(ψ)` and `U_G(ψ)` are the weight-zero
space and the sum of the positive weight spaces of `𝔾_m` acting on `Lie G` through `ψ`
(Conrad–Gabber–Prasad, *Pseudo-reductive Groups* (2015), Proposition 2.1.8 (1), printed p. 53).
Since `ψ` is central in `M'`, it factors through `T`. `X` is the complexified tangent vector of
`ψ` at `1`. On the `n`-th weight space `ad X` acts by `n`, which gives the three properties of
`X`.

*The subalgebra `𝔥`.* For an embedding `σ : F → ℂ`, the base change `G_σ = G ×_{F,σ} ℂ` is
connected reductive and `T_σ` is a maximal torus, split because `ℂ` is algebraically closed.
Since `ℂ ⊗_ℝ F_∞ ≅ ℂ ⊗_ℚ F ≅ ∏_{σ : F → ℂ} ℂ`, one has `𝔤 ≅ ∏_σ Lie(G_σ)` and
`𝔥 ≅ ∏_σ Lie(T_σ)`. For the split reductive group `(G_σ, T_σ)` over `ℂ`:

- `Lie(G_σ) = Lie(T_σ) ⊕ ⊕_{α ∈ Φ} 𝔤_α` (Milne 2017, Corollary 21.13 and its proof, printed
  p. 430). In characteristic zero distinct characters have distinct differentials, so the torus
  weight spaces are the weight spaces of `Lie(T_σ)`.
- Each root space `𝔤_α` is a line, and the only rational multiples of `α` in `Φ` are `±α`
  (Theorem 21.11 (b), printed p. 428). The root datum is reduced (Corollary 21.12, printed
  p. 430).
- Let `G_α = C_{G_σ}((ker α)°)`, the centralizer of the codimension-one subtorus of `T_σ`. The
  proof of Theorem 21.11 constructs a central isogeny `v_α : SL₂ → G_α'` onto the derived
  group `G_α'` of `G_α`, with `v_α(diag(x, x⁻¹)) = α^∨(x)` and `⟨α, α^∨⟩ = 2` (Theorem 21.11
  (b), (e) and its proof, printed pp. 428–430; 21.24, printed p. 432). Composed with the
  inclusion `G_α' ⊆ G_σ`, its differential carries the standard triple of `𝔰𝔩₂` to
  `e ∈ 𝔤_α`, `f ∈ 𝔤_{-α}` with `[e, f] = dα^∨(1)` and `dα(dα^∨(1)) = 2`.

In `∏_σ Lie(G_σ)` the roots of `∏_σ Lie(T_σ)` are the roots of one factor, extended by zero on
the other factors. All six properties of `IsSplitCartan` therefore follow factor by factor. The
semisimple analogue is Humphreys, *Introduction to Lie Algebras and Representation Theory*,
§8.3 (f) and §8.4 (a), (b), printed pp. 38–39. Describing the complexified Lie algebras through
curve tangents of images in `G(F_∞)` is internal.
