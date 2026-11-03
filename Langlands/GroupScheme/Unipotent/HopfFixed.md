# Invariant vectors in unipotent coordinate bialgebras

Worker 1395 wrote this module. It holds internal linear-algebra helpers for the Hopf-algebraic
treatment of unipotent group schemes in `Langlands.GroupScheme.Unipotent.*`. It asserts nothing
new from the literature. Throughout, `K` is a field and `B` a `K`-coalgebra or `K`-bialgebra.
`rightAct f b = ∑ f(b₂) • b₁` and `leftAct θ b = ∑ θ(b₁) • b₂` are the Library's translation
operators from `Langlands.GroupScheme.AffineLinearEmbedding.Comodule`, where
`comul b = ∑ b₁ ⊗ b₂`. `regularSpan` is the Library's span of right translates from
`Langlands.GroupScheme.Chevalley.RegularSubspace`.

## The predicate `OneMemStable`

`OneMemStable K B` (an `abbrev` of type `Prop`) says: every nonzero finite-dimensional subspace
`V` of `B` that is stable under all right translations `rightAct f` contains `1`. This is an
internal definition. It is the coordinate-algebra form of the Library's `IsUnipotent`, which says
that every nonzero finite-dimensional representation has a nonzero fixed vector (Milne,
*Algebraic Groups* (2017), 6.45 and 14.3). A stable subspace `V` is a subcomodule of the regular
representation, and a fixed vector in it is a multiple of `1` (`eq_counit_smul_one_of_invariant`).
`Unipotent.CoordinateBialgebra` proves the two directions of this correspondence for corepresented
group schemes. Nothing in this module needs a finite-type hypothesis.

## Contents

* `eq_of_forall_dual`: functionals separate vectors. `one_ne_zero'`: a bialgebra over a field is
  nonzero, because the counit sends `1` to `1`.
* Coalgebra identities: `counit_leftAct` (`ε (leftAct θ a) = θ a`), `leftAct_leftAct`
  (coassociativity: `leftAct ψ ∘ leftAct θ = leftAct (ψ ∘ leftAct θ)`, proved by separating with
  functionals and `apply_leftAct`), `leftAct_smul`, and `map_leftAct`
  (`φ (leftAct (χ ∘ φ) b) = leftAct χ (φ b)` for a coalgebra map `φ`, by induction on the
  comultiplication tensor). `leftAct_coord_of_grouplike`: if `g` is a basis of grouplike
  elements (`comul (g i) = g i ⊗ g i`), then `leftAct (g.coord i) c = g.coord i c • g i`. This is
  checked on basis vectors.
* Bialgebra identities: `rightAct_one` and `leftAct_one` (`rightAct f 1 = f 1 • 1`, from
  `comul 1 = 1 ⊗ 1`). `eq_counit_smul_one_of_invariant`: if `rightAct g b = g 1 • b` for all
  `g`, then `b = ε(b) • 1`. The hypothesis gives `leftAct ψ b = ψ b • 1` for every `ψ`, by
  separating with functionals; then take `ψ = ε`.
* `exists_invariant`: `hB : OneMemStable K B` is given. Let `M` be a `K`-module with operators
  `T g` indexed by `g : Module.Dual K B`, and let `π i : M → B` be a jointly injective family of
  linear maps with `π i ∘ T g = rightAct g ∘ π i`. Then every nonzero finite-dimensional
  `T`-stable subspace `W` of `M` contains a nonzero `w` with `T g w = g 1 • w` for all `g`.
  The proof is strong induction on `finrank W`. Pick `w₀ ≠ 0` in `W` and an `i` with
  `π i w₀ ≠ 0`. If `W ∩ ker (π i) = 0`, then `π i (W)` is a nonzero finite-dimensional stable
  subspace of `B`, so it contains `1 = π i w`. Then `T g w - g 1 • w` lies in
  `W ∩ ker (π i) = 0`. Otherwise `W ∩ ker (π i)` is a smaller nonzero stable subspace, and
  induction applies.
* `bialgHom_eq_algebraMap_counit`: `hB : OneMemStable K B` is given. Let `φ : B →ₐc[K] C` be a
  bialgebra map into a bialgebra `C` with a basis `g` of grouplike elements. Then
  `φ f = algebraMap K C (ε f)` for every `f`. Write `W i` for the `g i`-weight space of the
  left action of `C`-functionals pulled back along `φ`:
  `leftAct (χ ∘ φ) x = χ (g i) • x`. The components `x i = leftAct (g.coord i ∘ φ) f` lie in
  `W i`, by `leftAct_leftAct`, `map_leftAct` and `leftAct_coord_of_grouplike`. Each `W i` is
  stable under right translations, since left and right translations commute. Suppose
  `g i ≠ 1` and `x i ≠ 0`. Then `regularSpan {x i} ⊆ W i` is a nonzero finite-dimensional stable
  subspace, so it contains `1` by `hB`. But `1 ∈ W i` forces `χ 1 = χ (g i)` for all `χ`,
  i.e. `g i = 1`, a contradiction. Hence the `i`-th coordinate of `φ f`, which is `ε (x i)` by
  `counit_leftAct`, vanishes unless `g i = 1`. So `φ f = c • 1`, and applying the counit gives
  `c = ε f`.
* Transfer: `map_rightAct` (a linear map compatible with the comultiplications intertwines right
  translations), and `OneMemStable.of_linearEquiv`. `OneMemStable` transfers along a linear
  equivalence `φ : B ≃ C` with `φ 1 = 1` that is compatible with the comultiplications: pull a
  stable subspace of `C` back along `φ`.
