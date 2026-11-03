# A double coset from the limit of a cocharacter orbit in a subgroup quotient

This internal module proves the cell step of the limit proof of the Bruhat
covering. Work over a field `k` with a group scheme `G`, a subgroup
`iP : P ⟶ G` and a quotient morphism `q : G.X ⟶ Q`. The fibres of `q` are the
`P`-cosets, in the form of the hypothesis

`hfib : g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iP).carrier T`

for all test points `g h : T ⟶ G.X`. `G` acts on `Q` by `a : SchemeAction G Q`,
and `hact : a.act g (h ≫ q) = (g * h) ≫ q` says this is left translation. The
base point is `x₀ = 1 ≫ q`. The quotient, the action and both properties are
inputs, so the module does not depend on how the quotient is constructed. For
example, `Dynamic.flagQuotientSchemeAction` with
`Dynamic.flagQuotientSchemeAction_act_lift` provides `a` and `hact`.

## The stable cell

`isGmStable_cell`: let `iU : U ⟶ G` be a second subgroup and
`ψ : 𝔾_m ⟶ G` a cocharacter whose range lies in the range of `iP` and
normalizes the range of `iU`. Then the cell `iU ≫ q : U ⟶ Q`,
`u ↦ u · x₀`, is stable under `a.restrict ψ`, in the sense
`SchemeAction.IsGmStable`. For `s : T ⟶ 𝔾_m` and `z : T ⟶ U`, normalization
gives `z'` with `z' = ψ(s) z ψ(s)⁻¹` in `G`. By `hfib`, the points
`ψ(s) z · x₀` and `z' · x₀` agree because `ψ(s) ∈ P`.

## The cell argument

`exists_eq_mul_mul` takes:

- `hcell`: the multiplication `U × P ⟶ G`, `(u, p) ↦ u p`, is an open
  immersion;
- cocharacters `χ ψ` and a rational point `n` with `ψ ≫ (G.innerIso n).hom = χ`,
  i.e. `χ = n ψ n⁻¹`;
- `P(χ) ≤ P`; the range of `ψ` lies in `P` and normalizes `U`;
- `[IsSeparated Q.hom]`, `[Mono iP.hom.hom]`, and `q.left` surjective, flat and
  quasi-compact;
- a rational point `g` and an extension
  `e : Spec k ⊗ 𝔸¹ ⟶ Q` of the `χ`-orbit of `g · x₀`
  (`SchemeAction.IsGmOrbitExtension`) whose limit `Dynamic.evalZero e` equals
  `n · x₀`.

It concludes `∃ b₁ b₂ : Spec k ⟶ P.X, g = (b₁ ≫ iP) * n * (b₂ ≫ iP)`, i.e.
`g ∈ P n P`.

The Lean proof:

1. Translate by `n⁻¹`: `e' = n⁻¹ · e` extends the `ψ`-orbit of
   `n⁻¹ g · x₀`. This uses `χ(s) = n ψ(s) n⁻¹` (`comp_innerIso_hom`), the
   action laws, and `constantPoint` naturality. Its limit is
   `n⁻¹ n · x₀ = 1 · x₀`, which lies in the cell `U · x₀`.
2. The cell `iU ≫ q` is an open immersion: `QuotientCell.isOpenImmersion`
   applied to `hcell` and `hfib`. By `isGmStable_cell` it is `ψ`-stable, and
   it contains the value `x₀` of `e'` at `0`. The lift
   `SchemeAction.gmOrbitOpenLift` (from `SchemeActionLimit`) then factors `e'`
   as `f ≫ iU ≫ q` with `f : Spec k ⊗ 𝔸¹ ⟶ U`.
3. Evaluating `f` at `1` gives `u : Spec k ⟶ U` with
   `u · x₀ = n⁻¹ g · x₀`. So `hfib` gives `b₂` with `n⁻¹ g = u · b₂`.
4. Restricted to `𝔾_m`, `f` is the `ψ`-conjugation orbit of `u`. Both maps
   become equal after composing with the monomorphism `(iU ≫ q).left`, by
   normalization, `hfib` and the extension property of `e'`. Hence
   `f ≫ iU` extends the conjugation orbit, and `u ∈ P(ψ)`.
5. `Dynamic.mem_parabolic_conj` gives `n u n⁻¹ ∈ P(χ) ≤ P`, say
   `n u n⁻¹ = b₁`. Then `g = n u b₂ = b₁ n b₂`.

## The Borel-pair corollary

`exists_eq_mul_mul_of_mem_normalizerPoints` specializes this to the data of
the Bruhat-covering assembly. Here `G` is smooth and affine,
`i : B ⟶ G`, `j : T ⟶ G` for a commutative group scheme `T`, and
`ν : 𝔾_m ⟶ T` is a cocharacter with
`hP : (parabolic (ν ≫ j)).IsRepresentedBy i`. The point `n` is a rational point of
`normalizerPoints j`, and `e` extends the `(ν ≫ j)`-orbit of `g · x₀` with
limit `n · x₀`. The conclusion is again
`∃ b₁ b₂, g = (b₁ ≫ i) * n * (b₂ ≫ i)`. The proof sets:

- `κ = groupHom (powerHom (-1)) ≫ ν` and `iU = Affine.unipotentHom (κ ≫ j)`,
  which represents `U((ν ≫ j)⁻¹)` (`Affine.isRepresentedBy_unipotentHom`,
  using that `G.X.left` is affine). The published `oppositeCellStatement`
  gives `hcell`;
- `ρ = ν ≫ groupHom σ.symm.hom` for an automorphism `σ : T ≅ T` with
  `IsNormalizingPoint j n σ`, i.e. `j ≫ innerIso n = groupHom σ.hom ≫ j`
  (membership in `normalizerPoints j`). Then
  `ψ = ρ ≫ j` satisfies `ψ ≫ innerIso n = ν ≫ j`;
- the range of `ψ` lies in the centralizer of `ν ≫ j`
  (`range_comp_le_centralizer_comp`), hence in `P(ν ≫ j) = B`
  (`centralizer_le_parabolic`). It normalizes `U(κ ≫ j)`
  (`unipotent_isNormalizedBy_range_of_common_commutativeGroup`).

## Provenance and scope

The argument is a limit argument for flag varieties in the style of
Białynicki-Birula. After translating by `n⁻¹`, the cell `U · x₀` is an open
neighbourhood of `x₀` that is stable under the cocharacter `ψ`. It is not, in
general, contracted to `x₀`. For example, take `G = SL₂`, `B` upper
triangular, `ψ(t) = diag(t, t⁻¹)`, `n = 1` and `U` lower unipotent. Under
`G/B ≅ ℙ¹` the point `u₋(x) · x₀` is `[1 : x]` and `ψ(t) · [1 : x] = [t² : x]`,
which tends to `[0 : 1] ≠ x₀` when `x ≠ 0`. The proof uses only stability. The
extended orbit of `n⁻¹ g · x₀` takes the value `x₀` at `0`, which lies in the
stable open cell, so the stable-open lift puts the whole extension in the cell
(step 2). The lifted extension then shows that the corresponding `u ∈ U` lies in
`P(ψ)` (step 4), and so `g ∈ P n P` (step 5). This module states and proves
only that deduction, not the Bruhat decomposition itself. The Lean proof is an
internal deduction from the published opposite-cell theorem, the quotient-cell
open immersion, the dynamic parabolic conjugation lemma and the module
`SchemeActionLimit`. It assumes no existence of the quotient and no
properness; the orbit extension `e` and the normalizer point `n` are inputs.
It uses neither the rational Bruhat decomposition nor any statement that two
Borel subgroups contain a common maximal torus.
