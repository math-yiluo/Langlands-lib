# Axiom V 3 for the Chevalley root function family

Author: Worker 1620.

Lean module: `Langlands.Geometry.Building.ChevalleyRootFamilyCommutator`.

## Setting

`G` is a Chevalley group (`D.ChevGroup k`) over a field `k`, for a finite reduced root datum
with finite free weight lattice. `G.H` is affine and locally of finite type. `omega` is an
additive valuation of `k` with values in `WithTop ℝ`, and `family G omega` is the published
Chevalley root function family (`ChevalleyRootFamily`).

## Content

### Matrix realization

- `glHom G : rationalPoints G.H →* GL (Fin D.n) Γ(Spec k, ⊤)` sends `g` to the matrix of
  `g ≫ G.i`. It is injective (`glHom_injective`) and sends `G.rootPt j s` to
  `D.x j (ΓSpecIso.inv s)` (`glHom_rootPt`).
- `omegaΓ omega` is `omega` transported to the global sections, with `omegaΓ_inv`.
- `rootPt_add` and `rootPt_neg` follow.

### Filtration sets

- `mem_rootFiltration_root_iff`: the filtration set of the root character `charOf (root j)` at
  level `r` consists of the points `G.rootPt j s` with `omega s ≥ r`.
- `filtrationSubgroup`: this set as a subgroup.
- `closure_rootFiltration`: the closure of the filtration set is this subgroup.

### Two independent roots

- `pairHeight i j = (2 - ⟨i, j^∨⟩) ⟨·, i^∨⟩ + (2 - ⟨j, i^∨⟩) ⟨·, j^∨⟩ : X →+ ℤ`. It takes the
  value `4 - ⟨i, j^∨⟩⟨j, i^∨⟩` on both roots (`pairHeight_root_left`, `pairHeight_root_right`).
- `pairing_mul_pairing_lt_four`: this value is positive when `i ≠ j` and `root i ≠ -root j`.
  The proof uses Mathlib's `coxeterWeightIn_le_four` and `coxeterWeightIn_ne_four`.
- `pairFunctional` and `exists_pairFunctional`: a real functional with prescribed values `r, s`
  on the two roots. It is obtained by solving a 2 × 2 system with determinant
  `4 - ⟨i, j^∨⟩⟨j, i^∨⟩`.
- `pairCone i j`, the roots `p i + q j` with `p, q ≥ 1`, with `mem_pairCone`.
  `isClosedPositive_pairCone`: this set is closed and positive for any `h` positive on `i` and
  `j`.

### Main results

- **`commutator`**: the V 3 field of `IsRootDatumValuation` for `family G omega`, stated exactly
  as the field. For roots `a, b` with `1 ⊗ b ≠ -(t • 1 ⊗ a)` for all `t > 0`, the commutator
  subgroup `⁅⟨U_{a,r}⟩, ⟨U_{b,s}⟩⁆` lies in the closure of the union of the
  `U_{pa+qb, pr+qs}` over `p, q > 0` with `pa + qb` a root.
- **`isRootDatumValuation`**: `IsRootDatumValuation G.t (family G omega)`, assuming
  `3 ≤ (Set.range omega).encard`, `IsAffineHom G.H.X.hom` and `Mono G.t.hom.hom.left`. All
  fields come from the published `ChevalleyRootFamily` and `ChevalleyRootFamilyRankOne` and from
  `commutator`.

## Proof of `commutator`

By `Subgroup.commutator_le`, it suffices to treat the commutator of `x = rootPt i x₀` and
`y = rootPt j y₀` with `omega x₀ ≥ r` and `omega y₀ ≥ s`. There are three cases.

1. **`i = j`.** The commutator is `1`, because root points of one root commute (`rootPt_add`).
2. **`root i = -root j`.** Then `b = -a`, and the hypothesis fails at `t = 1`.
3. **Otherwise.** Let `h = pairHeight i j`, which is positive on both roots. Let `θ` be a real
   functional with `θ(i) = r` and `θ(j) = s`.
   - In `GL_n(Γ)` the commutator `C` lies in `rootsSub (pairCone i j)`
     (`commutator_mem_rootsSub_ring`).
   - By `exists_listProd_of_mem_rootsSub`, `C` is an ordered product
     `∏_{γ ∈ heightList} x_γ(w γ)`.
   - `C` is a product of four `θ`-bounded root elements, so it is `θ`-bounded
     (`normBound_divExp`, `normBound_mul`).
   - By `le_of_normBound_listProd`, every coefficient satisfies `v(w γ) ≥ θ(γ)`. Here
     `θ(γ) = p r + q s` for `γ = p i + q j`.
   - Injectivity of `glHom` turns the matrix identity into the identity
     `[x, y] = ∏ rootPt γ (w γ)` in `rationalPoints G.H`. Each factor lies in
     `U_{pa+qb, pr+qs}`, because `charOf (root γ) = p • a + q • b`.

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §6.1, state after Lemma 6.1.1
that the properties of that lemma and the commutation relations of their Construction 2.9.16(d)
make the Chevalley collection of a split group a valuation of the root datum in the sense of
their Definition 6.1.2. The Lean proof of V 3 is internal. It replaces the structure constants
of the commutation relations, which the published `ChevalleyData.commutator` field does not
record, with the matrix bounds of `RootValuationBounds`.
