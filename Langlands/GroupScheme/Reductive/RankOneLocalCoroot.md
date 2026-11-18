# The coroot of a rank-one open cell with a Weyl point

The setting is cell data `D : RankOneRootCellRelation.CellData k` over a field `k`. It consists
of:

- a group `G` and a commutative group `T` with a homomorphism `i : T ⟶ G`;
- root groups `xp, xm : 𝔾ₐ ⟶ G`, on which `T` acts by conjugation through `α` and `-α`;
- the condition that the cell multiplication `(Y, t, X) ↦ xm(Y) · t · xp(X)` is an open
  immersion.

We also have a `k`-point `n` of `G` that normalizes `T` through an automorphism `σ`
(`IsNormalizingPoint D.i n σ`).

The cell data and the normalizing point alone do not determine a coroot. For example, the
identity of `SL₂` normalizes the diagonal torus through `σ = id`, with the standard root
groups and open cell. But a reflection with `⟨α, h⟩ = 2` sends the nonzero root `α` to `-α`,
so it is not the identity. The main result `exists_coroot` therefore assumes all of the
following:

- `G` is locally of finite type over `k`, and its underlying scheme is connected;
- `i : T ⟶ G` is a monomorphism;
- `T` is a split torus;
- `α ≠ 0`;
- `σ^* α = -α`, that is, `σ.hom ≫ α = -α`.

Under these assumptions it builds a cocharacter `h` with `⟨α, h⟩ = 2` and `σ = 1 - α ≫ h`. It
uses no root-datum input and no global facts about roots. The intermediate steps need only
some of these assumptions, as listed in the sections below.

Separately, `exists_sq_eq_of_involution` shows that `n²` is a `k`-point of the torus. It does
not use cell data. Its hypotheses are that `i` represents the dynamic centralizer of some
cocharacter `ν` (`hC`), and that `n` normalizes `T` through an involution `σ`
(`σ ≫ σ = 1`, `hσ`).

The argument is internal to this development. In classical terms, the kernel of `α` lies in the
centre of a rank-one group, so the Weyl element acts on characters by a reflection along `α`.

## Kernel centrality

- `cu_kernelPoint`: `α` takes the value `1` on every point of its scheme-theoretic kernel
  `RelativeRoot.characterKernel D.α`. This comes from the kernel pullback square
  `kernel_isPullback`.
- `commute_cellPt`: a torus point `s` with `α(s) = 1` commutes with every point
  `xm(y) · t · xp(x)` of the open cell. It commutes with `xm(y)` and `xp(x)` by the weight
  relations `CellData.I_mul_B` and `CellData.I_mul_A`, and with `t` because `T` is commutative.
- `identityPoint_mem_range_cellMul`: the identity point of `G` lies in the image of the cell,
  as the image of `(1, 1, 1)`.
- `commute_kernelPoint`: if `G` is locally of finite type and connected, every point of
  `ker α` commutes with every point of `G`. This applies the Library result
  `MultiplicativeTypeCentralityPropagation.commute_of_unitOpen` to the homomorphism
  `ker α ⟶ T ⟶ G` and the open cell. That result says: if points of a group commute with all
  points of an open subscheme through the identity, then they commute with all points of a
  connected group.

## Integrality

- `kernelPoint_comp_eq`: since `n` commutes with the kernel points, `σ` fixes every point of
  `ker α`. Here `i` is a monomorphism.
- `comp_sub_mem_zmultiples`: for every character `χ`, `σ^* χ - χ ∈ ℤ α`. To see this, evaluate
  `σ^* χ - χ` at the universal point of the kernel, `Diagonalizable.kernelUniversalPoint`.
  Since `σ` fixes that point, the value is `1`. By
  `Diagonalizable.characterValue_kernelUniversalPoint` and
  `Diagonalizable.quotientUniversalCharacter_eq_one_iff`, a character is trivial at this point
  exactly when it lies in `ℤ α`. This step needs `T` to be a split torus.

## The coroot

`exists_coroot` adds two assumptions, `σ^* α = -α` and `α ≠ 0`. The character lattice of a
split torus is torsion-free (`IsSplitTorus.character_toRat_injective`), so the integer `m(χ)`
with `m(χ) α = σ^* χ - χ` is unique and additive in `χ`. Also `m(α) = -2`.

`IsSplitTorus.exists_hom_of_characterMap` turns the additive map `χ ↦ -m(χ) · 1` into a
cocharacter `h` with `h^* χ = -m(χ)` for every `χ`. Then:

- `⟨α, h⟩ = -m(α) = 2`;
- `σ = 1 - α ≫ h`, checked on characters with `IsSplitTorus.hom_ext_of_characters`. So `σ` is
  the Library reflection `latticeReflectionIso α h`.

## The square of the Weyl point

`exists_sq_eq_of_involution` generalizes the Library lemma
`RankOneRootCellRelation.exists_sq_eq_of_isNormalizingPoint`. Suppose the torus represents the
dynamic centralizer of some cocharacter `ν`, and `n` normalizes the torus through an involution
`σ`. Then `n²` is a `k`-point of the torus. The proof is the Library proof: `n²` acts trivially
on `T`, so it centralizes `ν(𝔾ₘ)` and lies in the dynamic centralizer of `ν`, which `T`
represents.
