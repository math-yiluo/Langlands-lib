# Geometric reductivity of `GL_n` and the radicals of its block parabolics: statement

Author: Worker 3483.

This module states, as one `Prop`-valued definition, two geometric structure
assertions about the matrix-coordinate group `GL_n` of the Library. Nothing is
proved here. The declaration `GeometricStructureStatement` is in the namespace
`Langlands.GroupScheme.GeneralLinear`.

## The objects used

Throughout, `k` is a field, `n` is a finite type with decidable equality, and
`GL_n = groupScheme n (CommRingCat.of k)`.

- `groupScheme n R` (module `Langlands.GroupScheme.GeneralLinear`) is
  the matrix-coordinate general linear group scheme over `Spec R`. Its points
  over a test scheme `T` are the invertible `n × n` matrices over `Γ(T, ⊤)`
  (`pointsEquiv`).
- `IsGeometricallyReductive G` (module
  `Langlands.GroupScheme.Reductive.GeometricReductivityShift`) is Haboush's
  geometric reductivity for a group scheme `G` over a field `k`. For every
  finite type `m` with decidable equality, every matrix representation `ρ` of
  `G` on `k^m` and every nonzero vector `v` fixed by `ρ`, there are `d > 0` and a
  homogeneous polynomial `F` of degree `d` in the coordinates of `k^m` such that
  `F(ρ(g) x) = F(x)` for every point `g` of `G` and every vector `x` over every
  test scheme, and `F(v) ≠ 0`.
- For a weight function `e : n → ℤ`, the block parabolic, block Levi and block
  unipotent subgroup schemes `blockParabolicScheme n R e`,
  `blockLeviScheme n R e` and `blockUnipotentScheme n R e` (module
  `Langlands.GroupScheme.CorepresentedClosedSubgroup`) are the closed subgroup
  schemes of `GL_n` whose points are the invertible matrices `g` with
  `g i j = 0` whenever `e i < e j`; with `g i j = 0` whenever `e i ≠ e j`; and
  with `g i j` equal to the `(i, j)` entry of the identity matrix whenever
  `e i ≤ e j`, respectively (`mem_blockParabolic`, `mem_blockLevi`,
  `mem_blockUnipotent` in `Langlands.GroupScheme.Dynamic.GeneralLinear`).
  They represent the dynamic subgroups `P(λ)`, `Z(λ)` and `U(λ)` of the
  diagonal cocharacter `λ(t) = diag(t^{e i})`
  (`isRepresentedBy_parabolic_diagonalCocharacter`,
  `isRepresentedBy_centralizer_diagonalCocharacter`,
  `isRepresentedBy_unipotent_diagonalCocharacter`, module
  `Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability`).
- `blockLimitHom n R e : blockParabolicScheme n R e ⟶ blockLeviScheme n R e`
  and `blockUnipotentIsoKernel n R e : blockUnipotentScheme n R e ≅
  kernel (blockLimitHom n R e)` (module
  `Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition`) are the block
  diagonal limit homomorphism and the identification of the block unipotent
  scheme with its kernel. The composite
  `(blockUnipotentIsoKernel n R e).hom ≫ kernelι (blockLimitHom n R e)` is a
  homomorphism `blockUnipotentScheme n R e ⟶ blockParabolicScheme n R e`.
  Followed by the inclusion of the block parabolic into `GL_n`, it is the
  inclusion `blockUnipotentHom n R e` of the block unipotent scheme
  (`blockUnipotentIsoKernel_hom_comp`).
- `IsGeometricUnipotentRadical r` for `r : U ⟶ P` (module
  `Langlands.GroupScheme.Rational.SemistandardIntersection`) says: `r` is a
  closed subgroup; `U` is smooth, connected and unipotent; the range of `r` is
  normal in `P`; and after base change to an algebraic closure `k̄` of `k`, `U`
  is still connected and unipotent, the range of `r` is still normal, and it
  contains every smooth connected unipotent normal closed subgroup of `P_k̄`.

## The statement

`GeometricStructureStatement : Prop` is the conjunction of:

1. for every field `k : Type u` with `[IsAlgClosed k]` and every finite type
   `n : Type` with decidable equality,
   `IsGeometricallyReductive (groupScheme n (CommRingCat.of k))`;
2. for every field `k : Type u`, every finite type `n : Type` with decidable
   equality and every `e : n → ℤ`,
   `IsGeometricUnipotentRadical
   ((blockUnipotentIsoKernel n (CommRingCat.of k) e).hom ≫
   kernelι (blockLimitHom n (CommRingCat.of k) e))`.

Part 1 says that `GL_n` over an algebraically closed field is geometrically
reductive. Part 2 says that, over every field, the block unipotent subgroup
`U(λ)` is the geometric unipotent radical of the block parabolic subgroup
`P(λ)`, for the diagonal cocharacter `λ` of every weight function. There is no
assumption on the characteristic, and `e` may be constant (then `P(λ) = GL_n`
and `U(λ)` is trivial) or have repeated values.

## Sources

- Mumford, Fogarty and Kirwan, *Geometric invariant theory*, 3rd edition
  (1994), source ID `mumford-fogarty-kirwan-1994-git-3rd`. PDF page = printed
  page + 12.
  - Appendix to Chapter 1, §A, definition (iii) (printed p.191, PDF p.203):
    `G` is "geometrically reductive if, whenever `G → GL(V)` is a rational
    representation and `0 ≠ v ∈ V^G`, then for some `r > 0`, there is an
    `F ∈ (Symm^r V*)^G` with `F(v) ≠ 0`." The same page lists
    "Formanek and Procesi [105] for `G = GL(n)`, any char., or over `Z`"
    among the proofs that reductive groups are geometrically reductive.
  - Theorem A.1.0 (printed p.192, PDF p.204): for an affine algebraic group `G`
    over any field `k`, "a) `G` is reductive" and "b) `G` is geometrically
    reductive" are equivalent (Haboush for a) ⇒ b)).
- Conrad, *Reductive group schemes* (2014), source ID
  `conrad-2014-reductive-group-schemes`. Printed page = PDF page.
  - Theorem 4.1.7 (pp.112–113): for a finitely presented affine group `G`
    over a ring with a `𝔾ₘ`-action, (1) the subfunctors `P_G(λ)`, `U_G(λ)` and
    `Z_G(λ)` are represented by closed subgroups, with `U_G(λ)` normalized by
    `Z_G(λ)`; (2) the fibres of `U_G(λ)` are connected; (3)
    `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an isomorphism; (4) if `G` is smooth, the
    three subgroups are smooth and the fibres of `U_G(λ)` are unipotent. The
    proof (p.113) identifies `U_G(λ)` with the fibre over `1` of the limit
    morphism.
  - Example 4.1.8 (p.114): for `SL_n` and `λ(t) = diag(t^{e₁}, …, t^{eₙ})`
    with `e₁ > ⋯ > eₙ`, `P_G(λ)` is the upper triangular subgroup and `U_G(λ)`
    the strictly upper triangular one.
  - Example 4.1.9 (p.114): for a connected reductive group `G` over an
    algebraically closed field, `P_G(λ) = Z_G(λ) ⋉ U_G(λ)` with `U_G(λ)` a
    smooth connected unipotent normal subgroup; "Thus, `U_G(λ)` is the
    unipotent radical of `P_G(λ)` and `Z_G(λ)` is a Levi subgroup of
    `P_G(λ)`."

## Correspondence with the sources

**Provenance.** Part 1 is Theorem A.1.0, a) ⇒ b), of Mumford–Fogarty–Kirwan for
the reductive group `GL_n` over an algebraically closed field, with definition
(iii) in the coordinate form of `IsGeometricallyReductive`: `V = k^m`, the
invariant `F` is a homogeneous polynomial of positive degree `d = r`, and
invariance is required on points over every test scheme. Part 2 is Conrad's
Example 4.1.9 for `G = GL_n` and the diagonal cocharacter of weights `e`,
read through `IsGeometricUnipotentRadical`: over a field `k` that is not
algebraically closed, the condition "unipotent radical" is imposed on the base
change to `k̄`, together with smoothness, connectedness, unipotence and
normality over `k`. Example 4.1.8 is the triangular case for `SL_n`. The
combination of the two parts into one declaration, and their exact Lean
formulation, are the program's own; the statement is the Milestone 1(a)
requirement of the program contract ("Prove geometric reductivity and identify
its standard parabolics, block Levi groups and unipotent radicals with the
dynamic `P(λ)`, `Z(λ)`, `U(λ)` of explicit diagonal cocharacters").

**Why the statement is true.** `GL_n` is connected reductive over every field
(`GeneralLinear.reductiveStatement`). Over an algebraically closed field a
connected reductive group is pseudo-reductive, and Haboush's theorem gives
part 1. For part 2, the block parabolic and the block unipotent subgroups are
`P(λ)` and `U(λ)` for `λ(t) = diag(t^{e i})`, and for a connected reductive
group over any field `U(λ)` is the geometric unipotent radical of `P(λ)`: it is
smooth, connected and unipotent by Theorem 4.1.7(2) and (4), normal in
`P(λ) = Z(λ) ⋉ U(λ)` by Theorem 4.1.7(1) and (3), its formation commutes with
base change to `k̄` (Conrad, p.114, after Example 4.1.9), and over `k̄` it is
the unipotent radical by Example 4.1.9.

## Relation to the Library

These remarks describe available tools; they are not part of the statement.

- The published index note `notes/group-schemes/ledger-milestones-interfaces.md`
  records both assertions as rows of status I (instances of published theorems
  with binders) and lists, as its remaining limitation 5, that no proposition
  declaration states them. This declaration states them.
- Part 1 follows from `reductiveGeometricReductivity :
  ReductiveGeometricReductivityStatement` (module
  `Langlands.GroupScheme.Reductive.GeometricReductivityProof`) through
  `isGeometricallyReductive_of_statement` (module
  `Langlands.GroupScheme.Reductive.GeometricReductivityShift`) and the
  pseudo-reductivity of `GL_n` from `GeneralLinear.reductiveStatement` (module
  `Langlands.GroupScheme.Reductive.GeneralLinearProof`).
- Part 2 follows from `dynamicGeometricUnipotentRadical :
  DynamicGeometricUnipotentRadicalStatement` (module
  `Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof`) applied to
  `GeneralLinear.reductiveStatement`, the representability theorems listed
  above and `blockUnipotentIsoKernel_hom_comp`.

## Lean conventions

- The block unipotent scheme is mapped into the block parabolic through the
  kernel of `blockLimitHom`; this is the published map that
  `blockUnipotentIsoKernel_hom_comp` relates to the inclusions into `GL_n`.
- `n : Type` lives in universe `0`, as in `groupScheme`; the field `k` lives in
  an arbitrary universe `u`.
