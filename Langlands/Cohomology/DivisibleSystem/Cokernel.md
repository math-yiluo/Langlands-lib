# Cokernels of ℓ-divisible systems

Author: Worker 61. Built on the published module
`Langlands.Cohomology.DivisibleSystem` (ℓ-divisible systems, Harris 1999,
(2.1)) and on Mathlib's short complexes, refinements in abelian categories
(`Mathlib.CategoryTheory.Abelian.Refinements`) and snake lemma
(`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`). All names below are in
the namespace `Langlands.Cohomology.DivisibleSystem`. `C` is an abelian
category and `ℓ : ℕ`. Write `T m` for `T.obj m`, `i` for `inclusion` and `j`
for the transition map `T m ⟶ T (m - m')`.

Harris (1999, section 2, printed p.304) writes: "Let b_m : T_m → F(T_m)
denote the canonical embedding. It follows from Facts 3 and 4 and the snake
lemma that {coker b_m} is again an ℓ-divisible system". This module proves
the general fact behind that sentence. For a morphism `b : T ⟶ T'` of
`ℓ`-divisible systems whose components are monomorphisms, the cokernels of
the `b_m` form an `ℓ`-divisible system. Exactness of a functor plays no role.
It is not applied here to Harris's Godement functor `F`.

## Building a system without the torsion condition

- `flat_of_eq T h`: for `h : a + b = n`, the short complex
  `T n ⟶ T n ⟶ T n` given by `ℓ ^ a` and `ℓ ^ b` is exact. This is the field
  `flat` with the index given by an equation.
- `torsion_exact_of_flat`: the condition `torsion_exact` follows from the
  other fields. Its hypotheses are a tower with maps `inclusion`, together
  with the conditions `powSMul_eq_zero`, `inclusion_comp`, `shortExact` and
  `flat` of `DivisibleSystem`. Let `m' < m` and let `x` in `T m` be killed by
  `ℓ ^ m'`. Flatness for the pair `(m - m', m')` writes `x = ℓ ^ (m - m') y`.
  Then `j x = ℓ ^ (m - m') (j y) = 0`, because `ℓ ^ (m - m')` kills
  `T (m - m')`. By exactness of the row (2.1), `x` lies in the image of `i`.
  The proof is a chase with refinements
  (`ShortComplex.exact_iff_exact_up_to_refinements`).
- `ofFlat`: the `ℓ`-divisible system with these data. Its field
  `torsion_exact` is `torsion_exact_of_flat`. `ofFlat_tower` and
  `ofFlat_inclusion` say that its tower and maps `i` are the given ones.

## The cokernel construction

Let `b : T ⟶ T'` be a morphism of `ℓ`-divisible systems.

- `cokernelTower b : ℕᵒᵖ ⥤ C` has object `cokernel (b.tower.app m)` at `m`.
  Its maps are induced by the maps of `T` and `T'` (`cokernel.map`), and
  `cokernelπ_map` states that they commute with the projections.
- `cokernelπ b m : T'.tower.obj m ⟶ (cokernelTower b).obj m` is the projection
  `cokernel.π`. It is an epimorphism (instance), `comp_cokernelπ` says
  `b_m ≫ cokernelπ b m = 0`, and `cokernelπIsCokernel` says that it is a
  cokernel of `b_m`.
- `cokernelDesc b g hg` is the map out of `coker b_m` induced by
  `g : T' m ⟶ X` with `b_m ≫ g = 0`. `cokernelπ_desc` says that it extends `g`.
- `cokernelInclusion b h : coker b_{m'} ⟶ coker b_m`, for `h : m' < m`, is
  induced by the maps `i` of `T` and `T'`. `cokernelπ_inclusion` states that
  it commutes with the projections.
- `cokernel_powSMul_eq_zero`: `ℓ ^ m` kills `coker b_m`, because it kills
  `T' m` and `cokernelπ` is an epimorphism.
- `cokernelInclusion_comp`: the induced `i` followed by the induced `j` is
  zero.

From here on every component `b.tower.app (op m)` is a monomorphism. This is
the instance argument `hb : ∀ m : ℕ, Mono (b.tower.app (op m))`.

- `cokernelSnakeInput b h`, for `h : m' < m`, is a snake input
  (`ShortComplex.SnakeInput`). Its rows are the sequences (2.1) of `T`, of
  `T'` and of the cokernels. The vertical maps are the components of `b`
  and the projections `cokernelπ`. The top row is the zero complex
  `0 ⟶ 0 ⟶ 0`, which is the kernel of the components of `b` because they are
  monomorphisms.
- `cokernel_shortExact`: the induced row
  `coker b_{m'} ⟶ coker b_m ⟶ coker b_{m-m'}` is short exact. The snake lemma
  gives exactness of this row (`L₃_exact`) and that its second map is an
  epimorphism (`epi_L₃_g`). The connecting morphism starts at the zero object,
  so it is zero. Exactness at the next spot of the snake sequence
  (`L₂'_exact`) then makes the first map a monomorphism.
- `cokernel_flat a c`: on `coker b_{a+c}`, the kernel of `ℓ ^ c` is the image
  of `ℓ ^ a`. Write `n = a + c`. Let `z` be killed by `ℓ ^ c` and lift it to
  `y` in `T' n`. Then `ℓ ^ c y = b x` for some `x` in `T n`, and
  `b (ℓ ^ a x) = ℓ ^ (a + c) y = 0`. Since `b_n` is a monomorphism,
  `ℓ ^ a x = 0`, so flatness of `T` for the pair `(c, a)` writes
  `x = ℓ ^ c x₀`. The element `y - b x₀` is killed by `ℓ ^ c`, so flatness of
  `T'` for the pair `(a, c)` writes `y - b x₀ = ℓ ^ a w`. Hence `z` is
  `ℓ ^ a` times the image of `w`. The proof carries out this chase with
  refinements.
- `cokernelSystem b`: the `ℓ`-divisible system `{coker b_m}`, built by
  `ofFlat` from the results above. `cokernelSystem_tower` and
  `cokernelSystem_inclusion` identify its tower and maps `i`.
- `toCokernelSystem b : T' ⟶ cokernelSystem b` is the morphism whose
  components are the projections (`toCokernelSystem_tower_app`). Its
  components are epimorphisms (instance), and
  `comp_toCokernelSystem_tower_app` says that `b_m` followed by them is zero.
- `shortExact_app b m`: each sequence `0 ⟶ T m ⟶ T' m ⟶ coker b_m ⟶ 0` is
  short exact.
- `cokernelSystemDesc b g hg`: a morphism `g : T' ⟶ T''` of `ℓ`-divisible
  systems with `b_m ≫ g_m = 0` for all `m` factors through the cokernel
  system. `toCokernelSystem_desc` gives the factorization, and
  `cokernelSystem_hom_ext` says that morphisms out of the cokernel system are
  determined by their composites with `toCokernelSystem b`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.304. Worker 61 read
the page in the scanned original.

Harris applies the fact to `T' = {F(T_m)}`. That is an `ℓ`-divisible system by
his Fact 4, and `b` is a morphism of systems by functoriality of the
embeddings. He cites Facts 3 and 4. In the general statement proved here,
only two inputs enter: `T'` is an `ℓ`-divisible system and the `b_m` are
monomorphisms. Given these, his claim is the instance of `cokernelSystem`
with these `T` and `T'`. This module does not construct `F`, the embeddings
`b_m`, or Harris's resolutions (Lemma 2.2, obtained "by induction" from this
fact).

Harris names only the snake lemma, which gives the rows (2.1). He does not
spell out freeness of `coker b_m` over `ℤ/ℓ^m` or the torsion condition. The
Lean proves both. Freeness is rendered by the field `flat`, as in the parent
module (its Markdown, item 4), and `cokernel_flat` proves it by the chase
above. For modules over `ℤ/ℓ^m` with `ℓ` prime, this matches a standard fact,
not formalized here. The ring `ℤ/ℓ^m` is self-injective and Noetherian, so a
free submodule of a free module is a direct summand. The quotient is then
projective over a local ring, hence free. The torsion condition comes from `torsion_exact_of_flat`. That
lemma and `ofFlat` are internal tools: they show that the field
`torsion_exact` of `DivisibleSystem` follows from the others. The projection
`toCokernelSystem`, `shortExact_app` and the factorization
`cokernelSystemDesc` are derived. Harris uses them implicitly when he
iterates the construction.

## Scope

The module does not apply the construction to a Godement functor, does not
prove Harris's Facts 3 and 4, and does not build Harris's resolutions
(Lemmas 2.2 and 2.2 bis).

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
