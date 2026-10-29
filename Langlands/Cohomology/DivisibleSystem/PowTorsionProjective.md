# Relative projectivity of direct sums and compact inductions

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem`
(`DivisibleSystem`, `DivisibleSystem.obj`, `DivisibleSystem.map`, `powSMul`,
`comp_powSMul`, `powSMul_comp_powSMul`, `map_powSMul`,
`SmoothRepComplexDivisibleSystem`), on
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`PowTorsionProjective`,
`powTorsionProjective_of_projective`, `homComplexSystem_map_f_surjective`,
`homComplexLimit_π_f_surjective`, `isMittagLeffler_smoothHomComplexSystem_eval`),
on `Langlands.Cohomology.DivisibleSystem.HomSystem` (`smoothHomComplexSystem`),
on `Langlands.Cohomology.DivisibleSystem.AdjunctionHomSystem`
(`compactInductionSystem`), on
`Langlands.Cohomology.DivisibleSystem.BiproductHomSystem`
(`DivisibleSystem.biproduct`) and on
`Langlands.Cohomology.SupercuspidalExt.Reciprocity` and
`Langlands.Representation.Induction.OpenAdjunction` (`compactInduction`,
`restriction`, the instances `restriction_additive` and
`restriction_preservesEpimorphisms`, and
`SupercuspidalExt.compactInductionAdjunction`, the adjunction
`c-Ind_H^G ⊣ restriction` for an open subgroup `H`). From Mathlib it uses the
biproduct API (`biproduct.desc`, `biproduct.ι_desc_assoc`, `biproduct.hom_ext'`,
`Functor.mapBiproduct`, `Abelian.hasFiniteBiproducts`), cokernels
(`cokernel.desc`, `cokernel.π_desc_assoc`, `cokernel.condition`, `cancel_epi`)
and adjunctions (`Adjunction.homEquiv`,
`Adjunction.homEquiv_naturality_right_symm`, `Functor.map_epi`).

`PowTorsionProjective ℓ m P` (published in HomSurjective) means: for every
epimorphism `p : X ⟶ Y` such that multiplication by `ℓ ^ m` on `X`
(`powSMul ℓ m X`) is zero, every morphism `P ⟶ Y` lifts along `p`. Below it is
read as "`P` is projective relative to objects killed by `ℓ ^ m`".

## Closure properties (namespace `Langlands.Cohomology.DivisibleSystem`)

`C` and `D` are preadditive categories.

- `powTorsionProjective_of_iso e hP` and `powTorsionProjective_iff_of_iso e`:
  invariance under an isomorphism `e : P ≅ Q`. A lift `f` of `e.hom ≫ g` gives
  the lift `e.inv ≫ f` of `g`.
- `powTorsionProjective_of_le h hP`: for `m' ≤ m`, projectivity relative to
  objects killed by `ℓ ^ m` implies projectivity relative to objects killed by
  `ℓ ^ m'`. An object killed by `ℓ ^ m'` is killed by `ℓ ^ m`: writing
  `m = m' + k`, `powSMul ℓ m X = powSMul ℓ m' X ≫ powSMul ℓ k X`
  (`powSMul_comp_powSMul`).
- `powTorsionProjective_biproduct X hX`: for any family `X : ι → C` with a
  biproduct `⨁ X` (no finiteness assumption on `ι`), if every `X i` is
  projective relative to objects killed by `ℓ ^ m`, so is `⨁ X`. The lifts
  `f i` of the restrictions `biproduct.ι X i ≫ g` are assembled into
  `biproduct.desc f`, and `biproduct.desc f ≫ p = g` is checked on the
  summands (`biproduct.hom_ext'`).
- `powTorsionProjective_obj_of_adjunction adj hP`: for an adjunction
  `adj : F ⊣ G` between `C` and `D` with `G` additive and preserving
  epimorphisms, if `P` is projective relative to objects killed by `ℓ ^ m`, so
  is `F.obj P`. Given `p : X ⟶ Y` in `D` as above and `g : F.obj P ⟶ Y`,
  `G.map p` is an epimorphism and `G.obj X` is killed by `ℓ ^ m`, because
  `G.map (powSMul ℓ m X) = powSMul ℓ m (G.obj X)` (`map_powSMul`). A lift `f`
  of the adjoint morphism `adj.homEquiv _ _ g : P ⟶ G.obj Y` along `G.map p`
  gives the lift `(adj.homEquiv _ _).symm f` of `g` along `p`
  (`homEquiv_naturality_right_symm`).
- `powSMul_cokernel_powSMul P`: the cokernel `P/ℓ^m P` of `powSMul ℓ m P` is
  killed by `ℓ ^ m` (checked after composing with the epimorphism
  `cokernel.π`, using `comp_powSMul` and `cokernel.condition`).
- `powTorsionProjective_cokernel_powSMul hP`: if `P` is projective relative to
  objects killed by `ℓ ^ m`, so is `P/ℓ^m P`. A lift `f : P ⟶ X` of
  `cokernel.π ≫ g` satisfies `powSMul ℓ m P ≫ f = f ≫ powSMul ℓ m X = 0`
  because `X` is killed by `ℓ ^ m`, so it factors as `cokernel.desc _ f _`,
  which lifts `g` (checked after composing with `cokernel.π`). With the
  published `powTorsionProjective_of_projective`, this applies to every
  projective object `P`.

## Termwise relative projectivity of `ℓ`-divisible systems of complexes

`C` and `D` are abelian categories, and `T` is an `ℓ`-divisible system of
`ℤ`-graded cochain complexes in `C` (the published
`DivisibleSystem (CochainComplex C ℤ) ℓ`, Harris 1999, (2.1)), with level-`m`
complexes `T.obj m`.

- `TermwisePowTorsionProjective T : Prop` (the entry declaration): for every
  level `m` and degree `p`, the term `(T.obj m).X p` is projective relative to
  objects killed by `ℓ ^ m`. This is exactly the hypothesis
  `∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)` of the published lemmas
  `homComplexSystem_map_f_surjective`, `isMittagLeffler_homComplexSystem_eval`
  and `homComplexLimit_π_f_surjective` of HomSurjective.
- `termwisePowTorsionProjective_biproduct T hT`: for a finite family
  (`ι : Type`, `[Finite ι]`) of such systems with the property, the direct sum
  `DivisibleSystem.biproduct T` of BiproductHomSystem has it. Its degree-`p`
  term at level `m` is `(⨁ᵢ T i m).X p`, which is isomorphic to
  `⨁ᵢ (T i m).X p` because evaluation in degree `p` is additive and preserves
  finite biproducts (`Functor.mapBiproduct`); the previous closure lemmas
  conclude.
- `termwisePowTorsionProjective_map_of_adjunction T adj hT`: for an adjunction
  `adj : F ⊣ G` with `F` additive, preserving finite limits and finite colimits
  (so that the published `T.map` applies to `F.mapHomologicalComplex`), and `G`
  additive and preserving epimorphisms, the system
  `T.map (F.mapHomologicalComplex (ComplexShape.up ℤ))`, whose terms are
  `F.obj ((T.obj m).X p)`, has the property if `T` has it
  (`powTorsionProjective_obj_of_adjunction`).

## Compact induction (namespace `Langlands.Cohomology`)

`R : Type u` is a commutative ring, `G : Type u` a topological group, and all
smooth representations are in `SmoothRep.{u, u, u}`, the one-universe setting
of the published `compactInduction`, `restriction` and
`compactInductionSystem`.

- `powTorsionProjective_compactInduction R hH hP`: for an open subgroup `H`,
  compact induction `c-Ind_H^G` sends a smooth representation of `H` that is
  projective relative to objects killed by `ℓ ^ m` (in the category of smooth
  representations of `H`) to a smooth representation of `G` with the same
  property (in the category of smooth representations of `G`). This is
  `powTorsionProjective_obj_of_adjunction` for the published adjunction
  `c-Ind_H^G ⊣ restriction`; restriction is additive and preserves
  epimorphisms by published instances.
- `termwisePowTorsionProjective_compactInductionSystem R hH T hT`: the same
  for the published system `compactInductionSystem R hH T`
  (`m ↦ c-Ind_H^G (T m)`), whose terms are `c-Ind_H^G ((T.obj m).X p)`.

For a finite family (`ι : Type`, `[Finite ι]`) of subgroups `H i` with
`hH : ∀ i, IsOpen (H i : Set G)`, `ℓ`-divisible systems `T i` of cochain
complexes of smooth representations of `H i` with
`hT : ∀ i, TermwisePowTorsionProjective (T i)`, and an `ℓ`-divisible system
`W` of cochain complexes of smooth representations of `G`, let `S` be the
direct sum `DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)`
(`m ↦ ⨁ᵢ c-Ind_{H i}^G (T i m)`).

- `termwisePowTorsionProjective_biproduct_compactInductionSystem R hH T hT`:
  `TermwisePowTorsionProjective S`, by the two previous results.
- `smoothHomComplexSystem_biproduct_compactInduction_map_f_surjective`: for
  every morphism `φ : m ⟶ m'` of `ℕᵒᵖ` and every degree `n`, the degree-`n`
  component of the map `(smoothHomComplexSystem R G S W).map φ` of the inverse
  system of Hom complexes `m ↦ Hom^•_G(S m, W m)` is surjective.
- `isMittagLeffler_smoothHomComplexSystem_biproduct_compactInduction_eval`: in
  every degree `n`, the inverse system of degree-`n` terms of
  `smoothHomComplexSystem R G S W` (as types) satisfies the Mittag-Leffler
  condition.
- `smoothHomComplexLimit_biproduct_compactInduction_π_f_surjective`: for every
  level `m` and degree `n`, the degree-`n` component of the limit projection
  `limit (smoothHomComplexSystem R G S W) ⟶ Hom^•_G(S m, W m)` is surjective.

Each of the last three results is the published HomSurjective lemma for `S`
and `W` (`homComplexSystem_map_f_surjective`,
`isMittagLeffler_smoothHomComplexSystem_eval`,
`homComplexLimit_π_f_surjective`), applied to the first one.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999).

Proof of Proposition 4.4, printed p.310 (one-based PDF page 12), (4.4.4):
`Z^{i,j} = ⊕_{dim(e)=n−1−i} C^j(ẽ) = ⊕_{(e,δ) ∈ O_i} c-Ind_{S(ẽ)}^{GJ} C^j(ẽ)`
"is a sum of compactly induced modules".

Proof of Proposition 4.10, printed p.311 (one-based PDF page 13): the
complexes used for the spectral sequences (4.9) are "of the form
`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`", which Harris rewrites as (4.10.2).

Printed p.312 (one-based PDF page 14), read in the rendered scanned page:
"Write `T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.
To check the Mittag-Leffler condition, we first need to study the maps
(4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)` as m varies. But we have seen in §2 that
the maps `C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p}` are surjective. Since
`C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective
for all m. Since the right-hand side of the spectral sequence (4.9) is a
finite group for all m, the complexes in (4.10.2) satisfy a Mittag-Leffler
condition."

The published module HomSurjective takes the freeness of the source used in
this argument as the explicit hypothesis `PowTorsionProjective` on the terms
of the source system. Harris checks the surjectivity after rewriting the
complexes into the form (4.10.2), that is, on Hom modules out of the inducing
modules over `S(ẽ)`. This module checks it on the complexes before the
rewriting: the hypothesis on the inducing systems `T i` over the open
subgroups `H i` (in Harris's notation `S(ẽ)`) passes to the direct sum of
their compact inductions, the source of the complexes of p.311, for a single
degree `-i`. The published isomorphisms of BiproductHomSystem
(`smoothHomComplexSystemBiproductReciprocityIso`) identify these Hom-complex
systems with the direct sums of the systems
`m ↦ Hom^•_{H i}(T i m, W m|_{H i})`, to which the published HomSurjective
lemmas apply directly with the same hypothesis on `T i`; this module does not
use these isomorphisms.

The cokernel lemmas give a source of objects with the hypothesis. For a free
`𝒪[Γ]`-module `P`, which is projective in the category of `𝒪[Γ]`-modules,
`P/ℓ^m P` is a free `𝒪/ℓ^m𝒪[Γ]`-module of the same rank, the kind of module
Harris names. This identification is not formalized.

The closure lemmas, the predicate `TermwisePowTorsionProjective`, the
corollaries for direct sums of compact inductions and all proofs are ours;
the cited passages contain only the decomposition (4.4.4), the form of the
complexes and the surjectivity of (4.10.3) justified by freeness.

## Scope

The module does not prove that Harris's modules `C^j_m(ẽ)` or
`C^j_m(ẽ)^{H_p}` satisfy `PowTorsionProjective`, and it does not treat the
passage from `C^j_m(ẽ)` to its `H_p`-invariants or from `K_p/H_p` to
`C_p/H_p` in the coefficients. It does not show that a free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-module, viewed as a smooth representation of `S(ẽ)`, is
projective relative to objects killed by `ℓ ^ m` in the category of smooth
representations of `S(ẽ)`; for `𝒪/ℓ^m𝒪[S(ẽ)/H_p] = c-Ind_{H_p}^{S(ẽ)} 𝒪/ℓ^m`
this would require the trivial representation `𝒪/ℓ^m` of `H_p` to have the
property. The index type of the direct sums of `ℓ`-divisible systems is
finite; the finiteness of Harris's `O_{-i}` is not proved. The module proves
nothing about the cohomology of the Hom complexes or their limits, the total
complex over `i + j = k`, the finiteness of the right-hand side of (4.9), or
the spectral sequences.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
