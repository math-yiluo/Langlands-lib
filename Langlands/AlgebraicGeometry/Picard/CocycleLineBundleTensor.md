# Tensor products of line bundles glued from unit cocycles

Module `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleTensor`, namespace
`Langlands.AlgebraicGeometry.Picard.CocycleGluing`.

This module shows that the tensor product of two line bundles glued from unit
cocycles on the same cover is the line bundle glued from the product cocycle.
It uses the gluing construction `glued g` of
`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof` and the project's
tensor product of module sheaves `Langlands.Scheme.Modules.tensorObj` (module
`Langlands.AlgebraicGeometry.Modules.Tensor`), which is the sheafification of
the sectionwise tensor product of presheaves of modules.

Fix a scheme `X`, an index type `ι : Type u`, a family of opens
`T : ι → X.Opens`, and unit families
`g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ`. Their product `g * h` is the pointwise
product, `(g * h) i j = g i j * h i j` (`mul_apply_val`). The main definition
is

```
noncomputable def tensorIso (hg : IsCocycle g) (hh : IsCocycle h) (hT : (⨆ i, T i) = ⊤) :
    tensorObj (glued g) (glued h) ≅ glued (g * h)
```

It is a specific morphism, not one chosen by `Classical.choice`: its forward
map `mulHom g h` multiplies the components of a section of `glued g` with the
components of a section of `glued h`. Over an open `V ≤ T i` it sends the
tensor of the local generators `genSec g hg i hV` and `genSec h hh i hV` to the
local generator `genSec (g * h) _ i hV`, and the inverse sends that generator
back.

## Conventions

The conventions for `glued g` are those of `CocycleLineBundleProof`. A section
of `glued g` over `U` is a family `(b i)` with `b i ∈ Γ(X, U ⊓ T i)` and
`b i = g i j * b j` on every open inside `U ⊓ T i ⊓ T j` (the predicate
`Compat g b`). `comp g m i` is the `i`-th component of a section `m`, and
`mk g b hb` is the section with components `b`. A scalar `r ∈ Γ(X, U)` acts on
each component through its restriction to `U ⊓ T i`. `IsCocycle g` is the
identity `g i j * g j k = g i k` on triple overlaps (restrictions left out
here). `genSec g hg i hV` is the local generator over an open `V ≤ T i`; its
`j`-th component is `g j i` restricted to `V ⊓ T j`.

For the sheaf tensor product, `tensorHomEquiv M N P` (from
`Langlands.AlgebraicGeometry.Modules.Tensor`) identifies morphisms
`tensorObj M N ⟶ P` with morphisms `M.val ⊗ N.val ⟶ P.val` of presheaves of
modules out of the sectionwise tensor product (the sheafification adjunction).
`tensorSheafifyUnit M N : M.val ⊗ N.val ⟶ (tensorObj M N).val` (from
`Langlands.AlgebraicGeometry.Modules.PullbackTensor`) is the unit of this
adjunction. As in that module, the file declares a local instance of the
monoidal structure on `X.PresheafOfModules` coming from
`PresheafOfModulesOfCommRing`; it is local and changes nothing outside the
file.

## Declarations

### Sections of the sheaf tensor product and an isomorphism criterion

These declarations concern arbitrary `M N P : X.Modules`.

- `tmulSec m n : Γ(tensorObj M N, U)`, for `m : Γ(M, U)` and `n : Γ(N, U)`, is
  the image of `m ⊗ₜ n` under `tensorSheafifyUnit M N` over `U`.
- `map_tmulSec`: `tmulSec` commutes with restriction.
- `app_tmulSec φ m n`: for `φ : tensorObj M N ⟶ P`,
  `φ.app U (tmulSec m n)` is the image of `m ⊗ₜ n` under
  `tensorHomEquiv M N P φ` over `U`. The proof rewrites
  `tensorHomEquiv M N P φ = tensorSheafifyUnit M N ≫ φ.val` with the
  adjunction identity `homEquiv_unit`. The same identity is the Library lemma
  `tensorHomEquiv_eq_tensorSheafifyUnit_comp` in
  `Langlands.AlgebraicGeometry.ModuleDualEvaluation`; it is proved again here
  in one line so that this module does not import the dual-module files.
- `isIso_of_bijective_tensorHomEquiv φ T hT hφ`: let `T : κ → X.Opens` be a
  family with `⨆ i, T i = ⊤`. If, for every `i` and every open `V ≤ T i`, the
  sectionwise map `tensorHomEquiv M N P φ` over `V` is bijective, then `φ` is
  an isomorphism. Proof: the sheafification unit is locally surjective; the
  sectionwise map is locally bijective because every point has a
  neighbourhood `U ⊓ T i` on which it is bijective. Since
  `tensorHomEquiv M N P φ = tensorSheafifyUnit M N ≫ φ.val`, the underlying
  map of `φ` is locally injective and locally surjective
  (`Presheaf.isLocallySurjective_of_isLocallySurjective_fac`,
  `Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac`),
  so it is an isomorphism of sheaves (`Sheaf.isLocallyBijective_iff_isIso`),
  and `SheafOfModules.toSheaf` reflects isomorphisms. This is the argument of
  the Library theorem `isIso_dualTensorEval`
  (`Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation`), stated
  here for an arbitrary morphism out of a sheaf tensor product.

### Products of cocycles and of sections

- `mul_apply_val`: `(g * h) i j = g i j * h i j` as sections over
  `T i ⊓ T j`.
- `IsCocycle.mul hg hh : IsCocycle (g * h)`: the product of two unit cocycles
  is a unit cocycle (restriction is a ring map and the rings are commutative).
- `compat_mul g h hb hc`: if `b` satisfies the gluing relation of `g` and `c`
  that of `h`, then the componentwise product `fun i ↦ b i * c i` satisfies
  that of `g * h`.
- `mulSec g h m n : Γ(glued (g * h), U)`, for `m : Γ(glued g, U)` and
  `n : Γ(glued h, U)`, is the section with components
  `comp g m i * comp h n i` (`comp_mulSec`, by `rfl`).
- `mulSec_add_left`, `mulSec_add_right`, `mulSec_smul_left`,
  `mulSec_smul_right`: `mulSec g h` is `Γ(X, U)`-bilinear.
- `map_mulSec`: `mulSec` commutes with restriction.
- `mulSec_genSec g h hg hh i hV`: for `V ≤ T i`,
  `mulSec g h (genSec g hg i hV) (genSec h hh i hV) =
  genSec (g * h) (hg.mul hh) i hV`. Both sides have `j`-th component
  `(g j i)|(V ⊓ T j) * (h j i)|(V ⊓ T j)`.

### The multiplication morphism

These declarations need neither the cocycle identity nor a cover hypothesis.

- `mulBilin g h U`: `mulSec g h` as a `Γ(X, U)`-bilinear map
  (`LinearMap.mk₂`).
- `mulPresheafHom g h : (glued g).val ⊗ (glued h).val ⟶ (glued (g * h)).val`:
  the morphism of presheaves of modules that is `TensorProduct.lift
  (mulBilin g h U)` over each open `U`. Its naturality is `map_mulSec`.
  `mulPresheafHom_app_tmul`: it sends `m ⊗ₜ n` to `mulSec g h m n`.
- `mulHom g h : tensorObj (glued g) (glued h) ⟶ glued (g * h)` is
  `(tensorHomEquiv _ _ _).symm (mulPresheafHom g h)`, the morphism of sheaves
  whose sectionwise tensor adjoint is `mulPresheafHom g h`
  (`tensorHomEquiv_mulHom`).
- `mulHom_app_tmulSec`: `mulHom g h` sends `tmulSec m n` to `mulSec g h m n`.
- `comp_mulHom_app_tmulSec`: the `i`-th component of the image of
  `tmulSec m n` is `comp g m i * comp h n i`.

### The isomorphism

From here on `hg : IsCocycle g` and `hh : IsCocycle h`.

- `bijective_mulPresheafHom_app hg hh i hV`: for `V ≤ T i`, the sectionwise
  map `mulPresheafHom g h` over `V` is bijective. Proof: by
  `smul_genSec_bijective`, `Γ(glued g, V)` and `Γ(glued h, V)` are free of
  rank one over `Γ(X, V)` on `genSec g hg i hV` and `genSec h hh i hV`, so the
  map `c ↦ c • (genSec g hg i hV ⊗ₜ genSec h hh i hV)` from `Γ(X, V)` onto the
  sectionwise tensor product is surjective (induction on tensors). Composed
  with `mulPresheafHom g h` it is `c ↦ c • genSec (g * h) _ i hV`
  (`mulSec_genSec`), which is bijective by `smul_genSec_bijective` for
  `g * h`. A surjection whose composite with a map is bijective is a
  bijection, so both maps are bijective.
- `isIso_mulHom hg hh hT`: if `⨆ i, T i = ⊤`, then `mulHom g h` is an
  isomorphism, by `isIso_of_bijective_tensorHomEquiv` and
  `bijective_mulPresheafHom_app`.
- `tensorIso hg hh hT := asIso (mulHom g h)`, displayed above;
  `tensorIso_hom` (`(tensorIso hg hh hT).hom = mulHom g h`, by `rfl`).
- `tensorIso_hom_app_tmulSec`: the forward map sends `tmulSec m n` to
  `mulSec g h m n`, over every open `U`.
- `tensorIso_hom_app_tmulSec_genSec`: for `V ≤ T i`, the forward map sends
  `tmulSec (genSec g hg i hV) (genSec h hh i hV)` to
  `genSec (g * h) (hg.mul hh) i hV`.
- `tensorIso_inv_app_genSec`: for `V ≤ T i`, the inverse sends
  `genSec (g * h) (hg.mul hh) i hV` to
  `tmulSec (genSec g hg i hV) (genSec h hh i hV)`.

## Related results

The FLT theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2`
(module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2`)
states that the tensor product of invertible modules is invertible, for the
monoidal structure on `X.Modules` used in the FLT library. This module works
instead with the project tensor `Langlands.Scheme.Modules.tensorObj` and with
the explicit sheaves `glued g`, and it identifies the tensor product with a
specified glued sheaf, with formulas on local generators.

The Library module `Langlands.AlgebraicGeometry.Picard.LineBundleTensor`
proves `IsLocallyFreeRankOne.tensor` for `tensorObj` under the published
premise `Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`.
This module does not use that premise: for the sheaves `glued g` and
`glued h` it identifies `tensorObj` directly with `glued (g * h)`, which is
locally free of rank one by `isLocallyFreeRankOne_glued` of
`CocycleLineBundleProof`. (No lemma combining the two is stated here.)

## Sources and provenance

Provenance: derived.

Source 1: Stacks Project, Cohomology of Sheaves, Lemma
`cohomology-lemma-h1-invertible` (tag 09NU), in the registered folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, file `cohomology.tex`,
lines 405-474 (tag map: `tags.txt` line 12227). The lemma states (lines
407-412) that for a ringed space with local stalks "there is a canonical
isomorphism H^1(X, O_X^*) = Pic(X). of abelian groups." Its proof sends an
invertible sheaf `L` to the torsor `L^*` of its local generators, and says
(line 443): "We omit the verification that this is a homomorphism of abelian
groups." The group law on `Pic(X)` is the tensor product. The Library gauge
module `CocycleLineBundleGauge` cites the same lemma.

Source 2: Stacks Project, Chapter 17 Sheaves of Modules, Section 17.25
Invertible modules, Lemma 17.25.5 (tag 01CT), part (1),
in the registered folder
`stacks-local-freeness-invertibility-sections-2026-10-21`, file `01CR.html`:
"If L, N are invertible O_X-modules, then so is L ⊗_{O_X} N."

Correspondence with the sources. Over every open inside `T i`, the sections
of `glued g` are free of rank one on `genSec g hg i _`
(`smul_genSec_bijective`), so these are local generators in the sense of
09NU, and on the overlaps `T i ⊓ T j` they differ by the units `g`. Thus
`glued g` is the line bundle whose torsor of local generators is described by
the Čech cocycle `g` on the cover `T`. The
isomorphism `tensorIso` says that the tensor product of the line bundles with
cocycles `g` and `h` is the line bundle with cocycle `g * h`, and its
generator formulas say that the tensor of the local generators is a local
generator of the tensor product. This is the cocycle form of the omitted
verification in 09NU that sending a line bundle to its class is compatible with
the group laws, for line bundles trivialized on a common cover; it also gives,
for these line bundles, the explicit form of Lemma 17.25.5 (1). The module
proves only the sheaf-level isomorphism and its formulas; it says nothing about
cohomology classes, about refinement of covers, or about the group `Pic(X)`.

The Lean proof is this module's own construction; the sources give no proof
of these statements. The morphism multiplies components, and it is shown to
be an isomorphism by the local criterion `isIso_of_bijective_tensorHomEquiv`
together with the rank-one freeness of the sections over the opens `T i`.

Differences from the sources. 09NU works with arbitrary invertible modules on
a ringed space with local stalks, and 01CT with arbitrary invertible modules
on a ringed space. This module works on a scheme, with the two line bundles
given by unit cocycles on the same family of opens `T`, and with the project
tensor product `tensorObj`. The morphism `mulHom` exists for every family `T`
and all unit families `g`, `h`; the cocycle identities and the cover
hypothesis `⨆ i, T i = ⊤` are used only for the isomorphism.
