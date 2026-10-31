# Acyclicity of the terms of the sheafified Čech complex

Author: Worker 958.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. For `π : X ⟶ Spec R` separated, an
ordered affine cover `𝒰 : X.OrderedAffineCover` and a quasi-coherent `𝒪_X`-module `M`, it
proves that every term `cechTerm 𝒰 M p` of the sheafified alternating Čech complex of
`Langlands.AlgebraicGeometry.Modules.CechResolution.Complex` has vanishing higher `R`-module
cohomology:

```lean
theorem isZero_relativeCohomology_cechTerm (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] (p n : ℕ) :
    IsZero ((DerivedSections.relativeCohomology π (n + 1)).obj (cechTerm 𝒰 M p))
```

Here `π` is an explicit argument with an `[IsSeparated π]` instance, and
`DerivedSections.relativeCohomology π n` is the Library's `n`-th right derived functor of
`R`-module global sections `DerivedSections.relativeGlobalSections π`. This is the
acyclicity input for computing `R`-module cohomology by the Čech resolution of
`CechResolution.Exact`.

## Declarations

- `rightDerived_additive F n` (an instance): for an additive functor `F : C ⥤ D` between
  abelian categories, `C` with injective resolutions, the right derived functor
  `F.rightDerived n` is additive. Proof: the sum of the chosen lifts
  `InjectiveResolution.desc f` and `InjectiveResolution.desc g` lifts `f + g`, so
  `Functor.rightDerived_map_eq` computes `(F.rightDerived n).map (f + g)` through it, and
  homology is additive.
- `isZero_obj_biproduct G f h`: an additive functor `G` that is zero on every summand `f j`
  of a finite biproduct `⨁ f` is zero on `⨁ f`. Proof: `𝟙 (⨁ f)` is the sum of the
  projection-inclusion composites (`IsBilimit.total`), and `G` maps each of them through a
  zero object.
- `isAffineOpen_inf π hU hV`: if `π : X ⟶ Spec R` is separated, the intersection `U ⊓ V` of
  two affine opens of `X` is affine. Proof: the diagonal of `π` is a closed immersion, hence
  affine, and Mathlib's `isAffineHom_diagonal_iff` applied over the affine open `⊤` of
  `Spec R` gives the claim.
- `isAffineOpen_inter π 𝒰 s`: every finite intersection `𝒰.inter s = ⨅ j, 𝒰.U (s j)` is
  affine, by induction over the nonempty finite infimum (`InfClosed.iInf_mem_of_nonempty`)
  using `isAffineOpen_inf` and `𝒰.isAffineOpen`.
- `isZero_relativeCohomology_sheafOn π M hW n`: for an affine open `W` of `X` and a
  quasi-coherent `M`, `(relativeCohomology π (n + 1)).obj (sheafOn M W)` is zero, where
  `sheafOn M W` is the pushforward along `W.ι : W ⟶ X` of the restriction `M|_W`
  (`CechResolution.Basic`). Proof: `W.ι` is an affine morphism (Mathlib's `IsAffineHom.of_comp`:
  `W.ι ≫ π` is a morphism of affine schemes and `π` is separated), so the Library's
  `affineQuasicoherentHigherDirectImageVanishing` gives `Rᵠ⁺¹ (W.ι)_* (M|_W) = 0`, and
  `pushforwardInjectiveAcyclic` gives that pushforwards along `W.ι` of injective modules are
  acyclic for `relativeGlobalSections π`. Hence the Library's
  `DerivedSections.isIso_pushforwardComparison` identifies
  `Hⁿ⁺¹_R(X, (W.ι)_* (M|_W))` with `Hⁿ⁺¹_R(W, M|_W)` for the structure map `W.ι ≫ π`, and the
  latter vanishes by `affineQuasicoherentCohomologyVanishing` because `W` is affine and
  `M|_W` is quasi-coherent.
- `isZero_relativeCohomology_cechTerm π 𝒰 M p n`: `cechTerm 𝒰 M p` is the finite biproduct
  of the modules `sheafOn M (𝒰.inter s)` over `s : 𝒰.Idx p`; the claim follows from
  `isZero_obj_biproduct` applied to the additive functor `relativeCohomology π (n + 1)`, with
  `isAffineOpen_inter` and `isZero_relativeCohomology_sheafOn` for the summands.

## Provenance

The mathematical content is the input to Stacks Project, Cohomology of Schemes, Lemma
`lemma-cech-cohomology-quasi-coherent` (tag 01XD): for a cover whose finite intersections are
affine, Čech cohomology of a quasi-coherent module computes its cohomology. The affineness of
the intersections over a separated base is Lemma `lemma-affine-diagonal` (tag 0BDX) of the
same chapter, and the vanishing on affine opens is Lemma
`lemma-quasi-coherent-affine-cohomology-zero` (tag 01XB). Source: `coherent.tex` of the
registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`), lines 146, 219 and 246. Stacks works with
`H^p(U, F)` directly; the Lean proof instead passes from `X` to the affine scheme `W` through
the pushforward comparison of the Library, because the terms of the sheafified complex are
pushforwards from the opens `𝒰.inter s`. The Lean proofs are this module's own.
