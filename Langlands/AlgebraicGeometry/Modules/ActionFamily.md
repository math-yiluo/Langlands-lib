# Families of modules with commuting degree-raising actions

Author: Worker 1645.

This module sets up sequences of module sheaves on a scheme with finitely many
commuting maps that raise the degree. It proves one uniform cohomology vanishing
statement for such families, by induction on the number of maps. It is internal
infrastructure for the uniform vanishing of the higher cohomology of twisted
ideal-adic layers.

## Families

- `ActionFamily X r` has modules `obj n : X.Modules` for `n : ℕ` and maps
  `act i n : obj n ⟶ obj (n + 1)` for `i : Fin r`. The field `comm` requires
  `act j n ≫ act i (n + 1) = act i n ≫ act j (n + 1)` for all `i`, `j`, `n`.
  Composition `≫` is in diagrammatic order.
- For `F : ActionFamily X (r + 1)`, `F.ker : ActionFamily X r` has the modules
  `kernel (F.act (Fin.last r) n)`. Its maps are the maps `kernel.map` induced by
  the remaining actions `F.act i.castSucc` (`ker_act_ι`). Likewise `F.coker` has
  the modules `cokernel (F.act (Fin.last r) n)` and the maps `cokernel.map`
  (`π_coker_act`). Both families satisfy `comm` because the actions of `F`
  commute.
- `secHom_comp_apply` says that the section map of a composite is the composite
  of the section maps. `mem_iSup_range_iff` says that `y` lies in the supremum of
  the ranges of finitely many linear maps `t i` exactly when `y = ∑ i, t i (x i)`
  for some `x`.

## Generation on a cover

Fix `U : ι → X.Opens` with `ι : Type u`. `F.IsGeneratedOn U` means that there is
`N₀` such that for all `n ≥ N₀` and all `l`,
`⨆ i, LinearMap.range (secHom (F.act i n) (U l)) = ⊤`. In words, on every
open `U l`, every section of `obj (n + 1)` is a sum of images of sections of
`obj n` under the actions. For `r = 0` the supremum is `⊥`, so the sections of
`obj (n + 1)` over each `U l` are zero.

- `isGeneratedOn_ker` assumes that `X` is locally noetherian, `ι` is finite,
  every `U l` is affine and every `F.obj n` has finite sections over affine
  opens (`HasFiniteAffineSections`). Then `F.IsGeneratedOn U` implies
  `F.ker.IsGeneratedOn U`. On each `U l`, the sections `K n` of the kernels form
  a family of submodules of `Γ(F.obj n, U l)` that is stable under the section
  maps of all actions. The ring `Γ(X, U l)` is noetherian, so
  `Langlands.Algebra.GradedStableGeneration.exists_stable_generation` gives
  `N₁ l` with `K (n + 1) = ⨆ i, (K n).map (act i n)` for `n ≥ N₁ l`. The image of
  the last action on `K n` is zero, and the other images are sections of the
  kernel maps, because sections of a kernel are the kernel of the section map
  (`QuasicoherentLocal.app_kernel_ι_app`, `exists_kernel_ι_app_eq`,
  `kernel_ι_app_injective`). The bound for the cover is the maximum of the
  `N₁ l`.
- `isGeneratedOn_coker` assumes that every `U l` is affine and every `F.obj n` is
  quasi-coherent. Then `F.IsGeneratedOn U` implies `F.coker.IsGeneratedOn U` with
  the same bound. Let `n ≥ N₀`. The degree `n + 1` module of `F.coker` is
  `cokernel (F.act (Fin.last r) (n + 1))`, a quotient of `F.obj (n + 2)`. So a
  section of it over the affine `U l` lifts through
  `cokernel.π (F.act (Fin.last r) (n + 1))` to a section of `F.obj (n + 2)`
  (`QuasicoherentLocal.surjective_app_of_epi`, using quasi-coherence of the
  cokernel). Generation of `F` at `n + 1` writes this lift as a sum of images
  of sections `x i` of `F.obj (n + 1)` under the actions `F.act i (n + 1)`. The
  term of the last action maps to zero in the cokernel (`cokernel.condition`).
  For `j : Fin r`, the term of `F.act j.castSucc (n + 1)` maps to the image
  under `F.coker.act j n` of the projection of `x j.castSucc` to
  `(F.coker).obj n = cokernel (F.act (Fin.last r) n)` (`π_coker_act`).

## Uniform vanishing

`exists_uniform_vanishing` has the following hypotheses:

- `X` is locally noetherian, `ι : Type u` is finite, every `U l` is affine and
  `⨆ l, U l = ⊤`;
- `f : X ⟶ Spec R` is any morphism, and `relativeCohomology f q` is the `q`-th
  right derived functor of the global sections, with values in `R`-modules;
- `P` is a property of modules such that every `M` with `P M` is quasi-coherent
  and has finite sections over affine opens, and `P (kernel φ)` and
  `P (cokernel φ)` hold for every `φ : M ⟶ N` with `P M` and `P N`;
- `T : ℕ → X.Modules ⥤ X.Modules` is a sequence of functors that preserve zero
  morphisms and short exact sequences;
- `hserre`: for every `M` with `P M` there is `d₀` such that
  `relativeCohomology f (p + 1)` of `(T d).obj M` is zero for all `d ≥ d₀` and
  all `p`;
- `F : ActionFamily X r` with `P (F.obj n)` for all `n`, and
  `F.IsGeneratedOn U`.

The conclusion is that there is one `d₀` such that
`relativeCohomology f (p + 1)` of `(T d).obj (F.obj n)` is zero for all
`d ≥ d₀`, all `n` and all `p`.

The proof is by induction on `r`.

- For `r = 0`, `F.obj (n + 1)` has zero sections over every `U l` once
  `n ≥ N₀`. Since it is quasi-coherent and the `U l` cover `X`, it is the zero
  module (`IntegralIdealFiltration.vanishesOn_of_affine`, `vanishesOn_iSup`,
  `NoetherianVanishing.isZero_of_vanishesOn_top`). So the cohomology of
  `(T d).obj (F.obj n)` vanishes for `n > N₀`
  (`NoetherianVanishing.isZero_relativeCohomology_of_isZero`). For `n ≤ N₀`
  take the maximum of the finitely many bounds from `hserre`.
- For `r + 1`, apply the induction hypothesis to `F.ker` and `F.coker`. Take
  `d₀` at least these two bounds and the `hserre` bound of `F.obj 0`. Then
  argue by induction on `n` with the map `φ = F.act (Fin.last r) n`. The
  vanishing of the cohomology in degree `p + 2` of `T d (kernel φ)` and in
  degree `p + 1` of `T d (cokernel φ)` and `T d (F.obj n)` implies the vanishing
  in degree `p + 1` of `T d (F.obj (n + 1))`
  (`SerreVanishing.isZero_cohomology_target`, which splits `φ` through its image
  into two short exact sequences).

## Provenance

Derived internal content. The proof of Stacks Project, Lemma 30.21.3 (tag
[02OF](https://stacks.math.columbia.edu/tag/02OF)) applies graded Serre
vanishing to the finite type graded module `⨁ n, 𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ` over `Gr_𝔪(A)`. This
module replaces that step by a dévissage on `X` itself. A family generated by
`r` commuting actions is cut down by the kernel and cokernel of the last action,
and Serre vanishing is used only for the individual members of the class `P`.
The finite generation of the kernel family is the graded Hilbert basis theorem
in the form of `GradedStableGeneration`.
