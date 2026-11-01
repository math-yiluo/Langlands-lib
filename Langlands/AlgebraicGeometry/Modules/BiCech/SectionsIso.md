# Global sections of the bi-Čech complex are the tensor total complex

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.SectionsIso`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

## Linear maps for a general bi-cover

These are stated for a general `𝒲 : BiCover P`, `F` and `π : P ⟶ Spec R`.

- `insT_add` gives additivity of the concentrated sections of `BiCech.GlobalSections`.
- `algebraMap_biOpen` matches the `R`-module structures of global sections and of
  sections over `biOpen s t`.
- `insLin` and `compLin` are `insT` and `compF`, as `R`-linear maps between bidegree
  `(p, q)` families and `R`-module global sections
  (`DerivedSections.relativeGlobalSections π`).
- `asΓ`, `famΓ`, `toΓ` and `ofΓ` are identity maps. They only change the stated type, so
  that rewriting is possible.

## Product setting

The setting is that of `BiCech.ProductSections`. Hypotheses `hU`, `hV`: all finite
intersections `𝒰.inter s` and `𝒱.inter t` are affine. Hypotheses `hL`, `hM`: all of them
carry frames of `L` and `M`.

- `totCech πX πY 𝒰 𝒱 L M` is the total complex
  `HomologicalComplex.mapBifunctor (cechCochainComplex πX 𝒰 L) (cechCochainComplex πY 𝒱 M)
  (curriedTensor (ModuleCat R)) (ComplexShape.up ℕ)`. It uses the tensor signs
  `Langlands.Cohomology.ModuleComplex.tensorSignsUpNat` (Worker 1137), with
  `ε₁ = 1` and `ε₂(p, q) = (-1)^p`.
- `sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M` is `relativeGlobalSections πP` applied termwise to
  `bicechComplex (prodBiCover p₁ p₂ 𝒰 𝒱) (p₁^* L ⊗ p₂^* M)`.
- `cupFamT` is `cupFam` with source the tensor product in `ModuleCat R`, and
  `cupFamEquiv` is the linear equivalence given by `cupFam_bijective`.
- `sectionsHom n` is defined by `HomologicalComplex.mapBifunctorDesc`. On the summand
  `C^p ⊗ C^q` it is `insLin ∘ cupFamT` (`ι_sectionsHom`, `ι_sectionsHom_apply`).
- `invComponent`, `invLin` and `sectionsInv n` form the inverse. It sums over the
  bidegrees `(p, q)` of the antidiagonal of `n`, the summand inclusion composed with
  `cupFamEquiv.symm ∘ compLin`.
- `sectionsHom_invLin`: `sectionsHom ∘ invLin = id`. It is checked on components with
  `compF_insT_self` and `compF_insT_ne`.
- `invLin_insT`: `invLin ∘ sectionsHom = id` on every summand.
- `sectionsHom_comm`: `sectionsHom` commutes with the differentials. This is checked on
  pure tensors of each summand. The total differential is
  `d₁ + d₂ = (d ▷ _) ≫ ι + (-1)^p • (_ ◁ d) ≫ ι` (`mapBifunctor.d₁_eq`, `d₂_eq`). The
  bi-Čech side is computed by `D_insT`, `horF_cupFamFun` and `verF_cupFamFun`.
- `sectionsIso hπ hP 𝒰 𝒱 L M hU hV hL hM : totCech πX πY 𝒰 𝒱 L M ≅ sectionsBicech ...`
  is built by `HomologicalComplex.Hom.isoOfComponents`.

Provenance: internal. This is the identification of the Čech double complex of a product
cover with the tensor product of the Čech complexes of the factors (Stacks Project,
Varieties, tag 0BED, proof), carried out for the bi-Čech complex.
