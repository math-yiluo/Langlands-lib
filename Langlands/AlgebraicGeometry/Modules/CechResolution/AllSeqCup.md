# Cohomology classes and the cup product of ordered Čech cocycles

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCup`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.

## Purpose

Earlier modules prove two things about ordered Čech cochains over all tuples:
their cohomology is actual cohomology (`AllSeq.cohomologyIso`), and the
canonical structure-sheaf pullback is computed by `Langlands.Cohomology.Cech.pull`
(`AllSeq.cohomologyIso_comp_relativeCohomologyPullback_unit`). This module
transports the Library's ordered Čech product of `1`-cocycles
(`Langlands.Cohomology.Cech.cup₁`, from `Cohomology.CechCup`) to actual
structure-sheaf cohomology.

The resulting product `H¹(X, 𝒪_X) × H¹(X, 𝒪_X) ⟶ H²(X, 𝒪_X)` is `R`-bilinear and
graded anticommutative. The canonical pullback commutes with it.

## Cohomology classes (section `Classes`)

For `π : X ⟶ Spec R`, a finite family `U`, and `M : X.Modules`:

- `cyclesOfKer π U M n` sends a cocycle in `ker (dCochain π U M (n + 1))` to the
  cycles of `cochainComplex π U M` in degree `n + 1`. It is defined by
  `liftCycles`, and `cyclesOfKer_i` says that it recovers the cocycle.
- `classMap π U M n` is the `R`-linear class map
  `ker (dCochain (n + 1)) ⟶ (cochainComplex π U M).homology (n + 1)`, namely
  `cyclesOfKer ≫ homologyπ`.
- `classMap_surjective`: every class is the class of a cocycle.
- `classMap_eq_zero_iff`: the class vanishes iff the cocycle is a coboundary
  `dCochain n y`. This uses the Library's
  `exists_toCycles_eq_of_homologyπ_eq_zero`.
- `homologyMap_classMap`: a map of cochain complexes sends the class of `z` to
  the class of its image. `chainMap_mem_ker` shows that the image is again a
  cocycle.

## Chain-level identity (section `ChainLevel`)

For a presheaf of commutative rings `P` and `1`-cochains `z`, `w`:

- `mulPt P z w` is the pointwise product `σ ↦ z σ * w σ`.
- `cup₁_add_cup₁_swap`: if `z` and `w` are cocycles, then
  `cup₁ z w + cup₁ w z = d (-(mulPt z w))`.

The proof evaluates at `τ = (τ₀, τ₁, τ₂)`. Write `a_ij = z(τ_i, τ_j)` and
`b_ij = w(τ_i, τ_j)`, restricted to `inter U τ`. The cocycle conditions give
`a₀₂ = a₀₁ + a₁₂` and `b₀₂ = b₀₁ + b₁₂`. Then
`a₀₁ b₁₂ + b₀₁ a₁₂ = -(a₁₂ b₁₂ - a₀₂ b₀₂ + a₀₁ b₀₁)`. This needs no division,
so it holds in every characteristic.

## The product (section `Cup`)

- `unitModule X := SheafOfModules.unit X.ringCatSheaf`. The `R`-module cochains
  `cochain π U (unitModule X) p` are definitionally the Library's
  `Cech.C (Cech.ab X.presheaf) U p`. `dCochain_unit` shows that `dCochain`
  agrees with `Cech.d`.
- `cup π U z b := Cech.cup₁ X.presheaf U z b`, the product of a `1`-cochain and
  a `q`-cochain.
- `algC`, `smul_apply`, `res_appLE`, `face_smul`: the `R`-action on cochains is
  multiplication by the image of `R` in the sections, and this image is
  compatible with restriction.
- `cup_add_left`, `cup_add_right`, `cup_smul_left`, `cup_smul_right`, and
  `cupL q` (the bilinear map): the product is `R`-bilinear.
- `dCochain_cup` is the Leibniz rule `d (z ∪ b) = -(z ∪ d b)` for a cocycle `z`,
  from the Library's `d_cup₁_of_cocycle`. `cup_dCochain_zero` says that
  `(d y) ∪ b` is a coboundary for a cocycle `b`, from `d_cup₀`.
- `cup_mem_ker`, `cupZ`, `cupZ_apply`: the bilinear product of two
  `1`-cocycles, landing in `2`-cocycles.
- `cupClassZ` is `cupZ` followed by `classMap`.
  `cupClassZ_eq_zero_of_left` and `cupClassZ_eq_zero_of_right` show that it
  vanishes when either cocycle is a coboundary.
- `cupH : homology 1 →ₗ[R] homology 1 →ₗ[R] homology 2` is the descended
  product. Its construction identifies `homology 1` with the quotient of
  `1`-cocycles by the kernel of `classMap` (`quotKerEquivOfSurjective`) and
  lifts twice. `cupH_classMap` gives
  `cupH (classMap z) (classMap w) = classMap (cupZ z w)`.
- `cupH_add_swap` and `cupH_swap` state `cupH x y = -cupH y x`. They follow from
  `cup₁_add_cup₁_swap`.

## Naturality (section `Naturality`)

For `h : Y ⟶ X` over `Spec R` and an index map `α` with
`V j ≤ h⁻¹ U (α j)`:

- `unitCochainMap h U V α hα` is `cochainMap h (unitToPushforwardUnit h.left) U V α hα`.
  `unitCochainMap_eq_pull` shows that it is `Cech.pull h.left U V α hα`, by
  `cochainMap_unit_f_apply`.
- `cup₁_eq_prod`: `cup₁ z w = Cech.prod 2 ![z, w]`.
- `unitCochainMap_cup`: `unitCochainMap` preserves the product of `1`-cochains,
  by the Library's `pull_prod`.
- `homologyMap_cupH`: the map induced on ordered Čech cohomology preserves `cupH`.

## Actual cohomology (sections `Canonical` and `CanonicalNaturality`)

Assume `π` is separated, `U` covers `X` (`hU`), and each `U i` is affine (`hUa`).

- `cohomologyEquiv π U hU hUa n` is `AllSeq.cohomologyIso` as a linear
  equivalence.
- `cupCanonical π U hU hUa : H¹(X, 𝒪_X) →ₗ[R] H¹(X, 𝒪_X) →ₗ[R] H²(X, 𝒪_X)` is
  `cupH` transported along `cohomologyEquiv`. Here `Hⁿ(X, 𝒪_X)` means
  `(relativeCohomology π n).obj (unitModule X)`. `cupCanonical_apply` unfolds
  the definition.
- `canonicalClass π U hU hUa n` is the actual class of an ordered Čech cocycle.
  It satisfies `canonicalClass_surjective` and `canonicalClass_eq_zero_iff`
  (vanishing iff the cocycle is a coboundary). `cupCanonical_canonicalClass`
  says that on classes the product is the product of cocycles.
- `cupCanonical_swap`: `cupCanonical x y = -cupCanonical y x`.
- `pull_cohomologyEquiv`: the canonical pullback
  `relativeCohomologyPullback h 𝒪_X n ≫ (relativeCohomology Y.hom n).map (pullbackUnitIso h.left).hom`
  corresponds to `homologyMap (unitCochainMap …) n`. This restates
  `cohomologyIso_comp_relativeCohomologyPullback_unit`.
- `pull_cupCanonical`: that canonical pullback sends `cupCanonical X.hom U hU hUa x y`
  to `cupCanonical Y.hom V hV hVa` of the pullbacks of `x` and `y`. The
  hypotheses are an index map `α` with `V j ≤ h⁻¹ U (α j)` and the covering and
  affineness hypotheses for `U` and `V`.
- `pull_canonicalClass`: on classes of cocycles, that canonical pullback is the
  class of `unitCochainMap` of the cocycle, which is `Cech.pull`.

This canonical pullback is exactly the `pull f` of
`Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonStatement`.

## Scope

`cupCanonical` is built from a chosen finite affine covering family. This module
proves neither that the product is independent of that choice nor that
`cupCanonical x x = 0`. Only anticommutativity is proved. In characteristic
`2`, anticommutativity does not imply alternation.

## Provenance

This is internal infrastructure. The product is the cup product of Čech
cochains of The Stacks Project, Cohomology of Sheaves, Section "Čech cohomology
of complexes" (tag 01FP), as formalized in the Library's `Cohomology.CechCup`.
The anticommutativity identity is the standard degree-one computation, written
without division by `2`. The transport and the naturality are formal
consequences of the modules `CechResolution.AllSeqCohomology` and
`CechResolution.AllSeqPullback`.
