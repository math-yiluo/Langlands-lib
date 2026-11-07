# Level towers away from the places dividing an integer

Author: Worker 13.

This internal construction applies the published splitting of finite adelic
points to the level towers of a rational involution, and then to the Harris
unitary level tower. Let `σ : AlgebraInvolution ℚ A` be an involution of a
finite-dimensional `ℚ`-algebra `A`, let `X` be a space with an action of the
rational similitudes `σ.similitudes`, and let `m ≠ 0`. The published
`Langlands.Shimura.Unitary.PointsSplit` gives the splitting

`e = σ.finiteAdelicPointsSplit m hm : σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints m × σ.PrimeToPoints m`,

written `GG(A_f) ≃ₜ* GG(∏_{v ∣ m} ℚ_v) × GG(A_f^{(m)})`, where the product is
over the finite places whose prime ideal contains `m`. Fix a compact open
level `K₀` of `GG(∏_{v ∣ m} ℚ_v)`. The module identifies the tower of level
spaces

`K' ↦ σ.similitudes \ (X × GG(A_f)) / e⁻¹ (K₀ × K')`

over the levels `K'` of `GG(A_f^{(m)})` with the tower of prime-to-`m` level
spaces

`K' ↦ σ.similitudes \ ((X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀) × GG(A_f^{(m)})) / K'`.

For a presheaf on spaces it gives the induced isomorphisms of towers, of
colimits with their action of `GG(A_f^{(m)})`, and of smooth representations.
All of these are instances of `Langlands.Shimura.SplitLevelSpace`, submitted
together with this module.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*
(`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), lets the
level `K(N)^{ℓ,p}` away from `ℓ` and `p` vary, with
`GG(A_f^{ℓ,p})`-equivariance. Taking `m` divisible by exactly the primes `ℓ`
and `p` would place such levels in `GG(A_f^{(m)})`, with the component at
the places above `ℓ` and `p` fixed as `K₀`. This module does not make that
identification: it does not identify the places whose prime ideal contains `m`
with rational primes, `σ` with Harris's inner form, or `σ.Points` with
Harris's group `GG`. Harris's passage is motivation only; no statement from it
is formalized. The prime-to-`m` domain and tower are implementation choices,
not attributed to a source.

The module constructs no Shimura variety, no cohomology and no spectral
sequence. It does not vary `K₀`, and it does not treat levels of `GG(A_f)` that
are not of the form `e⁻¹ (K₀ × K')`.

## Inputs

All declarations are in namespace `Langlands.Shimura`.

The published `Langlands.Shimura.Unitary.Adelic` provides the point groups
`σ.Points S` with their topologies and topological group structure (for
`Module.Finite ℚ A`), the diagonal homomorphisms
`σ.diagonalPoints S : σ.similitudes →* σ.Points S`, the finite adelic points
`σ.FiniteAdelicPoints` and the diagonal
`σ.finiteAdelicDiagonal = σ.diagonalPoints (FiniteAdeles ℚ)`.

The published `Langlands.Shimura.Unitary.PointsSplit` provides
`σ.DividingPoints m`, the points over
`Π v : {v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1`,
`σ.PrimeToPoints m`, the points over `PrimeToFiniteAdeles m`, the splitting
`σ.finiteAdelicPointsSplit m hm`, and `finiteAdelicPointsSplit_diagonal`: the
splitting sends `σ.finiteAdelicDiagonal g` to
`(σ.diagonalPoints _ g, σ.diagonalPoints _ g)`.

The module `Langlands.Shimura.SplitLevelSpace` of the same contribution
provides, for a splitting
`e : G ≃ₜ* H × H'`, `ι : Γ →* G`, homomorphisms `ι₁ : Γ →* H` and
`ι₂ : Γ →* H'` with `hι : ∀ γ, e (ι γ) = (ι₁ γ, ι₂ γ)`, and a level `K₀` of `H`:
the domain `LevelSpace.AwayDomain X ι₁ K₀`, which is `X × H ⧸ K₀` with `Γ`
acting diagonally and through `ι₁` on the cosets; the point
`LevelSpace.awayPoint e ι₁ K₀ (x, g) = ((x, (e g).1 K₀), (e g).2)`; and
`LevelSpace.awayTowerIso`, `awayTowerPresheafIso`, `awayActionIso` and
`awaySmoothRepIso`.

The published `Langlands.Shimura.Levels`, `Langlands.Shimura.LevelColimit` and
`Langlands.Shimura.SplitLevelTower` provide the level spaces
`LevelSpace ι K` with classes `LevelSpace.mk`, the tower `LevelSpace.tower`,
`LevelSpace.isLevelTrivial_tower`, the ordered synonym `Ordered G`,
`LevelColimit.action`, `LevelColimit.smoothRep`, the level functor
`CompactOpenLevel.awayOver e K₀`, whose functor sends `K'` to
`transport e.symm (prod K₀ K')`, the away tower `LevelColimit.awayTower` and
`LevelColimit.awaySmoothRep`.

The published `Langlands.Shimura.Unitary.HarrisLevels` provides, for
`D : CentralSimpleUnitaryData E K A n`, `h : HasHarrisSignature
D.toSecondKindInvolution n`, an imaginary quadratic field `F` with
`ιF : F →+* K` and `τ₀ : F →+* ℂ`: the CM-type section
`harrisCMSection E ιF τ₀` with `isCMSection_harrisCMSection E ιF τ₀`, the
charts `HarrisSignatureCharts.ofSignature h _` with their domain `Domain` and
its action of the rational similitudes of
`D.toSecondKindInvolution.rationalInvolution`, and the Harris tower
`harrisUnitaryLevelTower D h ιF τ₀`, which is by definition `LevelSpace.tower`
for this domain and `finiteAdelicDiagonal`.

## For a rational involution

These declarations are in namespace `Langlands.Shimura.AlgebraInvolution`.
Here `A` is a `ℚ`-algebra, `σ : AlgebraInvolution ℚ A` and `m : ℕ`.

- `σ.dividingDiagonal m : σ.similitudes →* σ.DividingPoints m` and
  `σ.primeToDiagonal m : σ.similitudes →* σ.PrimeToPoints m` are the published
  diagonal homomorphisms `σ.diagonalPoints _` into the two factors.
The remaining declarations of this section assume `Module.Finite ℚ A`, which
the published splitting and the topological group structure of the point
groups require.

- `finiteAdelicPointsSplit_finiteAdelicDiagonal σ m hm g`: for `m ≠ 0` the
  splitting sends `σ.finiteAdelicDiagonal g` to
  `(σ.dividingDiagonal m g, σ.primeToDiagonal m g)`. This is
  `finiteAdelicPointsSplit_diagonal`, and it is the hypothesis `hι` of
  `SplitLevelSpace` for this splitting.

Let `X` be a type with an action of `σ.similitudes`.

- `σ.PrimeToDomain m X K₀`, for a compact open level `K₀` of
  `σ.DividingPoints m`, is `LevelSpace.AwayDomain X (σ.dividingDiagonal m) K₀`:
  the domain `X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀`, on which the rational similitudes
  act diagonally, on the cosets by left multiplication through
  `σ.dividingDiagonal m`.

Assume `X` has a topology.

- `σ.primeToLevelTower m X K₀ : CompactOpenLevel (σ.PrimeToPoints m) ⥤ TopCat`
  is `LevelSpace.tower` for the domain `σ.PrimeToDomain m X K₀` and the
  homomorphism `σ.primeToDiagonal m`, the tower of prime-to-`m` level spaces.

Assume `hm : m ≠ 0`, and write `e = σ.finiteAdelicPointsSplit m hm`.

- `σ.primeToTowerIso m X hm K₀` is the natural isomorphism

  `(awayOver e K₀).functor ⋙ LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal) ≅ σ.primeToLevelTower m X K₀`,

  namely `LevelSpace.awayTowerIso` with `hι` the lemma above.
  `primeToTowerIso_hom_app_mk` states, by `rfl`, that its component at `K'`
  sends the class of `x : X × GG(A_f)` to the class of
  `LevelSpace.awayPoint e (σ.dividingDiagonal m) K₀ x`.

Let `P : TopCatᵒᵖ ⥤ C` be a presheaf on spaces with values in a category `C`.

- `σ.primeToPresheafIso m X hm K₀ P` is the isomorphism of presheaves on the
  levels of `GG(A_f^{(m)})` from
  `LevelColimit.awayTower e K₀ ((LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal)).op ⋙ P)`
  to `(σ.primeToLevelTower m X K₀).op ⋙ P`, namely
  `LevelSpace.awayTowerPresheafIso`.
- `σ.primeToActionIso m X hm K₀ P`: if colimits of shape
  `(Ordered (σ.PrimeToPoints m))ᵒᵖ` exist in `C`, the isomorphism of the
  objects `LevelColimit.action` of `Action C (σ.PrimeToPoints m)` on the
  colimits of these two presheaves, namely `LevelSpace.awayActionIso`.
- `σ.primeToSmoothRepIso m X hm K₀ P`: for a commutative ring `R`, a presheaf
  `P` of `R`-modules, and colimits of shapes
  `(Ordered σ.FiniteAdelicPoints)ᵒᵖ` and `(Ordered (σ.PrimeToPoints m))ᵒᵖ` in
  `ModuleCat R`, the isomorphism of smooth representations of
  `σ.PrimeToPoints m` from `LevelColimit.awaySmoothRep e K₀` of the first
  presheaf to `LevelColimit.smoothRep` of the second, namely
  `LevelSpace.awaySmoothRepIso`. The level-triviality arguments are
  `LevelSpace.isLevelTrivial_tower σ.finiteAdelicDiagonal P` and
  `LevelSpace.isLevelTrivial_tower (σ.primeToDiagonal m) P`.

## For the Harris unitary level tower

These declarations are in namespace `Langlands.Shimura`. As in the published
`harrisUnitaryLevelTower`, `E` is a totally real number field, `K` a totally
complex quadratic extension of `E`, `A` an algebra over `E`, `K` and `ℚ` with
the scalar towers `E → K → A`, `ℚ → E → A` and `ℚ → K → A`,
`D : CentralSimpleUnitaryData E K A n`, `h` the Harris signature hypothesis,
and `F`, `ιF`, `τ₀` as above; moreover `Module.Finite ℚ A` is assumed. Write
`σ = D.toSecondKindInvolution.rationalInvolution` and `X` for the domain of
`HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)`.
Let `K₀` be a compact open level of `σ.DividingPoints m`.

- `harrisPrimeToLevelTower D h ιF τ₀ m K₀` is `σ.primeToLevelTower m X K₀`,
  the Harris level tower away from the places whose prime ideal contains `m`.
- `harrisPrimeToTowerIso D h ιF τ₀ m hm K₀`, for `m ≠ 0`, is the natural
  isomorphism

  `(awayOver (σ.finiteAdelicPointsSplit m hm) K₀).functor ⋙ harrisUnitaryLevelTower D h ιF τ₀ ≅ harrisPrimeToLevelTower D h ιF τ₀ m K₀`,

  namely `σ.primeToTowerIso m X hm K₀`. It typechecks because
  `harrisUnitaryLevelTower D h ιF τ₀` is by definition
  `LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal)`.
- `harrisPrimeToPresheafIso D h ιF τ₀ m hm K₀ P`,
  `harrisPrimeToActionIso D h ιF τ₀ m hm K₀ P` and
  `harrisPrimeToSmoothRepIso D h ιF τ₀ m hm K₀ P` are
  `σ.primeToPresheafIso`, `σ.primeToActionIso` and `σ.primeToSmoothRepIso` for
  this domain, under the same colimit hypotheses. They identify the away tower
  at `K₀` of `P` on the Harris tower, with its colimit, its action of
  `GG(A_f^{(m)})` and, for presheaves of modules, its smooth representation,
  with the corresponding objects for `P` on the Harris prime-to-`m` tower.

## Proof outline

Every declaration is an instance of a declaration of `SplitLevelSpace`, with
`ι = σ.finiteAdelicDiagonal`, `ι₁ = σ.dividingDiagonal m`,
`ι₂ = σ.primeToDiagonal m` and `hι = finiteAdelicPointsSplit_finiteAdelicDiagonal`.
The Harris declarations are the rational ones for the Harris domain; they
typecheck because the Harris tower unfolds to `LevelSpace.tower`.
`primeToTowerIso_hom_app_mk` holds by `rfl`.
