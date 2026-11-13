# Ample-fibre covers of abelian schemes over noetherian affine bases

This helper module, in namespace `Langlands.AlgebraicGeometry.Picard`, proves that an abelian
scheme over the spectrum of a noetherian ring has an ample-fibre cover (`HasAmpleFibreCover`,
from `AmpleFibreCover`) of its whole base.

## Results

- `exists_ampleFibre_piece A₀ x`, for a noetherian `R₀`, `A₀ : AbelianScheme (Spec R₀)` and a
  point `x`. It produces an affine `T`, a map `g : T ⟶ Spec R₀`, a Cartesian square
  `IsPullback a q A₀.X.hom g`, and a line bundle `L` on `W` with two properties:
  `g '' ampleFibreLocus q L` is constructible, and it contains `x`. The proof:
  1. Let `K` be the residue field of `x`. The published `fieldAmpleExistence` gives an ample
     line bundle `L_K` on the base change of `A₀` to `Spec K`.
  2. The published `lineBundleSubalgebraDescent` descends `L_K` to a line bundle `L` on the base
     change `W` of `A₀` to `Spec B`. Here `B` is a finitely generated `R₀`-subalgebra of `K`, and
     the descent holds up to isomorphism after pullback along the comparison map `c`. Put
     `g = Spec(R₀ → B)` and `κ = Spec(B → K)`.
  3. The square for `c` over `κ` is Cartesian. The pullback of `L` along `c` is isomorphic to
     `L_K`, hence ample, and ampleness survives restriction to the fibre over the closed point
     (`IsAmple.pullback_of_isAffineHom`). By `mem_ampleFibreLocus_iff_of_isPullback`, the point
     `t = κ(closed point)` lies in `ampleFibreLocus q L`, and an ideal computation gives
     `g t = x`.
  4. `B` is of finite type over `R₀`, hence noetherian. So the open set `ampleFibreLocus q L`
     (`isOpen_ampleFibreLocus`) is compact in a noetherian space and is therefore constructible.
  5. `R₀ → B` is of finite presentation because `R₀` is noetherian. Mathlib's Chevalley theorem
     `PrimeSpectrum.isConstructible_comap_image` then shows that the image under `g` is
     constructible.
- `exists_finset_cover_of_isConstructible C hC hcov`. Let `X` be a compact, quasi-sober,
  prespectral, quasi-separated space (that is, a spectral space). A cover of `X` by constructible
  sets `C i` has a finite subcover. Each `C i` is open in `constructibleTopology X`, by
  `constructibleTopology_eq_generateFrom_isConstructible`. That topology is compact
  (Mathlib's `WithConstructibleTopology` instance), so `isCompact_univ.elim_finite_subcover`
  applies.
- `noetherian_hasAmpleFibreCover A₀`. Over a noetherian affine base, `A₀` has
  `HasAmpleFibreCover A₀.X.hom Set.univ`. For every point `x`, choose the piece from
  `exists_ampleFibre_piece`. Then extract a finite subcover of these constructible pieces with
  `exists_finset_cover_of_isConstructible`, indexed by a `Finset` of points. `Spec R₀` is spectral,
  and these instances are found automatically.

## Provenance

Internal helper lemmas. The mathematical ingredients are standard and are used here only through
their formal Library and Mathlib counterparts:

- existence of an ample line bundle on an abelian variety over a field (`fieldAmpleExistence`);
- descent of line bundles along filtered colimits of rings (`lineBundleSubalgebraDescent`);
- Chevalley's theorem on constructible images under finitely presented morphisms
  (`PrimeSpectrum.isConstructible_comap_image`);
- compactness of the constructible topology of a spectral space.
