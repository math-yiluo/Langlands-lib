# Twisted descent in congruence subgroups for cyclic base change

`Langlands.BaseChange.CongruenceTwistedDescent`. Namespace `Langlands.BaseChange`.

The algebra near the identity used by the matching of test functions near `1`
(`NearIdentityConcordance`, `NearIdentityMatching`): a predicate for subgroups of `GL_n(E)` on which
σ-conjugacy and `l`-th powers descend to `GL_n(F)`, the σ-centralizers of their rational elements,
and the spectral congruence subgroups as examples, with the descent of σ-conjugacy near `1` and the
power map on `GL_n(F)`.

## Statements

Throughout `F` is a field, `E` a field with `[Algebra F E]`, `σ : E ≃ₐ[F] E`, `l n : ℕ`.

- `baseChange_injective : Function.Injective (baseChange F E n)`.
- `cyclicNorm_baseChange σ l y : cyclicNorm σ l (baseChange F E n y) = baseChange F E n (y ^ l)`,
  the case `δ = 1` of `cyclicNorm_mul_baseChange` of `Langlands.BaseChange.Norm`.

The descent of σ-fixed elements of `GL_n(E)`,
`IsCyclicAlgebra.exists_baseChange_eq_of_entrywiseAut_eq (hσ : IsCyclicAlgebra σ l)`:
`entrywiseAut σ n g = g → ∃ x, baseChange F E n x = g`, is in `Langlands.BaseChange.Norm`.
- `IsTwistedDescentSubgroup F σ l K` for `K : Subgroup (GeneralLinear n E)` (a structure in `Prop`):
  - `entrywiseAut_mem : ∀ g ∈ K, entrywiseAut σ n g ∈ K`;
  - `rational_of_twistedConj`: for `u u' : GeneralLinear n F` with `baseChange u ∈ K`,
    `baseChange u' ∈ K` and `g : GeneralLinear n E` with
    `g⁻¹ * baseChange u * entrywiseAut σ n g = baseChange u'`, there is `x` with `baseChange x = g`;
  - `conj_of_conj_pow`: for such `u`, `u'` and `y : GeneralLinear n F`,
    `y⁻¹ * u ^ l * y = u' ^ l → y⁻¹ * u * y = u'`.
- `IsTwistedDescentSubgroup.sigmaCentralizer_eq`: for `baseChange u ∈ K`,
  `sigmaCentralizer σ n (baseChange F E n u) = (glCentralizer (u ^ l)).map (baseChange F E n)`.

Over a nonarchimedean local field `F` (`[ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, normed by `LocalGalois.localNormedField F`) and `E` with
`[FiniteDimensional F E] [TopologicalSpace E] [IsModuleTopology F E]` and the spectral norm
(`LocalGalois.finiteExtensionNormedField F E`), the statements below are written with these
structures installed by `letI`; `normCongruence` is that of `Langlands.Group.GL.NormCongruence`.

- `baseChange_mem_normCongruence_iff r γ`:
  `baseChange F E n γ ∈ normCongruence E n r ↔ γ ∈ normCongruence F n r`.
- `entrywiseAut_mem_normCongruence_iff σ r g`:
  `entrywiseAut σ n g ∈ normCongruence E n r ↔ g ∈ normCongruence E n r`.
- `isTwistedDescentSubgroup_normCongruence (hσ : IsCyclicAlgebra σ l) (hr₀ : 0 ≤ r) (hr₁ : r < 1)`:
  `r < ‖(l : F)‖ → IsTwistedDescentSubgroup F σ l (normCongruenceSubgroup E n hr₀ hr₁)`.
- `exists_twistedConj_baseChange_mul_eq (hσ) (hr₀ : 0 ≤ r)`: if `r < ‖(l : F)‖`,
  `u₀ ∈ normCongruence F n r` and `g ∈ normCongruence E n (r * ‖(l : F)‖)`, there are
  `κ ∈ normCongruence E n r` and `u ∈ normCongruence F n r` with
  `baseChange u₀ * g = κ⁻¹ * baseChange (u₀ * u) * entrywiseAut σ n κ`.
- `isOpen_twistedConj_normCongruence [IsTopologicalRing E] (hσ) (hr₀ : 0 < r)`: if `r < ‖(l : F)‖`,
  the set `{g | ∃ κ ∈ normCongruence E n r, ∃ u ∈ normCongruence F n r,
  g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ}` is open.
- `pow_image_normCongruence (hr₀ : 0 ≤ r)`: if `r < ‖(l : F)‖`,
  `(fun u => u ^ l) '' normCongruence F n r = normCongruence F n (r * ‖(l : F)‖)`.

## Proofs

- Rationality of σ-fixed elements: entrywise, by the last clause of `IsCyclicAlgebra` (the
  fixed field of `σ` is `F`); the determinant is nonzero because `algebraMap` commutes with it.
- σ-centralizer: an element of the σ-centralizer of `baseChange u` is rational by
  `rational_of_twistedConj`, then commutes with `u`, hence with `u ^ l`; conversely an element
  commuting with `u ^ l` commutes with `u` by `conj_of_conj_pow`, and is fixed by `σ`.
- Spectral congruence subgroups: `σ` and `algebraMap F E` are isometries of the spectral norm, so
  `map_mem_normCongruence_iff` applies. If `g⁻¹ u σ(g) = u'` with `u`, `u'` rational, taking norms
  (`cyclicNorm_twistedConj`, `σ^l = 1`) gives `g⁻¹ u^l g = u'^l`, so `g⁻¹ u g = u'` by
  `conj_eq_of_conj_pow_eq` in `GL_n(E)` (`‖(l : E)‖ = ‖(l : F)‖ > r`), hence `σ(g) = g` and `g` is
  rational. The descent of σ-conjugacy is `exists_mul_eq_twistedConj` for `τ = σ` (`σ^[l] = id`);
  the `σ`-fixed `u` it produces is rational. Openness: around `κ₀⁻¹ u₀ σ(κ₀)` the open set
  `κ₀⁻¹ u₀ · normCongruence E n (r ‖l‖) · σ(κ₀)` lies in the set, by the descent with centre `u₀`.
  Powers: `pow_mem_normCongruence` and `exists_pow_eq` over `F` (which is proper).

## Declarations, in order

`baseChange_injective`, `cyclicNorm_baseChange`, `IsTwistedDescentSubgroup`, `IsTwistedDescentSubgroup.sigmaCentralizer_eq`,
`baseChange_mem_normCongruence_iff`, `entrywiseAut_mem_normCongruence_iff`, private
`iterate_algEquiv`, `isTwistedDescentSubgroup_normCongruence`,
`exists_twistedConj_baseChange_mul_eq`, `isOpen_twistedConj_normCongruence`,
`pow_image_normCongruence`.

## Literature

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011): §I.2.2 (σ-orbits, σ-centralizers and the norm lemma,
  pp. 11–12) for the notions; §II.6.7, p. 123, for the use of the openness of the norm near `1`
  ("la norme … est continue et submersive (donc ouverte) au voisinage de 1").
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), Chapter 1, §3, p. 21: near `1` the `l`-th power map of `T(F)` is an
  isomorphism and `T(F)` parametrizes the σ-conjugacy classes of `T(E)`; p. 25 (end of the proof of
  Lemma 3.4): for `t` in the σ-centralizer of `δ₀`, `N(δ₀ t) = t^l γ₀`. For `δ₀ = 1` the σ-centralizer
  is `G(F)`, which is `IsTwistedDescentSubgroup.sigmaCentralizer_eq` near `1`.

## Source and licence

Port of parts of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, under
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/`:
`NearCore.lean` lines 35–54 and 95–139 (`incl_inj`, `norm_incl`, `root_conj`, `rigid`, `cent_eq`),
`RigidNear.lean` lines 5–20 (`rigidNear`), `Bridge.lean` lines 14–32 (`mem_range_incl`), and
`NearDown.lean` lines 165–172 and 221–235 (`near`, the image of the power map in `exists_push`),
`NearUp.lean` lines 181–196 (openness of the image of `p`). The repository has no licence file; its
text is used with attribution (see
`licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- The source's `incl`, `sigmaGL`, `normGL`, `twCent`, `ball` are the Library's `baseChange`,
  `entrywiseAut`, `cyclicNorm`, `sigmaCentralizer`/`glCentralizer`, `normCongruence`; the source's
  Galois hypotheses (`IsGalois`, `σ` generating the group) are replaced by `IsCyclicAlgebra σ l`.
- The three properties the matching uses are collected in the new predicate
  `IsTwistedDescentSubgroup`, so that the σ-centralizer equality (source `cent_eq`, proved there
  for the ball only) holds for any such subgroup.
- The source takes roots in `GL_n(E)` and descends them with `exists_fixed_root`; here roots are
  taken in `GL_n(F)` directly with the norm of `F`.
- The radius is a real number with `r < ‖(l : F)‖` instead of an element of the value group of `E`.
