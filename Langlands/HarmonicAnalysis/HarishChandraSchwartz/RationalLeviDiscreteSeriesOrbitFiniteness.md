# Discrete-series orbits under topological group isomorphisms; Theorem VIII.1.2 for `M_I(F)`

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFinitenessStatement`
  (Library, this author's Unit 2): `RationalDiscreteSeriesOrbitFinitenessStatement` (Theorem
  VIII.1.2 for a connected reductive group scheme, statement). Through its imports come
  `rationalDiscreteSeriesFixedOrbits`, the abstract `discreteSeriesFixedOrbits`,
  `DiscreteSeriesClass`, `IsDiscreteSeriesClass`, `DiscreteSeriesOrbitClass`, the action of
  `unitaryUnramifiedCharacters`, `commonNormKernel`, `IsSquareIntegrableModCentralSubgroup`,
  `UnitaryCentralCharacter`, `centralSubgroupCoefficientNorm`, `SmoothDualClass.HasFixedVector`,
  `SmoothDualClass.twist`, `IrreducibleAdmissibleRep.isoMk`, `equivOfRepresentationEq` and
  `rationalPoints_nonarchimedeanGroup`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients` (Library, Unit 19)
  for the local instances on `G(F)`, and `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme`
  (Library, this author's) for `leviScheme_isAffineHom` and `leviScheme_locallyOfFiniteType`.
- `Langlands.Representation.Aubert.General.RationalLeviNormTopology` (Library):
  `leviRationalPointHomeomorph i ν I : L(F) ≃ₜ* M_I(F)`, `leviRationalNormCharacters` and
  `leviRationalNormCharacters_apply_points`.
- `Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof` (Library, proved):
  `standardLeviSplitComponentStatement` (the Levi scheme of a standard parabolic of a connected
  reductive group is connected reductive and has a split component).
- `Langlands.Representation.CompactCoefficient.GroupTransport` (Library): `SmoothRep.pullback`,
  `SmoothRep.pullbackEquiv`, `isIrreducible_comp_continuousMulEquiv_iff`.
- `Langlands.Representation.CuspidalSupport.GroupTransport` (Library):
  `fixedVectors_comp_mulEquiv`, `isAdmissible_comp_continuousMulEquiv_iff`. Through its imports:
  `isSmoothVector_dual_comp_continuousMulEquiv_iff`.

From Mathlib: `QuotientGroup.congr`, `MeasurableEmbedding.memLp_map_measure_iff`,
`Homeomorph.measurableEmbedding`, `MeasurableEquiv.map_map_symm`,
`ContinuousMulEquiv.isHaarMeasure_map` (instance), `Set.Finite.of_finite_image`.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234. The author checked the quotations on the rendered PDF
page 87.

- Théorème VIII.1.2, printed p. 321: "Pour tout sous-groupe ouvert compact `H` de `G`, `Θ^H_G`
  est fini."
- Remarque VIII.1.3, printed p. 321: "Supposons le Théorème VIII.1.2 vrai pour tout sous-groupe
  de Lévi d'un sous-groupe parabolique semi-standard, resp. et propre, de `G`. [...]" The proof
  (VIII.1–VIII.5) proceeds by induction on the semisimple rank: "Nous supposerons désormais les
  deux théorèmes démontrés pour tout groupe de rang semi-simple strictement inférieur à celui de
  `G`."

Waldspurger applies Theorem VIII.1.2 to the Levi subgroups `M` of `G`, viewed as reductive groups
in their own right. In the Library, the statement `RationalDiscreteSeriesOrbitFinitenessStatement`
concerns a connected reductive group scheme and its rational points, while the actual Levi
subgroup `M_I(F)` of the units on actual points is a subgroup of `G(F)`. This module (provenance:
internal) supplies the adapter: the transport of all objects in `Θ^K` along a topological group
isomorphism, applied to `L(F) ≃ₜ* M_I(F)`. The source does not discuss this identification.

## Contents

### Classes (section `Classes`; `e : H ≃ₜ* G`, `G`, `H` groups with topologies)

- `IrreducibleAdmissibleRep.pullback e A`: the irreducible admissible representation `A ∘ e` of `H`
  (irreducibility and admissibility by the Library's transport lemmas);
  `IrreducibleAdmissibleRep.pullback_representation` (`rfl`).
- `SmoothDualClass.pullback e`: the induced map on classes (`Quotient.map`); `pullback_mk`.
- `SmoothDualClass.pullback_injective e`: if `A ∘ e ≅ B ∘ e` then `A ≅ B` (the same linear
  equivalence intertwines `A(g)` and `B(g)` for `g = e(e⁻¹ g)`).
- `SmoothDualClass.hasFixedVector_pullback e K ω`: `A ∘ e` has a nonzero `K`-fixed vector iff `A`
  has a nonzero `(K.comap e⁻¹)`-fixed vector (`fixedVectors_comp_mulEquiv`).
- `SmoothDualClass.pullback_twist e χ hχ hχe ω`: `(ω ⊗ χ) ∘ e = (ω ∘ e) ⊗ (χ ∘ e)`.

### Central characters (section `CentralCharacter`)

- `centerHomOfEquiv e : Z(H) →* Z(G)` (the restriction of `e`) and its continuity.
- `UnitaryCentralCharacter.pullback e c` (from `ρ` to `ρ ∘ e`) and
  `UnitaryCentralCharacter.ofPullback e c` (from `ρ ∘ e` to `ρ`).

### Square integrability (section `SquareIntegrable`)

Moreover: `G`, `H` topological groups, normal central subgroups `A ≤ G`, `B ≤ H` with
`hAB : e(B) = A` (`B.map e = A`), Borel structures on `G ⧸ A` and `H ⧸ B`, Haar measures `μG`,
`μH` with `hμ : μH.map φ = μG`, where:

- `quotientContinuousMulEquiv e A B hAB : (H ⧸ B) ≃ₜ* (G ⧸ A)` is `φ`, the isomorphism induced by
  `e` (`QuotientGroup.congr`, continuous in both directions); `quotientContinuousMulEquiv_mk`.
- `centralSubgroupCoefficientNorm_pullback`: the coefficient norms of `ρ ∘ e` on `H ⧸ B` are those
  of `ρ` on `G ⧸ A` composed with `φ`, for any unitary central characters `c`, `c'`.
- **`isSquareIntegrableModCentralSubgroup_comp_iff e A hA B hB hAB μG μH hμ ρ`**: `ρ ∘ e` is
  square integrable modulo `B` for `μH` iff `ρ` is square integrable modulo `A` for `μG`.
- `isDiscreteSeriesClass_pullback_iff` (on classes), `DiscreteSeriesClass.pullback` (the map
  `E₂(G) → E₂(H)` modulo `A`, `B`) and `DiscreteSeriesClass.pullback_injective`.

### Orbits (section `Orbits`)

Moreover: `G`, `H` nonarchimedean, `νG : I → (G →* ℝ≥0ˣ)`, `νH : I → (H →* ℝ≥0ˣ)` with
`hν : ∀ i h, νG i (e h) = νH i h` (so the unitary unramified characters correspond).

- `unitaryUnramifiedPullback e νG νH hν : unitaryUnramifiedCharacters νG →*
  unitaryUnramifiedCharacters νH`, `χ ↦ χ ∘ e`; `unitaryUnramifiedPullback_apply`;
  `norm_characters_symm_compat`; `unitaryUnramifiedPullback_surjective` (by `e⁻¹`).
- `DiscreteSeriesClass.pullback_smul`: pullback commutes with the twist action.
- **`discreteSeriesOrbitPullback e νG νH hν A hA B hB hAB μG μH hμ`** (definition, the recorded
  declaration): the induced map `DiscreteSeriesOrbitClass A hA μG νG →
  DiscreteSeriesOrbitClass B hB μH νH` on orbits of `Im X` in `E₂`; `discreteSeriesOrbitPullback_mk`.
- `discreteSeriesOrbitPullback_injective`.
- `discreteSeriesOrbitPullback_mem … K hx`: it maps `Θ^K_G = discreteSeriesFixedOrbits A hA μG νG K`
  into `Θ^{e⁻¹(K)}_H = discreteSeriesFixedOrbits B hB μH νH (K.comap e)`.
- **`finite_discreteSeriesFixedOrbits_of_pullback … K hfin`**: if `Θ^{e⁻¹(K)}_H` is finite, so is
  `Θ^K_G`.

### Actual Levi subgroups (section `Rational`)

The setting of Units 19–29: `F` a nonarchimedean local field, `G` a group scheme over `F` with
`[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]`, `i` a maximal split torus, `ν` a
cocharacter, `I` a finite set of simple roots, `M_I(F)` the subtype `𝐌` of `G(F)`, and
`L = Standard.leviScheme i ν (rootSet i ν I)` the Levi group scheme (local notation `𝐋`).

- **`rationalLeviSplitCenter I a`** (definition): for `a : T → L`, the image in `M_I(F)` of
  `a(T(F))` under `leviRationalPointHomeomorph i ν I : L(F) ≃ₜ* M_I(F)`. For a split component
  `a` this is Waldspurger's `A_{M_I}` (rational points of the maximal split central torus of
  `M_I`), realized inside `M_I(F)`.
- `rationalLeviSplitCenter_le_center I a ha`: for `ha : IsSplitComponent a`, it is central.
- `exists_isSplitComponent_standardLevi I hG hi hν`: for connected reductive `G`, `L` has a split
  component (from `standardLeviSplitComponentStatement`).
- **`finite_discreteSeriesFixedOrbits_standardLevi I hVIII hG hi hν a ha μM L hL`**: if
  `hVIII : RationalDiscreteSeriesOrbitFinitenessStatement` holds, then for every split component
  `a` of `L`, every Haar measure `μM` on `M_I(F) ⧸ rationalLeviSplitCenter I a` (with a Borel
  structure) and every compact open subgroup `L` of `M_I(F)`, the set
  `discreteSeriesFixedOrbits (rationalLeviSplitCenter I a) _ μM (leviRationalNormCharacters i ν I) L`
  is finite. This is Theorem VIII.1.2 for `M_I(F)`, in exactly the form of the hypothesis `hfin`
  (for `C = A_{M_I}(F)`) used for Remark VIII.1.3 on actual points.

## Proofs

- Classes: `Quotient.map` with the pulled-back equivalence (`SmoothRep.pullbackEquiv`) for
  well-definedness; injectivity by rebuilding an equivalence `A ≃ B` from `A ∘ e ≃ B ∘ e` using
  `e (e⁻¹ g) = g`; fixed vectors by `fixedVectors_comp_mulEquiv`; twists by
  `equivOfRepresentationEq rfl`.
- Central characters: compose with `centerHomOfEquiv e` or `e⁻¹`; the action is transported by
  `e (e⁻¹ z) = z`.
- Square integrability: admissibility by `isAdmissible_comp_continuousMulEquiv_iff`; a central
  character in each direction as above; smooth functionals of `ρ` and `ρ ∘ e` are the same linear
  forms (`isSmoothVector_dual_comp_continuousMulEquiv_iff`); the coefficient norms correspond
  under `φ` (checked on `QuotientGroup.mk h` by `rfl`), and `MemLp f 2 (μH.map φ) ↔
  MemLp (f ∘ φ) 2 μH` because `φ` is a measurable embedding (a homeomorphism between Borel
  spaces).
- Orbits: `Quotient.map`, compatible with the actions by `DiscreteSeriesClass.pullback_smul` (from
  `SmoothDualClass.pullback_twist`). Injectivity: if `ψ · (b ∘ e) = a ∘ e`, write
  `ψ = χ ∘ e` (surjectivity) so `(χ · b) ∘ e = a ∘ e`, hence `χ · b = a`. Membership: rewrite
  with `hasFixedVector_pullback` and `(K.comap e).comap e⁻¹ = K`. Finiteness:
  `Set.Finite.of_finite_image` with the injective map and the inclusion of the image.
- Actual Levi: `standardLeviSplitComponentStatement` gives `IsConnectedReductive L`; the
  rational-point topology of `L` is the Library's (local instances for the Levi scheme as in
  `RationalLeviScheme`). Take `B = a(T(F))`, `hAB` by `rfl`, `μH = μM.map φ⁻¹` (a Haar measure by
  `ContinuousMulEquiv.isHaarMeasure_map`) with `μH.map φ = μM` (`MeasurableEquiv.map_map_symm`),
  and the compact open subgroup `L.comap e` of `L(F)`. Apply `hVIII` to `L`, `a`, `μH` and
  `L.comap e`, then `finite_discreteSeriesFixedOrbits_of_pullback` with
  `νH = (rationalNormCharacters L ·).toMul` and `νG = leviRationalNormCharacters i ν I`, whose
  compatibility is `leviRationalNormCharacters_apply_points`.

## Scope

- Theorem VIII.1.2 itself is not proved: the actual result is conditional on the published
  statement `hVIII`, which is open.
- The central subgroup is the image of a split component `a` of `L`; for another central subgroup
  `C` of `M_I(F)` the result is not stated.
- Only standard Levi subgroups `M_I` are treated; semi-standard Levi subgroups are not.
