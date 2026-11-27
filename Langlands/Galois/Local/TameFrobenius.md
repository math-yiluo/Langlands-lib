# Frobenius acts on tame inertia by the `q`-th power

The module `Langlands.Galois.Local.TameFrobenius` provides the arithmetic input of
Grothendieck's monodromy argument for a nonarchimedean local field `K` of either
characteristic with a separable closure `Ω`. Write `p = ringChar 𝓀[K]` for the residue
characteristic and `q = Nat.card 𝓀[K]` for the residue cardinality. The results are used by
`Langlands.LadicMonodromy.finite_image_of_tameFrobenius` in the module
`Langlands.Representation.LadicMonodromy`.

## Finite level

In the namespace `Langlands.GaloisCohomology.Local`, for a finite extension `L/K` of
nonarchimedean local fields with `ValuativeExtension K L`, the module proves two results
about `integerAlgEquiv K L`, the action of `L ≃ₐ[K] L` on `𝒪[L]`, and the tame character
`inertiaToResidueUnits hϖ : G₀ →* 𝓀[L]ˣ`, `s ↦ s(ϖ)/ϖ mod 𝓂[L]`, of the module
`Langlands.GaloisCohomology.Local.Arithmetic.Ramification`:

- `residue_integerAlgEquiv_congr`: the residue of `σ x` depends only on the residue of `x`.
  This holds because `residue (σ x)` is `residueAlgEquiv K L σ (residue x)`.
- `inertiaToResidueUnits_conj`: let `σ` act on the residue field by the `q`-th power, in the
  sense that `σ z - z ^ q ∈ 𝓂[L]` for every `z : 𝒪[L]`. Then for every `s ∈ G₀` the tame
  character of `σ s σ⁻¹` is the `q`-th power of that of `s`.

For the proof of `inertiaToResidueUnits_conj`, write `u τ` for the unit with
`ϖ * u τ = τ ϖ` (`uniformizerRatio`). Then `u (τ * τ') = u τ * τ (u τ')`. Applying this
twice gives `u (σ s σ⁻¹) = u σ * σ (u s) * σ (s (u σ⁻¹))`. Applying it to `σ * σ⁻¹ = 1`
gives `u σ * σ (u σ⁻¹) = 1`. Since `s` acts trivially on residues, `σ (s (u σ⁻¹))` and
`σ (u σ⁻¹)` have the same residue. The residue of `σ (u s)` is the `q`-th power of the
residue of `u s`. Multiplying out gives the claim. This is the computation in Serre's proof
of Proposition 9 in IV §2, taken at index `0`, with `s` replaced by an automorphism acting on
the residue field by `x ↦ x ^ q`.

## Absolute level

The rest of the module is in the namespace `Langlands.LocalGalois.SepClosed`.

- `exists_normal_finiteIndex_subset`: for any Galois extension `Ω/K`, every neighbourhood of
  `1` in the Krull topology contains a normal subgroup of finite index. By
  `InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois` the neighbourhood contains the
  fixing subgroup of a finite Galois subextension `M`. That subgroup is the kernel of
  restriction to `M` (`IntermediateField.restrictNormalHom_ker`), a homomorphism to the
  finite group `M ≃ₐ[K] M`.
- `exists_frobenius_lift`: there is `φ : Ω ≃ₐ[K] Ω` acting on the residue field of
  `closureIntegers K Ω` by `x ↦ x ^ q`. The residue map `absoluteResidueHom K Ω` to the
  absolute Galois group of `𝓀[K]` is surjective (`absoluteResidueHom_surjective`). Take a
  preimage of the arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic`. By
  construction, `absoluteResidueHom` transports the residue action along
  `residueClosureEquiv K Ω`.
- `exists_tameFrobenius`: there is `φ : Ω ≃ₐ[K] Ω` with the following property. For every
  neighbourhood `U` of `1` there is a set `P` such that:
  - every `x ∈ P` has a power `x ^ p ^ a` in `U`;
  - `P` contains every commutator `x * y * x⁻¹ * y⁻¹` of elements of
    `absoluteInertia K Ω`;
  - `P` contains every `φ * x * φ⁻¹ * (x ^ q)⁻¹` with `x ∈ absoluteInertia K Ω`.

For the proof of `exists_tameFrobenius`, take `φ` from `exists_frobenius_lift`. Given `U`,
choose a finite Galois subextension `M` whose fixing subgroup lies in `U`. Give `M` the local
field structure `Ramification.Local.SepClosed.finiteTopologicalData K Ω M`. Let `r` be
restriction to `M`.

The inclusion of integers `finiteClosureIntegerMap K Ω M : 𝒪[M] → closureIntegers K Ω` is a
ring homomorphism compatible with `r`, so it maps units to units. Hence an element of `𝒪[M]`
whose image lies in the maximal ideal of `closureIntegers K Ω` lies in `𝓂[M]`. This
transfers two facts to `M`:

- absolute inertia acts trivially on the residue field of `closureIntegers K Ω`, so its
  restriction to `M` lies in the lower ramification group `G₀` of `M/K`;
- `r φ` acts on the residue field of `M` by the `q`-th power.

Choose a uniformizer `ϖ` of `M`. Let `Θ` be the composite of restriction from absolute
inertia to `G₀` with the tame character, and let `P` be the set of elements of absolute
inertia in the kernel of `Θ`. The three properties hold as follows:

- The kernel of the tame character is the first lower group `G₁`
  (`ker_inertiaToResidueUnits`). `G₁` is a `p`-group
  (`isPGroup_lowerRamificationGroup_one`). So for `x ∈ P`, `r (x ^ p ^ a) = 1` for some
  `a`, and `x ^ p ^ a` lies in the fixing subgroup of `M`, hence in `U`.
- `Θ` takes values in the commutative group `𝓀[M]ˣ`, so it kills commutators.
- `Θ (φ x φ⁻¹) = Θ x ^ q` by `inertiaToResidueUnits_conj`, since the restriction of
  `φ x φ⁻¹` is `r φ * r x * (r φ)⁻¹`. So `φ * x * φ⁻¹ * (x ^ q)⁻¹` lies in `P`.

## Sources and provenance

The finite-level facts used are those of Serre, *Local Fields*, IV §2, Proposition 7 at
index `0`, with Corollaries 1 and 3, printed pp. 67–68 (PDF pp. 74–75). They say that
`s ↦ s(ϖ)/ϖ` embeds `G₀/G₁` into the residue units, and that `G₁` is a `p`-group. These facts
are used through their formalization in
`Langlands.GaloisCohomology.Local.Arithmetic.Ramification`. The conjugation formula follows
the proof of Serre's Proposition 9, printed p. 69 (PDF p. 76), at index `0`. Serre states
that proposition for conjugation by elements of `G₀`; the same computation with an
automorphism acting by `x ↦ x ^ q` on the residue field gives `inertiaToResidueUnits_conj`.
The absolute statement is the form of "conjugation by `w` induces raising to the `‖w‖`
power in `I/P`" used in Tate's account of the monodromy theorem (Tate 1979, (4.2), p. 21).
Here it is expressed through the finite levels.

- J.-P. Serre, *Local Fields* (1979), `serre-1979-local-fields`, IV §2, Proposition 7 and
  Corollaries 1 and 3, pp. 67–68, and Proposition 9, p. 69. Retained PDF SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- J. Tate, *Number theoretic background* (1979), `tate-1979-number-theoretic-background`,
  (4.2), p. 21. Retained Corvallis Part II PDF SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
