# The centre of `R_Ω` lies in the centre of `R_D`: proof

Module `Langlands.Representation.CuspidalSupport.InducedProgeneratorCenterInclusionProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The theorem `inducedProgeneratorCenterInclusion` proves the published statement
`InducedProgeneratorCenterInclusionStatement` at the universe levels `u, v`. That is Renard
2026, VI.10.4, the second Lemma `ℨ_Ω ⊂ ℨ_D` and its consequence
`ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)` (printed p. 211, PDF p. 217). The statement is used exactly as published.
The proof adds no hypothesis.

## The claim

Let `k` be a non-archimedean local field, `G` a connected reductive group over `k`, and
`P = M N` an actual rational parabolic subgroup. Let `π` be an irreducible supercuspidal
representation of `M(k)` and `ρ₀` an irreducible representation of `⁰M(k)` with an injective
map `j : ρ₀ → π|_{⁰M(k)}`. Put `Π_D = ind_{⁰M(k)}^{M(k)} ρ₀` (`piD`) and
`I = i_P^G` (`leviInductionFunctor`). Then the centre of `End(I Π_D)` is the set of `I(z)`,
with `z` central in `End(Π_D)`, that commute with every element of `End(I Π_D)`.

The irreducibility of `π` and of `ρ₀` is not used.

## Route

Renard proves the Lemma with the free `ℨ_D`-module structure of `R_Ω` (the first Lemma of
VI.10.4) and the generic irreducibility VI.8.5. The Lean proof takes another route. It uses
neither of them, nor second adjointness or the projectivity of `Π_D`. It combines the
following helper results, all written for this proof:

1. `inducedCenter_eq_of_kernelVanishing`
   (`CuspidalSupport/InducedCenterFactorization`). For any smooth representation `σ` of
   `M(k)` in the universe `max u v`, Frobenius reciprocity reduces the set equality to a
   kernel vanishing property. Let `h : r_P^G(i_P^G σ) → σ` be an `M(k)`-map with
   `h ∘ r_P^G(i_P^G a) = a ∘ h` for every endomorphism `a` of `σ`. Then `h` must vanish on the
   classes of the induced functions `f` with `f(1) = 0`.
2. `leviJacquetInduction_hom_apply_mk_eq_zero` (`CuspidalSupport/InducedKernelVanishing`). It
   proves this kernel vanishing for every supercuspidal `σ` in which no `t ∈ M(k)` with
   `tⁿ ∉ ⁰M(k)` for all `n > 0` fixes a nonzero vector. The proof uses the support filtration
   of the geometric lemma, with the identity double coset `P · 1 · P` ordered last. It shows
   that every graded piece at a double coset `P w P` with `w ∉ M` admits only the zero map to
   `σ` that commutes with `End(σ)` (`CuspidalSupport/SelfIntersectionPieceVanishing`, using the
   published naturality `fullPieceEquiv_naturality` and Renard V.3.5,
   `leviNormalizerNormFixing`). It then vanishes step by step from the bottom of the filtration
   (`Filtration/NaturalHomStepVanishing`).
3. The two hypotheses on `Π_D`:
   - `isSupercuspidal_rationalNormKernelSummandInduction`
     (`CuspidalSupport/RationalSummandInductionSupercuspidal`): `Π_D` is supercuspidal,
     because `π` is and `ρ₀` embeds in `π|_{⁰M(k)}`.
   - `Induction.compactInduced_eq_zero_of_fixed` (`Induction/OpenNormalSubgroupInduction`):
     for an open normal subgroup `H` and an element `t` none of whose positive powers lies in
     `H`, the only compactly induced function fixed by right translation by `t` is zero.

## Proof

After introducing the data, the proof installs the instances of the statement on `M`: affine,
smooth, the Levi point topology, local compactness and the non-archimedean group structure.

1. `hsc`: `Π_D` is supercuspidal, by `isSupercuspidal_rationalNormKernelSummandInduction` applied
   to `π`, its supercuspidality, `ρ₀`, `j` and the injectivity of `j`.
2. `hfix`: let `t ∈ M(k)` with `tⁿ ∉ ⁰M(k)` for all `n > 0`, and let `v ∈ Π_D` with
   `Π_D(t) v = v`. `Π_D` is the compact induction from `⁰M(k)`, which is normal
   (`Plancherel.rationalCommonNormKernel_normal`) and open
   (`Plancherel.isOpen_rationalCommonNormKernel`). `compactInduced_eq_zero_of_fixed` gives
   `v = 0`.
3. Applying `inducedCenter_eq_of_kernelVanishing` with `σ = Π_D` leaves the kernel vanishing
   property. `Π_D` lies in `SmoothRep.{0, u, max u v}`, the universe of that theorem.
4. Given `h`, its commutation property `hh`, `f` and `f(1) = 0`, the theorem
   `leviJacquetInduction_hom_apply_mk_eq_zero` with `hsc` and `hfix` gives `h(mk f) = 0`.

Step 4 passes the arguments one at a time, in successive `have`s, and names the parabolic data
`p, l, r, hp, hr, hl, hmul` explicitly. Elaborating the whole application at once exceeds the
heartbeat limit. The file sets `backward.isDefEq.respectTransparency false`, as the helper
module `InducedKernelVanishing` does.

## Helper modules

The proof depends on these helper modules, which were written for it. Each has its paired Markdown:

- `Langlands/Representation/Induction/OpenNormalSubgroupInduction`
- `Langlands/Representation/CuspidalSupport/RationalSummandInductionSupercuspidal`
- `Langlands/Representation/Filtration/NaturalHomStepVanishing`
- `Langlands/Representation/CuspidalSupport/InducedCenterFactorization`
- `Langlands/Representation/CuspidalSupport/SelfIntersectionPieceVanishing`
- `Langlands/Representation/CuspidalSupport/InducedKernelVanishing`
