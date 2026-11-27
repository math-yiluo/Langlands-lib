# Cutting ordinary test functions by a norm condition on the determinant

This module proves two derived lemmas used to pass from the regular σ-lift identity
`IsRegularSigmaLift` to the Shintani identity `IsShintaniLift`, in the module
`Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularForward`.
`IsRegularSigmaLift` restricts the ordinary test function to matrices whose determinant
lies in the norm image \(N_{E/F}(E^\times)\). These lemmas let the proof impose that
restriction on a concordant pair without changing its twisted orbital integrals.

## The norm image is clopen

Let `F` be a nonarchimedean local field of characteristic zero (`Field`, `ValuativeRel`,
`TopologicalSpace`, `IsNonarchimedeanLocalField`, `CharZero`).

- `range_pow_mem_nhds_one_of_localField` proves that for `m ≠ 0` the set of `m`-th powers
  of units, `Set.range (fun x : Fˣ => x ^ m)`, is a neighborhood of `1` in `Fˣ`. The proof
  gives `F` the normed field structure `LocalGalois.localNormedField F`, whose topology
  is the given one and for which `F` is complete (`LocalGalois.localNormedField_complete`).
  It then applies `Langlands.Global.AdelicFunctoriality.range_pow_mem_nhds_one`, the
  inverse function theorem for `x ↦ x ^ m` at `1`.
- `isOpen_normUnitsRange` proves that for every commutative `F`-algebra `E` with
  `Module.finrank F E ≠ 0`, the subgroup
  `(Units.map (Algebra.norm F : E →* F)).range` of `Fˣ` is open. It contains every
  `x ^ (finrank F E)` for `x : Fˣ`, the norm of the image of `x` in `E`
  (`Algebra.norm_algebraMap`), so it is a neighborhood of `1`. A subgroup that is a
  neighborhood of a point is open (`Subgroup.isOpen_of_mem_nhds`).
- `isClopen_normUnitsRange` adds closedness: an open subgroup is closed
  (`Subgroup.isClosed_of_isOpen`).

No finiteness hypothesis on `E` appears. If `E` is not a finite `F`-module, then
`finrank F E = 0`, which the hypothesis excludes. For a cyclic algebra
`IsCyclicAlgebra σ l`, the dimension is `l > 0`.

## A one-sided cutoff preserves concordance

`ConcordanceLocalization.concordant_cutoff_ordinary` is the one-sided variant of
`ConcordanceLocalization.concordant_cutoff`. Its setting is that of `concordant_cutoff`:
a field `F` and a commutative `F`-algebra `E`, both topological rings, Borel measurable
structures on `GL_n(F)` and `GL_n(E)`, and measures `μF` and `μE`. Let `φ` on
`GL_n(E)` and `f` on `GL_n(F)` be concordant Schwartz–Bruhat functions
(`AreConcordant σ l μF μE φ f`). Let `q : GL_n(F) → Y` be continuous and invariant
under conjugation, and let `B ⊆ Y` be clopen. Suppose that `q γ ∈ B` whenever `γ` is
associated with some `δ` (`IsNormAssociated σ l δ γ`). Then `φ` and the cutoff
`cutoff (hB.preimage hq) f`, which is `f` on `q ⁻¹' B` and `0` elsewhere, are
concordant.

By `ConcordanceLocalization.orbital_cutoff`, the orbital integral of the cutoff at `γ`
is the orbital integral of `f` at `γ` if `q γ ∈ B` and `0` otherwise. At regular
non-norms the orbital integral of `f` is zero, so the cutoff's is zero too. At an
associated regular pair `(δ, γ)` the hypothesis gives `q γ ∈ B`, so the cutoff's orbital
integral at `γ` is that of `f`. It therefore equals the twisted orbital integral of `φ` at
`δ`, for every compatible choice of quotient measures.

In `RegularForward`, `q` is the determinant `GeneralLinear.determinant`, continuous by
`Matrix.GeneralLinearGroup.continuous_det` and invariant under conjugation. `B` is the norm
image, clopen by `isClopen_normUnitsRange`. For an associated pair,
`IsNormAssociated.norm_determinant_units_eq` gives \(\det\gamma = N_{E/F}(\det\delta)\),
so \(\det\gamma\) lies in the norm image.

## Sources

These lemmas are derived. In Henniart–Lemaire (2011), II.6.8 and II.6.13 (printed
p. 129, PDF p. 137), the chosen auxiliary ordinary functions \(f_v\) at the places
\(v \in S \setminus \{v_0, v_1\}\) are supported in \(G(F_v)_r \cap N_v(G(E_v))\). For
concordant test pairs, the ordinary orbital integrals vanish at regular non-norms. The
cutoff in this module imposes a different condition, the norm condition on determinants
required by `IsRegularSigmaLift`. Arthur–Clozel (1989), Chapter 1, §6.3 (printed p. 57,
PDF p. 71), observes that the determinant twists on the right of (6.5) have coinciding
local characters on the image of the norm. The lemmas above let the Library's forward
argument for II.2.9 meet the norm condition of `IsRegularSigmaLift`.

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour
  GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011). Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula*, Annals of Mathematics Studies 120 (1989). Source ID
  `arthur-clozel-1989-base-change`.
