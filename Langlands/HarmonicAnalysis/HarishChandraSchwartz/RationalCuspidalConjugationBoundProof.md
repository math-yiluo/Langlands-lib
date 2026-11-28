# Waldspurger VIII.3.1 for the actual intrinsic cuspidal Schwartz kernel

`Langlands.HarishChandraSchwartz.rationalCuspidalConjugationBound` proves
`RationalCuspidalConjugationBoundStatement.{u}` (module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationStatement`)
at an arbitrary universe `u`. The theorem has no hypotheses; its type is
exactly the statement. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.
[Target statement](RationalCuspidalConjugationStatement.md) ·
[Assembly](RationalCuspidalConjugationAssembly.md)

## The statement

Let `F` be a nonarchimedean local field (of either characteristic), `G` an
affine, locally finite type connected reductive group scheme over `F`,
`i : S → G` a maximal split torus, `ν` a generic cocharacter with minimal
standard parabolic `P₀ = standardParabolicPoints i ν ∅`, and `K0` any subgroup
of `G(F)` with `SimultaneousStandardBasisAt i ν K0`. Let `K` be any compact open
subgroup with `G(F) = P₀(F) K`, `ρ` any closed matrix representation on a
nonempty finite index (height `σ = rationalHeight ρ`) and `muG` any Haar
measure on `G(F)`. Then `RationalCuspidalConjugationBound hKc hPK ρ muG`
holds:

1. for every `f₁` in the intrinsic cuspidal submodule
   `rationalCuspidalSubmodule hKc hPK ρ`, every `f₂` in
   `RationalSchwartzSpace hKc hPK ρ` and every `h ∈ G(F)`, the function
   `g ↦ f₁(h g h⁻¹) f₂(g)` is `Integrable` for `muG`;
2. for every such `f₁`, `f₂` and every real `r` there is a real `c > 0` with

   ```
   ‖∫ f₁(a g a⁻¹) f₂(g) dmuG(g)‖ ≤ c δ₀(a) (1 + σ(a))^(-r)
   ```

   for every `a` in `rationalMinimalChamberInNormKernel i ν`, the full
   chamber `componentPlus` of the minimal Levi intersected with the common
   norm kernel `G¹`. Here `δ₀ = rationalMinimalModulus i ν` and the integral
   is `rationalConjugationPairing`, without complex conjugation.

The cases of relative rank zero, nonsplit and non-quasisplit groups are
included; no rank, splitness or characteristic condition is assumed.

## The proof

The Lean term is one application:

```
rationalCuspidalConjugationBound_of_prerequisites
  ⟨jointSpecialCompactBasisExistence, rationalXiUpperBound,
    rationalConstantTermEstimate⟩
```

`rationalCuspidalConjugationBound_of_prerequisites` (module
`RationalCuspidalConjugationAssembly`) derives the statement from
`RationalCuspidalConjugationPrerequisites`, the conjunction of three
closed propositions. Each is proved by a theorem of the Library, with no
hypotheses of its own:

- `JointSpecialCompactBasisExistenceStatement`, by
  `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`). For every
  nonarchimedean local field, connected reductive `G`, maximal split torus
  `i` and generic `ν`, one apartment datum `D` and special vertex `x` give a
  compact open subgroup `D.specialCompactSubgroup x` with Renard's special
  compact properties (V.5.1), standard-Levi inheritance, the Iwasawa products
  for `G` and every standard Levi, the Cartan comparisons for `G` and the
  standard Levis, and the simultaneous standard basis (V.5.2), all for the
  same `D`, `x` and one represented torus centralizer.
  [Proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `RationalXiUpperBoundStatement`, by `rationalXiUpperBound` (module
  `RationalXiUpperBoundProof`): given a subgroup with
  `SimultaneousStandardBasisAt i ν K0`, a compatible split component `q` of
  the minimal Levi, a compact open `K` with `G(F) = P₀(F) K` and a closed
  matrix representation, there is `d ∈ ℕ` such that for all `g₁, g₂` there
  is `C` with `Ξ(g₁ a g₂) ≤ C δ₀(a)^{1/2} (1 + σ(a))^d` on the weak chamber
  `C_A^+` (Lemma II.1.1, in the uniform form of the proof of II.1.2).
  [Proof](RationalXiUpperBoundProof.md)
- `RationalConstantTermEstimateStatement`, by `rationalConstantTermEstimate`
  (module `RationalConstantTermEstimateProof`): given `J ⊆ Δ` and a compact
  open `K0` with `SimultaneousStandardBasisAt i ν K0`, the finite Cartan
  covering of `G(F)` and the Cartan covering of `M_J(F)`, a compact open `K`
  with the Iwasawa decompositions of `G(F)` and `M_J(F)`, a closed matrix
  representation and a Haar measure on `U_J(F)`, the constant-term estimate
  of Proposition II.4.5 holds for the opposite parabolic `P̄_J`.
  [Proof](RationalConstantTermEstimateProof.md)

## Route of the assembly

The assembly, which this theorem applies, proceeds as follows; its
Markdown gives more detail.

- If `simpleRelativeRoots i ν` is empty,
  `rationalCuspidalConjugationBound_of_simpleRoots_empty` (module
  `RationalCuspidalConjugationRankZero`) proves the conclusion directly: the
  norm kernel is compact, `Ξ = 1`, and the chamber in `G¹` is compact.
- Otherwise `exists_constantTermPremises_of_joint` (module
  `RationalSpecialCompactConstantTermPremises`) turns the joint witness into
  a compact open `K0'` with `G(F) = P₀(F) K0'`, the simultaneous basis, the
  finite Cartan covering of `G(F)` and, for every `J ⊆ Δ`, the Cartan
  covering of `M_J(F)` and `M_J(F) = (P₀(F) ∩ M_J(F))(K0' ∩ M_J(F))`.
- With `Ξ` built from `K0'`, the Xi upper bound gives weighted square
  integrability (`rationalXiSquareIntegrable_of_upperBound`) and hence the
  convergence for every conjugator
  (`rationalCuspidalConjugationConverges_of_squareIntegrableWeight`). The
  chamber is covered by finitely many simple-root sectors; on each, the
  maximal proper standard parabolic of the sector gives an open-cell split,
  cuspidality gives zero integral over the opposite radical, and the
  constant-term estimate in both orientations, the Levi Xi bound and the
  modulus identity give the sector estimate. The sum of the sector constants
  bounds the whole chamber.
- `rationalCuspidalConjugationBound_of_compact` (module
  `RationalCuspidalCompactComparison`) transfers the complete conclusion,
  convergence and chamber estimate, from `K0'` to the arbitrary compact open
  Iwasawa subgroup `K` of the statement; the Schwartz space, cuspidal
  submodule, height, measure and pairing are the same functions under the
  change of compact.

The subgroup `K0` quantified by the statement is not used: the structural
compact comes from the joint witness, and `K` remains arbitrary.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, Proposition VIII.3.1 and its proof, printed
pp. 323–326 (PDF pp. 89–92). Registered source `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
On printed p. 325 the reference to VII.2.1 for cuspidal vanishing should read
VIII.2.1. The Lean proof uses the intrinsic cuspidal kernel of the Library
(`rationalCuspidalSubmodule`), defined by integrability and vanishing of the
constant terms along every proper standard parabolic, for every Haar measure
on its unipotent radical and every two-sided translate; it does not identify
this kernel with the image of Waldspurger's recursive VIII.2 construction.
