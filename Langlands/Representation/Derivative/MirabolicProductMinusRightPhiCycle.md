# The cyclic orbit piece of the right `Φ⁻` sequence

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of the
published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). Its main theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.rightPhiCyclePiece_iso
    (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r : ℕ) :
    Nonempty (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0) ≅
      rightPhiSubobject.{uF, uV} T ψ k r ⋙ SmoothRep.toRep)
```

for every prime `p`, `F : PadicField.{uF} p`, `T`, `ψ`, `k` and `r`, with
independent universes `uF`, `uV`. It is the isomorphism `E₀` required by the
published `rightPhiShortExact_of_pieces` (`MirabolicProductMinusRightPhiAssembly`):
the normalized localized orbit piece of `τ × ρ` at the cyclic representative is
`(Φ⁻τ) × ρ`, naturally in `τ` on `P_(r+2)` and `ρ` on `GL_(k+1)`. The clause itself
is proved in `MirabolicProductMinusRightPhi`.

## Provenance

BZ77 (`bernstein-zelevinsky-1977-induced-i`), Proposition 4.13(c), printed p.458
(PDF p.19), gives the subobject `Φ⁻(τ) × ρ` of `Φ⁻(τ × ρ)`; §7.2, printed p.471
(PDF p.32), identifies it with the contribution of the open orbit and leaves the
calculation to the reader. The route and all declarations of this module are
derived internal content; the localization of the orbit piece is computed with
the published `Induction.SplitStagesCharacter.comparisonEquiv`. The module
follows the identity-orbit module `MirabolicProductMinusRightPhiIdentity` step by
step and reuses its generic declarations `localizedActionEquiv`,
`localizedActionEquiv_natural`, `plusSubgroup_compactOpenBasis` and
`chain_natural₅`.

## The chain at an object

Let `t = k+r+1`, `Q = plusSubgroup t`, `P = rightStages k r 0`,
`S = rightCycStabilizer k r` and `K = P.comap plusSuccessor`
(`MirabolicProductMinusRightPhiCycleGroups`). For `X = (τ, ρ)` the equivalence
`E X` is the composite of

1. `rightCycleLocalizationEquiv₀`: the identity from `plusPhiLocalization` of the
   orbit piece to the published split-kernel `localizedAction`
   (`plusProjection`, `plusSuccessor`, `plusKernelThetaSmooth`) of the orbit
   piece;
2. `localizedActionEquiv` of `rightCycleOrbitEquiv`: the orbit piece is compact
   induction from `S` of `rightCycleCoefficient T k r τ ρ` (`χ_R (τ ⊠ ρ)` through
   the stabilizer), through the identity on vectors
   (`rightCycleOrbitCoefficient`, `rightCycleCoefficientBridge`,
   `compactInducedEquiv`);
3. the published `comparisonEquiv` at these data, to compact induction from `K`
   of the localized coefficient twisted by the Haar character;
4. under the `Φ⁻` twist `phiMinusCharacter T t`, the published
   `compactInductionTwistEquiv` moving the twist into the coefficient;
5. `rightCycleCompactEquivOf`: the published `compactInducedTransport` along
   `rightCycleCast` (the rank cast `P_(k+r+2) ≅ P_((k+1)+r+1)`, which carries `K`
   onto `rightSubgroup (k+1) r` by `mem_rightStages_zero_comap_iff`) with
   `rightCycleCoefficientEquiv`, followed by `compEquivOfEq` and
   `rightCycleCast_toMonoidHom` to the pullback along the published
   `mirabolicCastHom (Nat.succ_add k r)`. `rightCycleTarget T ψ k r` is the target
   `(Φ⁻τ) × ρ` with this explicit pullback.

The transport hypothesis `hE` is the coefficient action: by
`coefficientAction_mk`, `rightCycleCoefficientEquiv_section`,
`rightCycle_phiMinus_tmul` and `rightCycle_scalar_eq`, `l ∈ K` acts on the
coefficient by `χ_R'(l) (Φ⁻τ(p) ⊗ ρ(a))`, the normalized right mixed coefficient
of shape `(k+1, r)` of `(Φ⁻τ, ρ)`. The character `η` of the kernel intersection
is `θ_r` through `rightCycleKernelEquiv` by `thetaPlus_rightCycle`; this is the
hypothesis of `rightCycleCoefficientEquiv`.

The comparison data are proved as in the identity module: closedness and
containments from the groups module; `ker plusProjection` closed;
`plusSubgroup_compactOpenBasis`; local compactness, Borel structures, the kernel
basis and cover transported from the radical `V_(t+2)` along
`splitStagesKernelContinuousEquiv` and `plusKernelContinuousEquiv`
(`compactOpenBasis_of_continuousMulEquiv`, published `radical_compactOpenBasis`);
Haar measures, unimodularity from the published
`Haar.compactOpenCoverUnimodularity`, and a compatible quotient measure from
`QuotientIntegration.compatibleMeasureExists`. The coefficient is smooth
(published `isSmooth_comp`, `isSmooth_twist_iff`,
`isSmooth_rightInducingRepresentation`).

## Naturality and the isomorphism

For a morphism `φ = (f₁, f₂)`, `chain_natural₅` combines: the identity step
(classes go to classes); `localizedActionEquiv_natural`; the published
`comparisonEquiv_natural`; the published `compactInductionTwistEquiv_natural`;
and `rightCycleCompactEquivOf_natural`, whose coefficient condition is
`rightCycleCoefficientEquiv_natural` on the class map of `χ_R (f₁ ⊠ f₂)`.
`NatIso.ofComponents` with `Rep.mkIso` gives
`rightPhiPiece … ≅ rightCycleTarget T ψ k r ⋙ toRep`, and the published
`mirabolicRankCastIso` replaces the explicit pullback by the actual
`mirabolicRankCast T (Nat.succ_add k r)` of `rightPhiSubobject T ψ k r`.
The theorem uses `set_option maxHeartbeats 8000000`; it is a long proof whose
steps are each elementary.

## Imports

The direct imports are `MirabolicProductMinusRightPhiCycleCoefficient` and
`MirabolicProductMinusRightPhiIdentity` (generic chain lemmas, and through it
the assembly module, the right-`Ψ⁻` and right-boundary modules for lower lemmas
and `MirabolicProductRestrictionTransport` for `compactInducedTransport`). The
complete import closure and the restriction audit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPhi.md`.
