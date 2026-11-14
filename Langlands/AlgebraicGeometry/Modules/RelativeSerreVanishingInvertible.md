# Relative Serre vanishing for invertible modules

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.RelativeSerreVanishingInvertible` (namespace
`Langlands.AlgebraicGeometry.Modules.CechBridge`) proves

```lean
theorem exists_isZero_relativeCohomology_tensor_tensorPow [IsNoetherianRing A] [IsSeparated f]
    [IsClosedImmersion 𝔓.toProj] (hL : Scheme.Modules.IsInvertible L) (F : X.Modules)
    (hF : Scheme.Modules.IsInvertible F) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ i : ℕ, 0 < i →
      IsZero ((DerivedSections.relativeCohomology f i).obj (F ⊗ L.tensorPow d))
```

for `f : X ⟶ Spec A` separated over a noetherian ring and `𝔓 : L.ProjPresentation f N` (FLT
port) whose morphism to `ℙᴺ_A` is a closed immersion. For every invertible `F`, the actual
cohomology of `F ⊗ L^{⊗ d}` (FLT tensor products and tensor powers) vanishes in positive degrees for
all large `d`. This is relative Serre vanishing (The Stacks Project, Lemma 30.16.2, Tag 02O1;
literature id `stacks-projective-cohomology-ample-2026-11-13`) in the Library's cohomology.

## Proof

Let `K` be the pulled-back standard cover `ProjSpace.stdCoverPullback 𝔓.toProj`. Its
intersections lie in charts (`inter_le_pullbackChart`).

1. `RelativeSerreVanishingFLT` applied to `G = ofModules f F` gives `d₀` with
   `HSucc` of `G ⊗ O(d)` zero for `d ≥ d₀`. The FLT theorems
   `isCoherent_ofModules_of_locallyTrivial` and `isQuasicoherent_ofModules_of_locallyTrivial`
   supply the hypotheses.
2. `nonempty_hsucc_twist_equiv_tensor`: the FLT theorem
   `ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2` gives natural maps
   `Γ(L^{⊗ d}, U) → O(d)(U)`, bijective on opens inside a chart. With `tensorRightAffHom` and
   `hsuccEquivOfBijective`, the `HSucc` groups of `G ⊗ O(d)` and of `G ⊗ ofModules(L^{⊗ d})` agree.
3. `nonempty_hsucc_tensor_equiv_ofModules`: with `tensorSectionsAffHom`, those of
   `G ⊗ ofModules(L^{⊗ d})` agree with those of `ofModules(F ⊗ L^{⊗ d})`.
4. `nonempty_hsucc_ofModules_equiv`: those agree with the actual cohomology in degree `j + 1`
   (`hsuccEquivRelativeCohomology`). Invertible modules are quasi-coherent
   (`IsLocallyFreeRankOne.isQuasicoherent`).

The groups in positive degrees are therefore trivial. The steps are separate lemmas returning
`Nonempty` equivalences, and the theorem transports subsingletons along them. The module uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.
