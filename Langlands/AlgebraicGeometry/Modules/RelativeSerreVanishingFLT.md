# Relative Serre vanishing for coherent presheaves (FLT Čech form)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.RelativeSerreVanishingFLT` (namespace
`Langlands.AlgebraicGeometry.Modules.CechBridge`) proves one helper theorem:

```lean
theorem exists_forall_subsingleton_HSucc_tensor_twist {A : Type u} [CommRing A]
    [IsNoetherianRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsClosedImmersion ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) (G : OModulePresheaf q)
    (hc : G.IsCoherent) (hq : G.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ i : ℕ,
      Subsingleton ((G.tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i)
```

For a closed subscheme `P` of `ℙʳ_A` over a noetherian ring and a coherent quasi-coherent FLT
presheaf `G`, the higher Čech cohomology of `G ⊗ O(d)` on the pulled-back standard cover vanishes
for all large `d`. This is relative Serre vanishing (The Stacks Project, Lemma 30.16.2, Tag 02O1;
literature id `stacks-projective-cohomology-ample-2026-11-13`).

The proof uses the FLT port's family results with the constant family `G k = G` and one frame map,
the identity:

1. `exists_isFG_hom_injective_saturated_familyFramesGradedModule` gives a finitely generated
   graded module `D` over `A[Y]` with an injective, saturated map into the graded module of
   frames of the family (the commutation condition and the generation condition hold trivially
   for the identity);
2. `ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated`
   (needing `A[Y]` noetherian) gives `d₀` beyond which the shifted graded Čech groups vanish in
   positive degrees;
3. `subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule` transfers
   this vanishing to `G ⊗ O(d)`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
