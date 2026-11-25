/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisCech
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.Cr

/-!
# The Brauer group of a quasi-algebraically closed field

For a quasi-algebraically closed (`C₁`) field `K` the cohomological Brauer group
`H²(Spec(K)_ét, 𝔾ₘ)` vanishes.

The proof is the Čech computation of `H²` in low degrees. Embedding `𝔾ₘ` into an injective sheaf
`I` with cokernel `Q`, Hilbert 90 over the quasi-compact étale `K`-schemes
(`AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf_of_compactSpace`) makes the Čech
complexes of `𝔾ₘ`, `I` and `Q` on the coverings `Spec M ⟶ Spec K` short exact, so
`H²(𝔾ₘ) = H¹(Q)` vanishes as soon as the second Čech cohomology of `𝔾ₘ` vanishes on enough
coverings (`CategoryTheory.Sheaf.subsingleton_H_two_of_exactAt_cechComplex`). Every covering is
refined by `Spec M ⟶ Spec K` for a finite Galois extension `M / K`, whose Čech complex computes
the group cohomology of `Gal(M/K)` with values in `Mˣ`; its second cohomology vanishes when `K`
is `C₁`, by the crossed product construction
(`AlgebraicGeometry.Scheme.GaloisCech.exactAt_two_cechComplex_gmSheaf`).

## Main statements

- `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`: `H²(Spec(K)_ét, 𝔾ₘ) = 0` for a
  quasi-algebraically closed field `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf AlgebraicGeometry Scheme

/-- **The Brauer group of a `C₁` field vanishes.** The cohomological Brauer group
`H²(Spec(K)_ét, 𝔾ₘ)` of a quasi-algebraically closed field `K` vanishes. -/
theorem IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup (K : Type u) [Field K]
    [IsQuasiAlgClosed K] : Subsingleton (Spec (.of K)).CohomologicalBrauerGroup := by
  refine Sheaf.subsingleton_H_two_of_exactAt_cechComplex GaloisCech.isTerminal
    (fun V ↦ CompactSpace V.left) (Spec (.of K)).gmSheaf ?_ ?_
  · -- Hilbert 90 over quasi-compact étale `K`-schemes
    intro S hS hSF V hV
    cases S
    subst hSF
    exact surjective_app_of_shortExact_gmSheaf_of_compactSpace _ _ _ hS V
  · -- coverings by the spectra of finite Galois extensions
    intro R hR
    obtain ⟨L, _, _, _, f, hf⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology R hR
    have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
    have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
    let F := SeparableClosure L
    have : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
    have : IsSepClosure K F := ⟨inferInstance, inferInstance⟩
    let M := IntermediateField.normalClosure K L F
    have : Algebra.FormallyEtale K M := Algebra.FormallyEtale.of_isSeparable K M
    have : Algebra.Etale K M := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
    let ι : L →ₐ[K] M := IsScalarTower.toAlgHom K L M
    refine ⟨1, GaloisCech.family K M, fun k y ↦ ?_, fun a ↦ ?_, ?_,
      GaloisCech.exactAt_two_cechComplex_gmSheaf⟩
    · have : CompactSpace (MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
          (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))).left :=
        inferInstanceAs (CompactSpace (Spec (.of K)))
      have : QuasiSeparatedSpace (MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
          (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))).left :=
        inferInstanceAs (QuasiSeparatedSpace (Spec (.of K)))
      exact (compactSpace_and_quasiSeparatedSpace_piObj
        (fun l ↦ GaloisCech.family K M (y l)) fun _ ↦
          ⟨inferInstanceAs (CompactSpace (Spec (.of M))),
          inferInstanceAs (QuasiSeparatedSpace (Spec (.of M)))⟩).1
    · have : (GaloisCech.family K M a).hom = etaleSpecMap ι ≫ f :=
        GaloisCech.isTerminal.hom_ext _ _
      rw [this]
      exact R.downward_closed hf _
    · refine (ofArrows_mem_smallEtaleTopology_iff _).2 ?_
      refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨0, ?_⟩
      obtain ⟨z⟩ : Nonempty (Spec (.of M)) := inferInstance
      exact ⟨z, Subsingleton.elim (α := Spec (.of K)) _ _⟩
