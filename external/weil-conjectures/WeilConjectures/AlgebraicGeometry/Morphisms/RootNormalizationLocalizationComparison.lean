/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.RootCoverNormalizationCartesian
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineLocalizationPullbackStalk

/-! # Root normalization after principal-prime localization

## References

* Stacks Project, Tag 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem adjoinRoot_localization_of_map_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) (F : Polynomial R) (F0 : Polynomial S)
    (hF0 : F0 = F.map (algebraMap R S)) (hd : F0 ∣ F.map (algebraMap R S))
    (h : let γ := AdjoinRoot.map (algebraMap R S) F (F.map (algebraMap R S)) dvd_rfl
      let := γ.toAlgebra
      IsLocalization (M.map (AdjoinRoot.of F)) (AdjoinRoot (F.map (algebraMap R S)))) :
    let γ := AdjoinRoot.map (algebraMap R S) F F0 hd
    let := γ.toAlgebra
    IsLocalization (M.map (AdjoinRoot.of F)) (AdjoinRoot F0) := by
  subst F0
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- The geometric root-normalization comparison over an already constructed
principal-prime localization. The DVR and its uniformizer are fixed data; the generic
map to U and its pulled-back cover are supplied separately. -/
theorem root_normalization_localization_comparison
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (H B : CommRingCat.{u}) [Algebra H B] (g : H)
    [(Ideal.span {g}).IsPrime] [IsLocalization.AtPrime B (Ideal.span {g})]
    [IsDomain B] [IsDiscreteValuationRing B]
    (hpi : Irreducible (algebraMap H B g))
    (ψ : Spec H ⟶ L)
    (k : Spec (CommRingCat.of (FractionRing B)) ⟶ U)
    (hk : k ≫ i = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ)
    (hbranch : IsPullback k (𝟙 _) i
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ))
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (ρ : T.P ⟶ W.P) (hT : IsPullback ρ T.π W.π k)
    (hrootloc :
      let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
      let F0 := F.map (algebraMap H B)
      let γ := AdjoinRoot.map (algebraMap H B) F F0 dvd_rfl
      let := γ.toAlgebra
      IsLocalization ((Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)) (AdjoinRoot F0)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      (Ideal.span {AdjoinRoot.root
                    ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)}).comap
        (algebraMap H A) = Ideal.span {g} →
      let C := a.normalization.presheaf.stalk x
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      let pi := algebraMap H B g
      let A0 := AdjoinRoot
        ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
      let N0 := Spec (CommRingCat.of A0)
      let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
      let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
      let a0 := pullback.snd (T.π ≫ j0) q0
      ∃ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
        letI := hqc
        letI := hqs
        IsFinite a0.fromNormalization ∧
        ∃ (x0 : a0.normalization),
          (a0.fromNormalization x0).asIdeal = Ideal.span
            {AdjoinRoot.root
              ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} ∧
          ∃ (e : a0.normalization.presheaf.stalk x0 ≃+* C),
            e ((a0.fromNormalization.stalkMap x0).hom
              (AlgebraicGeometry.StructureSheaf.toStalk A0 (a0.fromNormalization x0)
                (AdjoinRoot.root
                  ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))) =
              (a.fromNormalization.stalkMap x).hom t := by
  classical
  intro A N q V hN
  let := hN
  intro _ p hp
  let := hp
  intro _ a hep hfin x hx hcontract C t pi A0 N0 q0 j0 a0
  let := T.isFinite
  have : IsAffineHom j0 := by dsimp only [j0]; infer_instance
  have : IsAffineHom (T.π ≫ j0) := by infer_instance
  have hqc : QuasiCompact a0 := by dsimp only [a0, j0, q0]; infer_instance
  have hqs : QuasiSeparated a0 := by dsimp only [a0, j0, q0]; infer_instance
  let := hqc
  let := hqs
  obtain ⟨c, hsq⟩ := root_cover_normalization_cartesian
    i G W H B g hpi ψ k hk hbranch T ρ hT hrootloc hN hp hep hqc hqs
  have hfinite : IsFinite a0.fromNormalization :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin
  let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let F0 := (Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi
  let γ : A →+* A0 := AdjoinRoot.map (algebraMap H B) F F0 (by simp [F, F0, pi])
  let : Algebra A A0 := γ.toAlgebra
  let M := (Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)
  have hloc : IsLocalization M A0 :=
    adjoinRoot_localization_of_map_eq (Ideal.span {g}).primeCompl F F0
      (by simp [F, F0, pi]) (by simp [F, F0, pi]) hrootloc
  let := hloc
  have hdis : Disjoint (M : Set A) ((a.fromNormalization x).asIdeal : Set A) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨r, hr, rfl⟩ hz
    apply hr
    rw [← hcontract]
    change AdjoinRoot.of F r ∈ Ideal.span {AdjoinRoot.root F}
    rwa [hx] at hz
  obtain ⟨x0, hcx, e, he⟩ := exists_lift_stalkEquiv_of_isLocalization
    (CommRingCat.of A) (CommRingCat.of A0) M c a0.fromNormalization
    a.fromNormalization hsq x hdis
  refine ⟨hqc, hqs, hfinite, x0, ?_, e, ?_⟩
  · have hpoint : (Spec.map (CommRingCat.ofHom γ) (a0.fromNormalization x0)).asIdeal =
        (a.fromNormalization x).asIdeal := by
      have hw := congrArg (fun f ↦ f x0) hsq.w
      simpa only [Hom.comp_apply, hcx] using congrArg PrimeSpectrum.asIdeal hw.symm
    change (a0.fromNormalization x0).asIdeal = Ideal.span {AdjoinRoot.root F0}
    have hm := IsLocalization.map_under M A0 (a0.fromNormalization x0).asIdeal
    change Ideal.map γ (Ideal.comap γ (a0.fromNormalization x0).asIdeal) =
      (a0.fromNormalization x0).asIdeal at hm
    change Ideal.comap γ (a0.fromNormalization x0).asIdeal =
      (a.fromNormalization x).asIdeal at hpoint
    rw [← hm, hpoint, hx, Ideal.map_span, Set.image_singleton]
    change Ideal.span {γ (AdjoinRoot.root F)} = Ideal.span {AdjoinRoot.root F0}
    rw [show γ (AdjoinRoot.root F) = AdjoinRoot.root F0 from AdjoinRoot.map_root ..]
  · change e ((a0.fromNormalization.stalkMap x0).hom
      (StructureSheaf.toStalk A0 (a0.fromNormalization x0) (AdjoinRoot.root F0))) =
        (a.fromNormalization.stalkMap x).hom
          (StructureSheaf.toStalk A (a.fromNormalization x) (AdjoinRoot.root F))
    have hroot : γ (AdjoinRoot.root F) = AdjoinRoot.root F0 := AdjoinRoot.map_root ..
    have he' := he (AdjoinRoot.root F)
    change e ((a0.fromNormalization.stalkMap x0).hom
      (StructureSheaf.toStalk A0 (a0.fromNormalization x0)
        (γ (AdjoinRoot.root F)))) = (a.fromNormalization.stalkMap x).hom t at he'
    exact (congrArg (fun z : A0 ↦ e ((a0.fromNormalization.stalkMap x0).hom
      (StructureSheaf.toStalk A0 (a0.fromNormalization x0) z))) hroot).symm.trans he'

end AlgebraicGeometry.Scheme
