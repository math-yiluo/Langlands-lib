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

import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationAffineLocalization
import WeilConjectures.AlgebraicGeometry.Morphisms.RootCoverGenericPullback

/-! # Cartesian comparison of the root-cover normalizations

## References

* Stacks Project, Tag 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normalization_iso_of_iso_over {X Y T : Scheme.{u}}
    (f : X ⟶ T) (g : Y ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (e : X ≅ Y) (he : e.hom ≫ g = f) :
    ∃ E : f.normalization ≅ g.normalization,
      E.hom ≫ g.fromNormalization = f.fromNormalization := by
  have hi : e.inv ≫ f = g := by rw [← he]; simp
  let a := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp [he])
  let b := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by simp [hi])
  have hab : a ≫ b = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  have hba : b ≫ a = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  exact ⟨⟨a, b, hab, hba⟩, by simp [a]⟩

private theorem spec_sections_localization (R S : CommRingCat.{u})
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    letI := (g.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
    IsLocalization (M.map (ΓSpecIso R).inv.hom) Γ(Spec S, ⊤) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let er := (ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let : Algebra Γ(Spec R, ⊤) S :=
    ((algebraMap R S).comp (ΓSpecIso R).hom.hom).toAlgebra
  have : IsLocalization (M.map er) S :=
    IsLocalization.isLocalization_of_base_ringEquiv M S er
  let : Algebra Γ(Spec R, ⊤) Γ(Spec S, ⊤) :=
    (g.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
  let e : S ≃ₐ[Γ(Spec R, ⊤)] Γ(Spec S, ⊤) :=
    { (ΓSpecIso S).symm.commRingCatIsoToRingEquiv with
      commutes' r := by
        apply (ΓSpecIso S).commRingCatIsoToRingEquiv.injective
        change (ΓSpecIso S).hom ((ΓSpecIso S).inv
            (algebraMap R S ((ΓSpecIso R).hom r))) =
          (ΓSpecIso S).hom ((g.appLE ⊤ ⊤ (by simp)) r)
        rw [Iso.inv_hom_id_apply]
        have he : g.appLE ⊤ ⊤ (by simp) = g.appTop := by simp [Hom.appLE]
        rw [he]
        exact (congrArg (fun k : Γ(Spec R, ⊤) ⟶ S ↦ k r)
          (ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S)))).symm }
  exact IsLocalization.isLocalization_of_algEquiv (M.map er) e

private theorem normalization_cartesian_of_isIso
    {X Y C D : Scheme.{u}} (f : X ⟶ C) (f0 : Y ⟶ D) (g : D ⟶ C)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f0] [QuasiSeparated f0]
    (m : Y ⟶ X) (h : IsPullback m f0 f g)
    [IsIso (f.normalizationPullback g)] :
    ∃ c : f0.normalization ⟶ f.normalization,
      IsPullback c f0.fromNormalization f.fromNormalization g := by
  obtain ⟨e, he⟩ := normalization_iso_of_iso_over f0 (pullback.snd f g)
    h.isoPullback h.isoPullback_hom_snd
  let E := e ≪≫ asIso (f.normalizationPullback g)
  have hE : E.hom ≫ pullback.snd f.fromNormalization g = f0.fromNormalization := by
    simp only [E, Iso.trans_hom, asIso_hom, Category.assoc,
      Hom.normalizationPullback_snd, he]
  refine ⟨E.hom ≫ pullback.fst f.fromNormalization g,
    IsPullback.of_iso_pullback ?_ E rfl hE⟩
  exact ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hE]⟩

set_option linter.unusedVariables false in
/-- The normalization of the DVR root cover is the coefficient-localized normalization. -/
theorem root_cover_normalization_cartesian
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
    Etale p →
    let pi := algebraMap H B g
    let A0 := AdjoinRoot
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
    let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
    let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a0 := pullback.snd (T.π ≫ j0) q0
    let γ := AdjoinRoot.map (algebraMap H B)
      ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi) (by simp [pi])
    ∀ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
      letI := hqc
      letI := hqs
      ∃ c : a0.normalization ⟶ a.normalization,
        IsPullback c a0.fromNormalization a.fromNormalization
          (Spec.map (CommRingCat.ofHom γ)) := by
  dsimp only
  intro hN hp het hqc hqs
  let :=  hN
  let :=  hp
  let :=  hqc
  let :=  hqs
  let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let F0 := (Polynomial.X : Polynomial B) ^ Nat.card G -
    Polynomial.C (algebraMap H B g)
  let γ := AdjoinRoot.map (algebraMap H B) F F0 (by simp [F, F0])
  let :=  γ.toAlgebra
  let M := (Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)
  have hloc : IsLocalization M (AdjoinRoot F0) := by
    have aux (Q : Polynomial B) (hQ : F.map (algebraMap H B) = Q) :
        let δ := AdjoinRoot.map (algebraMap H B) F Q (hQ ▸ dvd_rfl)
        letI := δ.toAlgebra
        IsLocalization M (AdjoinRoot Q) := by
      subst Q
      exact hrootloc
    exact aux F0 (by simp [F, F0])
  let N := Spec (CommRingCat.of (AdjoinRoot F))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H (AdjoinRoot F) g)
  let p := pullback.snd (W.π ≫ i)
    (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H (AdjoinRoot F))) ≫ ψ)
  let a := p ≫ V.ι
  let β := Spec.map (CommRingCat.ofHom γ)
  have hflat : Flat β := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (AdjoinRoot F0) M)
  let :=  hflat
  have hM := spec_sections_localization (CommRingCat.of (AdjoinRoot F))
    (CommRingCat.of (AdjoinRoot F0)) M
  have : IsIso (a.normalizationPullback β) :=
    Hom.isIso_normalizationPullback_affine_localization a β
      (M.map (ΓSpecIso (CommRingCat.of (AdjoinRoot F))).inv.hom) hM
  obtain ⟨m, hm⟩ := root_cover_generic_pullback i G W H B g hpi ψ k hk
    hbranch T ρ hT
  exact normalization_cartesian_of_isIso a _ β m hm

end AlgebraicGeometry.Scheme
