/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
import WeilConjectures.AlgebraicGeometry.Morphisms.TraitGenericRootModel
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDenseOpen

/-!
# Standard root charts for a generic Galois cover of a smooth trait family

## References

* Stacks Project, Tag 0EYJ, first paragraph
* Tags 0EYG and 0EYH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normalization_iso_of_dense_open_model
    {X Y T : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (q : T ⟶ Y) [IsIntegralHom q] [IsLocallyNoetherian T]
    (hn : ∀ z : T, IsDomain (T.presheaf.stalk z) ∧
      IsIntegrallyClosed (T.presheaf.stalk z))
    (V : T.Opens) (hV : Dense (V : Set T)) [QuasiCompact V.ι]
    (γ : X ≅ V.toScheme) (hγ : γ.hom ≫ V.ι ≫ q = g) :
    ∃ δ : g.normalization ≅ T, δ.hom ≫ q = g.fromNormalization := by
  let := isIso_fromNormalization_denseOpen hn V hV
  let a := g.normalizationDesc (γ.hom ≫ V.ι) q (by simpa using hγ.symm)
  have ha : a ≫ q = g.fromNormalization := Hom.normalizationDesc_comp ..
  have hga : g.toNormalization ≫ a = γ.hom ≫ V.ι :=
    Hom.toNormalization_normalizationDesc ..
  have hb : V.ι = (γ.inv ≫ g.toNormalization) ≫ a := by
    rw [Category.assoc, hga, Iso.inv_hom_id_assoc]
  let b := V.ι.normalizationDesc (γ.inv ≫ g.toNormalization) a hb
  let c := inv V.ι.fromNormalization ≫ b
  have hca : c ≫ a = 𝟙 T := by
    dsimp only [c, b]
    rw [Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  have hcq : c ≫ g.fromNormalization = q := by
    rw [← ha, ← Category.assoc, hca, Category.id_comp]
  have hj : V.ι.toNormalization = V.ι ≫ inv V.ι.fromNormalization := by
    apply (cancel_mono V.ι.fromNormalization).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Hom.toNormalization_fromNormalization]
  have hvc : V.ι ≫ c = γ.inv ≫ g.toNormalization := by
    dsimp only [c]
    rw [← Category.assoc, ← hj, Hom.toNormalization_normalizationDesc]
  have hac : a ≫ c = 𝟙 g.normalization := by
    apply Hom.normalization.hom_ext g _ _ g.fromNormalization
    · rw [← Category.assoc, hga, Category.assoc, hvc, Iso.hom_inv_id_assoc,
        Category.comp_id]
    · rw [Category.assoc, hcq, ha]
    · exact Category.id_comp _
  exact ⟨⟨a, c, hac, hca⟩, ha⟩

/-- Standard tame charts for the normalization of a generic Galois cover over a DVR. -/
theorem GaloisCover.trait_generic_normalization_chart
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A))
    [QuasiCompact d] [QuasiSeparated d] [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : A))
    (W : GaloisCover G (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    IsFinite p.fromNormalization → ∀ x : L,
      ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
        Etale φ ∧ φ y = x ∧
        ∃ (m : ℕ) (f : R) (e : Fin m → ℕ),
          (∀ k, 0 < e k ∧ IsUnit (e k : R)) ∧
          ∃ α : pullback p.fromNormalization φ ≅
            Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) =
              pullback.snd p.fromNormalization φ := by
  dsimp
  intro _ x
  obtain ⟨R, φ, y, hφ, hy, m, f, e, he, hn, V, hV, γ, hγ⟩ :=
    GaloisCover.trait_generic_root_model A K d G hG W x
  let := hφ
  let := W.isFinite
  let p := W.π ≫ pullback.fst d (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap R (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
  let (k : Fin m) : Module.Finite R
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) :=
    (Polynomial.monic_X_pow_sub_C f (ne_of_gt (he k).1)).finite_adjoinRoot
  have : Module.Finite R (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) := inferInstance
  have : IsFinite q := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian d
  let : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian φ
  let : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨δ, hδ⟩ := normalization_iso_of_dense_open_model (pullback.snd p φ) q hn V hV γ hγ
  let α := (asIso (p.normalizationPullback φ)).symm ≪≫ δ
  refine ⟨R, φ, y, hφ, hy, m, f, e, he, α, ?_⟩
  dsimp only [α, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, hδ]
  apply (cancel_epi (p.normalizationPullback φ)).mp
  rw [← Category.assoc, asIso_inv, IsIso.hom_inv_id, Category.id_comp,
    Hom.normalizationPullback_snd]

end AlgebraicGeometry.Scheme
