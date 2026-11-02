import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientStatement
import Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine quotients pull back along cartesian morphisms: proof -/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open FaithfullyFlatCoalgebraDescent

set_option backward.isDefEq.respectTransparency false in
theorem etaleEquivalenceRelationCartesianAffineQuotient :
    EtaleEquivalenceRelationCartesianAffineQuotientStatement.{u} := by
  intro E E₀ f g ⟨hgt, hpb⟩ hU hU₀ ⟨M₀, q₀, hM₀, hpb₀, hflat, hlfp, hsurj⟩
  have hR₀ : IsAffine E₀.R := IsAffine.of_isPullback hpb₀
  have hR : IsAffine E.R := IsAffine.of_isPullback hpb
  obtain ⟨diag, hdt, hds⟩ := E.refl E.U (𝟙 _)
  obtain ⟨comp, hct, hcs⟩ :=
    E.trans _ (pullback.fst E.s E.t) (pullback.snd E.s E.t) pullback.condition
  have hout : IsPullback (E.t ≫ f) E.s q₀ (f ≫ q₀) := by
    have := hpb.paste_horiz hpb₀
    rwa [hgt] at this
  have hP := isPushout_appTop_of_isPullback hout
  have hP₂ := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback E.s E.t)
  have hφ : q₀.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q₀).mp ⟨hflat, hsurj⟩
  have hw : E.t ≫ f ≫ q₀ = E.s ≫ f ≫ q₀ := by
    rw [← Category.assoc, ← hgt, Category.assoc, hpb₀.w, ← Category.assoc, hpb.w,
      Category.assoc]
  have hmem : ∀ a, f.appTop.hom (q₀.appTop.hom a) ∈
      E.t.appTop.hom.eqLocus E.s.appTop.hom := fun a =>
    congrArg (fun k : E.R ⟶ M₀ => k.appTop.hom a) hw
  have key := isPushout_eqLocus_of_groupoid q₀.appTop.hom hφ f.appTop.hom E.t.appTop.hom
    E.s.appTop.hom diag.appTop.hom (pullback.fst E.s E.t).appTop.hom
    (pullback.snd E.s E.t).appTop.hom comp.appTop.hom hP hP₂
    (congrArg (fun k => k.appTop.hom) hdt) (congrArg (fun k => k.appTop.hom) hds)
    (congrArg (fun k => k.appTop.hom) hct) (congrArg (fun k => k.appTop.hom) hcs) hmem
  -- the affine quotient
  set A : Subring Γ(E.U, ⊤) := E.t.appTop.hom.eqLocus E.s.appTop.hom with hA
  let iA : Γ(M₀, ⊤) →+* A := (f.appTop.hom.comp q₀.appTop.hom).codRestrict _ hmem
  let M : Scheme.{u} := Spec (CommRingCat.of A)
  let h : M ⟶ M₀ := Spec.map (CommRingCat.ofHom iA) ≫ M₀.isoSpec.inv
  let q : E.U ⟶ M := E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A.subtype)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ key
  have hpbU : IsPullback f q q₀ h := by
    refine hsq.of_iso E.U.isoSpec.symm E₀.U.isoSpec.symm (Iso.refl _) M₀.isoSpec.symm ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, q, Iso.inv_hom_id_assoc]
      rfl
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, h]
      rfl
  have hq : E.t ≫ q = E.s ≫ q := by
    simp only [q, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact x.2
  have hfin : IsPullback E.t E.s q q := by
    have H : IsPullback (E.t ≫ f) E.s q₀ (q ≫ h) := by rwa [← hpbU.w]
    exact IsPullback.of_right H hq hpbU
  exact ⟨M, q, inferInstance, hfin,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hpbU hflat,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
      hpbU hlfp,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hpbU hsurj⟩

end Langlands.AlgebraicGeometry
