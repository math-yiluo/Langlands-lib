/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedTwistAffineFrames
import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart

/-! # Existence of the ordered global twist line

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-line).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The chosen boundary adjunction is the section-normalized tensor adjunction. -/
private theorem boundary_adjunction_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g) =
      Scheme.Modules.tensorPullbackSectionAdjunction g :=
  (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g).unique
    (fun M U m ↦ Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g)
      M (op U) m)
    (Classical.choose_spec (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g)).1

set_option linter.unusedVariables false in
/-- The local normalized affine comparisons glue to a global line isomorphism.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-line).

Proof: on each affine base chart, use the supplied polynomial and normalized
Proj comparison to identify the standard degree-one frame with the chart frame
of the tautological quotient.  The ratio on overlaps is the ratio of the same
homogeneous generators, so the local isomorphisms satisfy the cocycle condition.
Glue them, together with their local inverses, by the sheaf gluing theorem.
The resulting global map is an isomorphism, and its restrictions retain the
normalized coordinate equations used to glue it.  The argument also covers the
zero-dimensional and empty-chart cases.
-/
theorem exists_ordered_twist_line (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line,
    ∀ V : S.affineOpens, ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        ((Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient) =
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        (((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom) := by
  classical
  let X := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let f := (eRel ≪≫ θ).hom
  let P := (Scheme.Modules.pullback f).obj
    (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1)
  let σ := (Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv E D.line D.quotient
  let q (i : ULift.{u} (Fin (r + 1))) : Γ(D.line, ⊤) :=
    σ.app ⊤ (b.hom.app ⊤ ((SheafOfModules.ιFree
      (R := S.ringCatSheaf) i).val.app (op ⊤) (1 : Γ(S, ⊤))))
  let s (i : ULift.{u} (Fin (r + 1))) : Γ(P, ⊤) :=
    Scheme.Modules.pullbackSection f (ProjectiveSpace.twistOneSection _ S i)
  let U (i : S.affineOpens × ULift.{u} (Fin (r + 1))) : X.Opens :=
    p ⁻¹ᵁ i.1.1 ⊓ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i.2
  have hU : (⨆ i, U i) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top S).ge (Set.mem_univ (p x)))
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen (ULift.{u} (Fin (r + 1))) S).ge
        (Set.mem_univ (f x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(V, i), hV, hi⟩
  have hs (i : S.affineOpens × ULift.{u} (Fin (r + 1))) :
      Scheme.Modules.IsFreeGenerator
        (P.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i.2)) := by
    have h := (ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection f i.2).map
      (inf_le_right : U i ≤ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i.2)
    rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at h
    convert! h using 1
  have hq (i : S.affineOpens × ULift.{u} (Fin (r + 1))) :
      Scheme.Modules.IsFreeGenerator
        (D.line.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (q i.2)) :=
    (ordered_quotient_affine_frames S E D r b eRel θ i.1
      (hAffine i.1) (hθAffine i.1) i.2).1
  have ratios (i j : S.affineOpens × ULift.{u} (Fin (r + 1))) :
      ∃ c : Γ(X, U j),
        P.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s i.2) =
          c • P.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s j.2) ∧
        D.line.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (q i.2) =
          c • D.line.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (q j.2) := by
    refine ⟨X.presheaf.map (homOfLE (inf_le_right :
      U j ≤ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S j.2)).op
        (f.app (ProjectiveSpace.standardOpen _ S j.2)
          (ProjectiveSpace.coordRatio _ S j.2 i.2)), ?_, ?_⟩
    · exact Scheme.Modules.presheaf_map_homOfLE_eq_smul _ inf_le_right
        (ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul f i.2 j.2)
    · exact (ordered_quotient_affine_frames S E D r b eRel θ j.1
        (hAffine j.1) (hθAffine j.1) j.2).2 i.2
  have hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a c : Γ(X, W)),
      a • P.presheaf.map (homOfLE hi).op
          (P.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i.2)) =
        c • P.presheaf.map (homOfLE hj).op
          (P.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s j.2)) →
      a • D.line.presheaf.map (homOfLE hi).op
          (D.line.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (q i.2)) =
        c • D.line.presheaf.map (homOfLE hj).op
          (D.line.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (q j.2)) := by
    intro i j W hi hj a c hac
    obtain ⟨d, hdP, hdQ⟩ := ratios i j
    have hdP' := Scheme.Modules.presheaf_map_homOfLE_eq_smul _ hj hdP
    have hdQ' := Scheme.Modules.presheaf_map_homOfLE_eq_smul _ hj hdQ
    simp only [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hac ⊢
    rw [hdP', smul_smul] at hac
    have hsj := (hs j).map hj
    simp only [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hsj
    have heq := hsj.smul_left_injective hac
    rw [hdQ', smul_smul, heq]
  let T := Scheme.Modules.isoOfIsFreeGenerator hU hs hq hc
  have key (k : ULift.{u} (Fin (r + 1))) : T.hom.app ⊤ (s k) = q k := by
    refine (Scheme.Modules.isGlueValue_glueHom_app hU hs hc (s k)).unique hU hs ?_
    intro j W hW hWj a ha
    obtain ⟨c, hcP, hcQ⟩ := ratios (j.1, k) j
    have hcP' := Scheme.Modules.presheaf_map_homOfLE_eq_smul _ hWj hcP
    have hcQ' := Scheme.Modules.presheaf_map_homOfLE_eq_smul _ hWj hcQ
    simp only [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at ha hcP' hcQ' ⊢
    rw [hcP'] at ha
    have hsj := (hs j).map hWj
    simp only [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hsj
    rw [hcQ', hsj.smul_left_injective ha]
  let adj := Scheme.Modules.tensorPullbackSectionAdjunction p
  let u := (adj.unit.app (Scheme.Modules.unit S)).app ⊤ (1 : Γ(S, ⊤))
  have hbd : Scheme.Modules.boundaryPullbackComparison p =
      adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction p) := by
    rw [Scheme.Modules.boundaryPullbackComparison, boundary_adjunction_eq]
  have hu : ((Scheme.Modules.boundaryPullbackComparison p).app (Scheme.Modules.unit S) ≪≫
      Scheme.Modules.pullbackObjUnitIso p).hom.app ⊤ u = (1 : Γ(X, ⊤)) := by
    have hb := congrArg (fun φ ↦ φ.app ⊤ (1 : Γ(S, ⊤)))
      (Adjunction.unit_leftAdjointUniq_hom_app adj
        (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.unit S))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
      ConcreteCategory.comp_apply] at hb
    have h2 := Scheme.Modules.pullbackObjUnitIso_hom_app_pullbackSection p (U := ⊤)
      (1 : Γ(S, ⊤))
    refine Eq.trans ?_ (h2.trans ?_)
    · simp only [Iso.trans_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app,
        ConcreteCategory.comp_apply, hbd]
      exact congrArg _ hb
    · exact map_one (p.app ⊤).hom
  let t := (Scheme.Modules.boundaryPullbackComparison f).app _ ≪≫ T
  refine ⟨t, fun V i ↦ congrArg _ ?_⟩
  rw [← Iso.inv_comp_eq]
  apply Scheme.Modules.unit_hom_ext
  refine (?_ : _ = q i).trans ?_
  · rw [← hu, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id_assoc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    have hnat := congrArg (fun ψ ↦ ψ.app ⊤ (1 : Γ(S, ⊤)))
      (adj.unit.naturality (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom))
    simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
      Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply] at hnat
    simp only [q, σ, Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
      Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply]
    exact congrArg _ hnat.symm
  · rw [← key i]
    rw [show t.hom = (Scheme.Modules.boundaryPullbackComparison f).hom.app _ ≫ T.hom from rfl]
    simp only [Iso.trans_inv, Iso.app_inv, Category.assoc]
    rw [(Scheme.Modules.boundaryPullbackComparison f).hom.naturality_assoc,
      Iso.inv_hom_id_app_assoc, ← Category.assoc, Scheme.Modules.Hom.comp_app _ T.hom,
      ConcreteCategory.comp_apply]
    congr 1
    exact (congrArg (Scheme.Modules.pullbackSection f)
      (ProjectiveSpace.coordinateSection_app_top_one _ S i).symm).trans
      (Scheme.Modules.pullbackSection_app_one f _)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
