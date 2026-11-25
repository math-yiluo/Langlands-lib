/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.AbelianPullbackGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLift
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero

/-! # Descent of degree-zero classes of a fixed inverse-image sheaf
Source: Stacks Project, Tag 09YQ, via Tags 0EYL, 04HR, 09YN, and 03S2. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A degree-zero class of a sheaf pulled back from one stage comes from its pullback
at a later stage. No varying coefficient sheaves or colimit of sheaves occurs here.

Source: Stacks Project, Étale Cohomology, Tag 09YQ, degree-zero argument using
Tags 0EYL, 04HR, 09YN and restriction along an étale morphism, Tag 03S2.
(blueprint: lem-weil-pbc-fixed-pullback-degree-zero-descent).

Proof: Identify degree-zero cohomology with sections of the identity étale object
by H.equiv₀. Restrict the inverse scheme diagram to the cofinal upper tail of i.
For an affine étale object over D_i, the affine étale-site colimit theorem 0EYL
and affine-topos equivalence 04HR identify the limit inverse image with the
inverse image from the colimit site. The finite-cover section comparison 09YN
then gives a finite-stage representative. For the identity étale object of a
qcqs stage, choose a finite affine cover and finite affine refinements of its
overlaps. Represent the restrictions at one common stage; equality of their
limit images becomes equality on each affine overlap at a later stage by the
injectivity part of the same section comparison. Directedness supplies a common
later stage for this finite collection. The sheaf condition glues the compatible
local representatives. Unit compatibility of the inverse-image composition
isomorphism identifies its image with the original section. The degree-zero
pullback/unit formula translates this to the equation stated below. An empty
scheme has just the zero section, and the nonempty tail represents it as zero. -/
theorem fixed_pullback_degree_zero_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (y : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) 0) :
    ∃ (j : I) (f : i ⟶ j)
      (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj F) 0),
      cohomologyMap (c.π.app (op j)) _ 0 x =
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
            (c.π.app (op i)) (c.w f.op).symm).hom.app F) 0 y := by
  classical
  let eI := Sheaf.H.equiv₀ ((upperStar AddCommGrpCat.{u + 1}
    (c.π.app (op i))).obj F) terminalIsTerminal
  let g := (Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).inv.app
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) (eI y)
  obtain ⟨e, he⟩ := exists_abelianPullbackGlobalSectionsComparison (D.obj (op i)) F
  have : IsIso (⊤_ (D.obj (op i)).Etale).hom := by
    let e := terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal (@Etale) (D.obj (op i)))
    have : IsIso e.hom.left := inferInstance
    have he : e.hom.left = (⊤_ (D.obj (op i)).Etale).hom := by
      have hw := e.hom.w
      change e.hom.left ≫ 𝟙 (D.obj (op i)) = _ at hw
      exact (Category.comp_id _).symm.trans hw
    rw [← he]
    exact this
  have : QuasiCompact (⊤_ (D.obj (op i)).Etale).hom := inferInstance
  have : QuasiSeparated (⊤_ (D.obj (op i)).Etale).hom := inferInstance
  obtain ⟨a, s, hs⟩ := etaleSetSectionLift D c hc i
    ((sheafForget (D.obj (op i)).smallEtaleTopology).obj F) (⊤_ (D.obj (op i)).Etale)
    (e c.pt (c.π.app (op i)) g)
  let j : I := a.left.unop
  let f : i ⟶ j := a.hom.unop
  let h := (e (D.obj (op j)) (D.map f.op)).symm s
  have hh' := he (D.obj a.left) c.pt (c.π.app a.left) (D.map a.hom)
    (c.π.app (op i)) (c.w a.hom) h
  have eh : (e (D.obj a.left) (D.map a.hom)) h = s :=
    (e (D.obj a.left) (D.map a.hom)).apply_symm_apply s
  rw [eh] at hh'
  have hh : globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (c.π.app (op j))
      ((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj F) h =
      (Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app F) g := by
    have ht := (e c.pt (c.π.app (op i))).injective (hh'.trans hs)
    let α := (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
      (c.π.app (op i)) (c.w f.op).symm).app F
    let β := (Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso α
    have ht' := congrArg (fun z ↦ β.hom z) ht
    change β.hom (β.inv _) = β.hom g at ht'
    rw [Iso.inv_hom_id_apply] at ht'
    exact ht'
  let x := (Sheaf.H.equiv₀ ((upperStar AddCommGrpCat.{u + 1}
    (D.map f.op)).obj F) terminalIsTerminal).symm
    ((Sheaf.ΓNatIsoSheafSections (D.obj (op j)).smallEtaleTopology
      AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app
      ((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj F) h)
  refine ⟨j, f, x, ?_⟩
  rw [cohomologyMap_zero_eq_globalSectionsUpperStarMap]
  apply (Sheaf.H.equiv₀ _ terminalIsTerminal).injective
  rw [AddEquiv.apply_symm_apply]
  dsimp only [Functor.comp_obj, Functor.const_obj_obj]
  erw [← Sheaf.H.equiv₀_naturality
    (hT := terminalIsTerminal (C := c.pt.Etale))
    ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
      (c.π.app (op i)) (c.w f.op).symm).hom.app F) y]
  have hn := ConcreteCategory.congr_hom
    ((Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.naturality
      ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
        (c.π.app (op i)) (c.w f.op).symm).hom.app F)) g
  have hg : (Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology
      AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) g = eI y :=
    Iso.inv_hom_id_apply
      ((Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).app _) (eI y)
  erw [hh]
  simp only [ConcreteCategory.comp_apply] at hn
  erw [hg] at hn
  exact hn

end AlgebraicGeometry.Etale
