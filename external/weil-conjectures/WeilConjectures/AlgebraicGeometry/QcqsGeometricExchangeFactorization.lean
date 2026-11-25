/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.StrictHenselizationRingResidue
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # The degree-zero exchange factorization through strict-local sections

Source: Stacks Project, Tags 03Q9, 03Q1 and 0A3U.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Global sections to the identity geometric stalk on the spectrum of a closed field.
This is the global-section identification followed by the identity-neighbourhood germ.
Source: Stacks Project, Tag 03QO.
(auxiliary; not a blueprint node). -/
noncomputable def geometricPointGlobalGerm
    (Λ : Type (u + 1)) [CommRing Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj G ⟶
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj G :=
  (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app G ≫
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)) G.obj

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a qcqs morphism, exchange on the identity geometric stalk factors through
sections over the strict henselization and restriction to the given geometric fibre.
There is no properness hypothesis and no invertibility claim for the fibre restriction.
Source: Stacks Project, Tags 03Q9, 03Q1 and 0A3U
(auxiliary; not a blueprint node).

Proof: the pointed affine-neighbourhood colimit constructs the strict-local ring and
its distinguished map from Spec Ω. Its maximal ideal is the kernel of the residue map,
so this is its geometric closed point. The neighbourhood maps show that its composite
with the structural morphism is s. Form the pullback with X; the universal property
provides q and its cartesian square. The qcqs section-continuity comparison (03Q9)
identifies the direct-image stalk with global sections on this pullback. Forgetting
modules commutes with the filtered colimit and the inverse-image constructions, so
this bijective comparison is a module isomorphism. On an affine representative it is
adjunction unit followed by restriction along the corresponding limit leg.
The inverse-image stalk formula (03Q1) identifies the source stalk of exchange with
this direct-image stalk. Expand exchange as unit, square comparison and counit.
On every representative the result restricts its section to the same pointed fibre.
The upperStarComp inverse identifies the iterated inverse image with g' inverse image;
the lowerStar global-section comparison and the terminal germ give the target stalk.
The colimit's jointly epimorphic germs give the displayed equality. This proves only
the factorization: the restriction to the geometric closed fibre need not be invertible
without properness, and is handled separately. -/
theorem qcqs_geometricExchange_factorization
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let R := Scheme.strictHenselizationRing s
    let ρ := Scheme.strictHenselizationStructuralMap s
    let Z := pullback f ρ
    let p := pullback.fst f ρ
    let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
    ∃ (_ : IsLocalRing R), IsStrictlyHenselianLocalRing R ∧
      ∃ (t : Spec (.of Ω) ⟶ Spec R) (q : X' ⟶ Z),
        t default = IsLocalRing.closedPoint R ∧
        IsPullback q f' (pullback.snd f ρ) t ∧
        ∃ (hq : q ≫ p = g')
          (e : (Scheme.pointSmallEtale ((𝟙 (Spec (.of Ω))) ≫ s)).sheafFiber.obj
              ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
            (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj H),
          (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
              ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
            (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
              (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
            e.hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
            (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) q p g' hq.symm).inv.app F) ≫
            (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
            geometricPointGlobalGerm Λ Ω
              ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
                ((upperStar (ModuleCat.{u + 1} Λ) g').obj F))  := by
  classical
  dsimp only
  let : Algebra (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
    strictHenselizationRingResidue s rfl
  let := hlocal
  let t := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
  have ht : t default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  have htbase : t ≫ Scheme.strictHenselizationStructuralMap s = s := hbase
  let q := pullback.lift g' (f' ≫ t)
    (sq.w.trans (by rw [Category.assoc, htbase]))
  have hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g' :=
    pullback.lift_fst _ _ _
  have hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hcart : IsPullback q f'
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) t := by
    apply IsPullback.of_right (s := ?_) hqt (IsPullback.of_hasPullback _ _)
    simpa only [hq, htbase] using sq
  refine ⟨hlocal, hstrict, t, q, ht, hcart, hq, ?_⟩
  obtain ⟨eFull, heFull⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  let ps := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let pb := pullback.fst f (Scheme.strictLocalizationToBase s)
  let τ := pullback.map f (Scheme.strictHenselizationStructuralMap s)
    f (Scheme.strictLocalizationToBase s) (𝟙 X)
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 Y)
    (by simp) (by simpa using (Scheme.smallStrictLocalization_toBase s).symm)
  have : IsIso τ := by dsimp [τ]; infer_instance
  have hp : ps = τ ≫ pb := by simp [τ, ps, pb]
  let eΓ := globalSectionsUpperStarIso (ModuleCat.{u + 1} Λ) τ
    ((upperStar (ModuleCat.{u + 1} Λ) pb).obj F) ≪≫
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).mapIso
      (((upperStarComp (ModuleCat.{u + 1} Λ) τ pb ps hp).app F).symm)
  let e₀ := eFull ≪≫ eΓ
  have he₀ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ e₀.hom =
      unitSectionRestriction Λ ps F
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
        ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j)
        (by
          change _ ≫ pullback.snd _ f =
            pullback.fst f (Scheme.strictHenselizationStructuralMap s)
          simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd]) := by
    have hj := heFull j
    have hu : qcqsStrictLocalSectionRestriction Λ f s F j =
        unitSectionRestriction Λ pb F
          (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
          ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
            Scheme.strictHenselizationBaseChangeMap f s j)
          (by
            change _ ≫ pullback.snd _ f = pullback.fst f (Scheme.strictLocalizationToBase s)
            simp [Scheme.strictHenselizationBaseChangeMap, Category.assoc]) := by rfl
    rw [hu] at hj
    simp only [e₀, Iso.trans_hom]
    rw [reassoc_of% hj]
    change unitSectionRestriction Λ pb F _ _ _ ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) τ _ ≫
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) τ pb ps hp).inv.app F) = _
    rw [unitSectionRestriction_comp]
    congr 1
    simp only [Scheme.smallStrictHenselizationBaseChangeMap]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [τ, Category.assoc]
  let e : (Scheme.pointSmallEtale ((𝟙 (Spec (.of Ω))) ≫ s)).sheafFiber.obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) :=
    (eqToIso (by rw [Category.id_comp])) ≪≫ e₀
  refine ⟨e, ?_⟩
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let e := geometricPointSourceStalkIso Λ s P
  let r := globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F)
  let b := (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
  change _ = e.hom ≫ e₀.hom ≫ r ≫ b
  apply (Iso.inv_comp_eq e).1
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  have : N.Initial := (Scheme.strictHenselization_properties s).1
  let c := ((Scheme.pointSmallEtale s).presheafFiberCocone P.obj).whisker N.op
  let hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P.obj)
  apply hc.hom_ext
  intro j
  change (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫
    (e.inv ≫ _) = (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫ (e₀.hom ≫ r ≫ b)
  have he := exchange_pointed_representative Λ sq.toCommSq F
    ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1)
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2
  let V := (Scheme.AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1
  let v := ((equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let l := (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
    Scheme.smallStrictHenselizationBaseChangeMap f s j.unop
  have hl : l ≫ (f.Etale.obj V).hom = p := by
    change l ≫ pullback.snd _ f = p
    simp only [l, p, Category.assoc,
      Scheme.smallStrictHenselizationBaseChangeMap_snd, pullbackSymmetry_hom_comp_snd]
  have hr := unitSectionRestriction_comp Λ q p g' hq.symm F (f.Etale.obj V) l hl
  have hg : etaleSectionGraph g' (f.Etale.obj V) (q ≫ l)
      (by rw [Category.assoc, hl, ← hq]) = geometricFibreSectionLift sq.toCommSq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [etaleSectionGraph, geometricFibreSectionLift,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, pullback.lift_fst]
      apply pullback.hom_ext
      · simp only [l, Category.assoc, pullback.lift_fst]
        rw [Scheme.smallStrictHenselizationBaseChangeMap_fst]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
        rw [hqt]
        simp only [Category.assoc]
        rw [← Scheme.isoSpec_Spec_inv, hpoint j.unop]
      · simp only [pullback.lift_snd]
        change (q ≫ l) ≫ (f.Etale.obj V).hom = g'
        rw [Category.assoc, hl, hq]
    · exact (etaleSectionGraph g' (f.Etale.obj V) (q ≫ l)
        (by rw [Category.assoc, hl, ← hq])).w.trans
        (geometricFibreSectionLift sq.toCommSq V v).w.symm
  have heq : unitSectionRestriction Λ g' F (f.Etale.obj V) (q ≫ l)
      (by rw [Category.assoc, hl, ← hq]) =
      geometricFibreSectionRestriction Λ sq.toCommSq F V v ≫
        (Sheaf.ΓNatIsoSheafSections _ _
          (IsTerminal.isTerminalOfObj
            (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
            (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by
    unfold unitSectionRestriction
    rw [hg]
    rfl
  have hr := hr.trans heq
  have h := congrArg (fun k ↦ k ≫ r ≫ b) (he₀ j.unop)
  simpa only [r, b, e, P, N, Scheme.strictHenselizationAffineInclusion,
    Functor.comp_obj, Functor.op_obj, ObjectProperty.ι, ObjectProperty.lift,
    Functor.Elements.precomp, inducedFunctor, Functor.elementsMk, Category.assoc] using
    (he.trans (congrArg (fun k ↦ k ≫ b) hr).symm).trans h.symm

end AlgebraicGeometry.Etale
