/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionConeStalkIso
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationRingResidue
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-!
# A germ-compatible constant model on a strict-local fibre

Source: Stacks Project, Tag 0GJR, proof of lemma-locally-acyclic-locally-constant.
(blueprint: lem-weil-pbc-strict-local-constant-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem isConstant_of_strictlyHenselian
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    [Scheme.IsLocallyConstantSheaf F] : F.IsConstant (Spec (.of R)).smallEtaleTopology := by
  have : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} :=
    inferInstanceAs (Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale))
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint R)
  have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨σ, hσ⟩ := Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing (𝒰.f i) y hy
  have : ((upperStar AddCommGrpCat.{u + 1} (𝒰.f i)).obj F).IsConstant
      (𝒰.X i).smallEtaleTopology :=
    (Scheme.isConstant_over_iff_upperStar AddCommGrpCat.{u + 1}
      (𝒰.etalePrecoverageToEtale i) F).1 (h𝒰 i)
  have : ((upperStar AddCommGrpCat.{u + 1} σ).obj
      ((upperStar AddCommGrpCat.{u + 1} (𝒰.f i)).obj F)).IsConstant
      (Spec (.of R)).smallEtaleTopology :=
    Sheaf.IsConstant.upperStar AddCommGrpCat.{u + 1} σ _
  let e : ((upperStar AddCommGrpCat.{u + 1} σ).obj
      ((upperStar AddCommGrpCat.{u + 1} (𝒰.f i)).obj F)) ≅ F :=
    ((upperStarComp AddCommGrpCat.{u + 1} σ (𝒰.f i)).app F).symm ≪≫
      eqToIso (congrArg (fun h ↦ (upperStar AddCommGrpCat.{u + 1} h).obj F) hσ) ≪≫
      (upperStarId AddCommGrpCat.{u + 1} (Spec (.of R))).app F
  exact Sheaf.isConstant_congr _ e

private theorem constantSheaf_counit_isIso
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    [F.IsConstant (Spec (.of R)).smallEtaleTopology] :
    IsIso ((constantSheafΓAdj (Spec (.of R)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).counit.app F) := by
  let J := (Spec (.of R)).smallEtaleTopology
  let adj := constantSheafΓAdj J AddCommGrpCat.{u + 1}
  let adj' := constantSheafAdj J AddCommGrpCat.{u + 1} (Scheme.isTerminalEtaleTerminal R)
  have hu (N : AddCommGrpCat.{u + 1}) : IsIso (adj'.unit.app N) := by
    have hb := Scheme.bijective_toSheafify_app_of_isStrictlyHenselianLocalRing R
      ((Functor.const _).obj N)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : IsIso adj'.unit := NatIso.isIso_of_isIso_app _
  let ff := adj'.fullyFaithfulLOfIsIsoUnit
  have : (constantSheaf J AddCommGrpCat.{u + 1}).Full := ff.full
  have : (constantSheaf J AddCommGrpCat.{u + 1}).Faithful := ff.faithful
  exact (adj.isIso_counit_app_iff_mem_essImage).2 F.mem_essImage_of_isConstant

private theorem globalSectionsUpperStarMap_eq
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app _ := by
  let e := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  change _ = _ ≫ e.hom.app _ ≫ _ ≫ _
  rw [e.hom.naturality_assoc]
  rfl

private theorem globalSectionsUpperStarMap_naturality
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ F') :
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStar AddCommGrpCat.{u + 1} g).map a) =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map a ≫
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F' := by
  rw [globalSectionsUpperStarMap_eq, globalSectionsUpperStarMap_eq]
  simp only [Category.assoc]
  rw [← (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  congr 1
  exact congrArg (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality a).symm

private theorem constantSection_pullback
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (N : AddCommGrpCat.{u + 1}) :
    (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app N ≫
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N) ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app N) =
      (constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app N := by
  let adjY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let e := lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app _)).1
  simp only [Category.assoc]
  rw [(Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality]
  simp only [globalSectionsUpperStarMap, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Sheaf.ΓNatIsoSheafSections]
  have hY := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}) adjY N
  have hZ := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}) adjZ N
  simp only [← Category.assoc]
  rw [hY, hZ]
  exact Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ N

/-- A locally constant sheaf on a strict-local fibre is the constant sheaf on its
original geometric stalk, with the canonical alpha map equal to constant sections.
Source: Stacks Project, Tag 0GJR, proof of lemma-locally-acyclic-locally-constant.
(blueprint: lem-weil-pbc-strict-local-constant-comparison).

Proof: pull the locally constant sheaf back to the strict henselization T. A
trivializing etale cover has a point above its closed point; strict henselianity
provides a section of this member. Pulling its constant trivialization back along the
section proves constancy on T. Sheafification of a constant presheaf does not change
its value on T, so the constant-sheaf functor on T is fully faithful. Its counit is
therefore an isomorphism on every constant sheaf. The canonical germ restriction r
identifies the original geometric stalk M with sections of the pullback F. Thus
C(r) followed by the counit gives an isomorphism C(M) to F. The adjunction triangle
identifies the induced map on sections, preceded by the constant-section unit, with r.
Pull this isomorphism back to the fibre. Naturality of the sections pullback map and
the unit identities for the constant-sheaf adjunctions show that constant sections
pull back to constant sections. Finally the inverse-image composition isomorphism
is the one in localAcyclicityAlpha, giving the asserted equality. -/
theorem exists_strictLocalConstantComparison
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Scheme.IsLocallyConstantSheaf G] :
    ∃ e : (constantSheaf (localAcyclicityFiber f x t).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj ((Scheme.pointSmallEtale x).sheafFiber.obj G) ≅
      (upperStar AddCommGrpCat.{u + 1}
        (pullback.fst (localAcyclicityStrictMap f x) t ≫
          Scheme.strictHenselizationStructuralMap x)).obj G,
      localAcyclicityAlpha f x t G =
        (constantSheafΓAdj (localAcyclicityFiber f x t).smallEtaleTopology
          AddCommGrpCat.{u + 1}).unit.app _ ≫
        (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology
          AddCommGrpCat.{u + 1}).map e.hom := by
  classical
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure x
  let := hlocal
  let := hstrict
  let T := Scheme.strictHenselizationScheme x
  let j := Scheme.strictHenselizationStructuralMap x
  let V := localAcyclicityFiber f x t
  let p : V ⟶ T := pullback.fst (localAcyclicityStrictMap f x) t
  let F := (upperStar AddCommGrpCat.{u + 1} j).obj G
  let M := (Scheme.pointSmallEtale x).sheafFiber.obj G
  let C := constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let ΓV := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let adj := constantSheafΓAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Scheme.IsLocallyConstantSheaf F :=
    Scheme.IsLocallyConstantSheaf.upperStar j G
  have : F.IsConstant (Spec (.of (Scheme.strictHenselizationRing x))).smallEtaleTopology :=
    isConstant_of_strictlyHenselian (R := Scheme.strictHenselizationRing x) F
  have : IsIso (adj.counit.app F) :=
    constantSheaf_counit_isIso (R := Scheme.strictHenselizationRing x) F
  let r := Classical.choose ((strictLocalSectionCone x).existsUnique_restriction G)
  have hr : (strictLocalSectionCone x).IsRestriction G r :=
    (Classical.choose_spec ((strictLocalSectionCone x).existsUnique_restriction G)).1
  have : IsIso r := by
    let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom.toAlgebra
    obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
      strictHenselizationRingResidue x rfl
    let := hlocal
    let y := Spec.map (CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing x))))
    have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing x) := by
      rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
      change PrimeSpectrum.comap
        ((((IntermediateField.val
          (separableClosure (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
            σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing x)))
        (IsLocalRing.closedPoint Ω) = _
      rw [PrimeSpectrum.comap_comp]
      exact IsLocalRing.PrimeSpectrum.comap_residue _ _
    refine (strictLocalSectionCone x).isIso_restriction y hbase ?_
      G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
    intro i
    let n := (equivSmallModel.{u}
      (Scheme.strictHenselizationNeighbourhoods x)).inverse.obj i
    change y ≫ (strictLocalNeighbourhoodSection x i).left ≫
      pullback.fst ((Scheme.AffineEtale.Spec X).obj n.1).hom
        (Scheme.strictHenselizationStructuralMap x) = n.2.left
    dsimp only [n]
    simp only [strictLocalNeighbourhoodSection,
      MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
    simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i
  let e₀ : C.obj M ≅ F := C.mapIso (asIso r) ≪≫ asIso (adj.counit.app F)
  have he₀ : adj.unit.app M ≫ Γ.map e₀.hom = r := by
    change adj.unit.app M ≫ Γ.map (C.map r ≫ adj.counit.app F) = r
    exact (adj.homEquiv M F).apply_symm_apply r
  let k := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} p).app M
  let b := (upperStarComp AddCommGrpCat.{u + 1} p j).app G
  let e : (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ≅
      (upperStar AddCommGrpCat.{u + 1} (p ≫ j)).obj G :=
    k.symm ≪≫ (upperStar AddCommGrpCat.{u + 1} p).mapIso e₀ ≪≫ b.symm
  refine ⟨e, ?_⟩
  change r ≫ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} p F ≫ ΓV.map b.inv =
    (constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app M ≫
      ΓV.map e.hom
  have hk := constantSection_pullback p M
  change adj.unit.app M ≫
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} p (C.obj M) ≫ ΓV.map k.hom = _ at hk
  rw [← hk]
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hcancel := (ΓV.mapIso k).hom_inv_id_assoc
    (ΓV.map ((upperStar AddCommGrpCat.{u + 1} p).map e₀.hom) ≫ ΓV.map b.inv)
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at hcancel
  rw [hcancel]
  rw [← Category.assoc (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} p (C.obj M))
    (ΓV.map ((upperStar AddCommGrpCat.{u + 1} p).map e₀.hom)) (ΓV.map b.inv)]
  rw [globalSectionsUpperStarMap_naturality p e₀.hom]
  simp only [← Category.assoc]
  rw [he₀]

end AlgebraicGeometry.Etale
