/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteSupportLifting
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionLocalSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenCounitLocalizationDiagram
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Finite support diagrams for the open counit

## References

* Stacks Project, Tags 00WK and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- A section of the pushforward of an open extension has a finite support diagram
coming from a quasi-compact open in the affine test object. The maps `a` and `b` are
homomorphisms of section groups and intertwine the two specified open counits.
Properness is not assumed: quasi-compactness and quasi-separatedness suffice for
this finite-representative step, which makes no surjectivity assertion about either
counit. -/
theorem sfOpenCounit_finiteSupportDiagram {V W T : Scheme.{u}} (p : V ⟶ T)
    [QuasiCompact p] [QuasiSeparated p] (i : W ⟶ T) [IsOpenImmersion i]
    (M : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) (Q : T.ProEt) [IsAffine Q.left] :
    let F := (sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
      proEtaleConstantModuleDirectImage p A).obj M
    let c := (sfIntrinsicExtensionByZeroAdjunction i A).counit.app F
    ∀ y : F.val.obj (op Q),
      ∃ (O : Q.left.Opens) (_ : IsCompact (O : Set Q.left))
        (_ : (O : Set Q.left) ⊆ Q.hom ⁻¹' Set.range i)
        (M₀ : proEtaleRingModules (pullback (pullback.snd p Q.hom) O.ι)
          (proEtaleConstantRing (pullback (pullback.snd p Q.hom) O.ι) A)),
        let F₀ := (sfIntrinsicExtensionByZero
          (pullback.fst (pullback.snd p Q.hom) O.ι) A ⋙
            proEtaleConstantModuleDirectImage (pullback.snd p Q.hom) A).obj M₀
        let c₀ := (sfIntrinsicExtensionByZeroAdjunction O.ι A).counit.app F₀
        ∃ (a : ((sfIntrinsicExtensionByZero O.ι A).obj
            ((sfIntrinsicOpenRestriction O.ι A).obj F₀)).val.obj (op (ProEt.mk (𝟙 Q.left))) →+
              ((sfIntrinsicExtensionByZero i A).obj
                ((sfIntrinsicOpenRestriction i A).obj F)).val.obj (op Q))
          (b : F₀.val.obj (op (ProEt.mk (𝟙 Q.left))) →+ F.val.obj (op Q))
          (y₀ : F₀.val.obj (op (ProEt.mk (𝟙 Q.left)))),
          (∀ x, c.val.app (op Q) (a x) =
            b (c₀.val.app (op (ProEt.mk (𝟙 Q.left))) x)) ∧ b y₀ = y := by
  intro F c y
  classical
  let R := ULift.{u + 1, u} A
  let N := (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} R)
    (pullback.fst p i)).obj ((sfIntrinsicModuleEquivalence (pullback p i) A).inverse.obj M)
  let H := (ProEtale.lowerStar (ModuleCat.{u + 1} R) p).obj N
  let e : (sfIntrinsicModuleEquivalence T A).functor.obj H ≅ F :=
    ((sfIntrinsicDirectImageComparison p A).app N).symm
  let eH : H ≅ (sfIntrinsicModuleEquivalence T A).inverse.obj F :=
    (sfIntrinsicModuleEquivalence T A).unitIso.app H ≪≫
      (sfIntrinsicModuleEquivalence T A).inverse.mapIso e
  let yH := (ProEtale.fixedSectionEquiv R eH (op Q)).symm
    ((sfIntrinsicSectionEquiv A T F (op Q)).symm y)
  let I : Q.left.ProEt := ProEt.mk (𝟙 Q.left)
  let L := MorphismProperty.Over.map ⊤ Q.prop
  let eI : L.obj I ≅ Q :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _).symm
  let pQ : pullback p Q.hom ⟶ Q.left := pullback.snd p Q.hom
  let r := pullback.fst p Q.hom
  let G := (ProEtale.localizationRestriction (ModuleCat.{u + 1} R) r inferInstance).obj N
  have hbc := ProEtale.isIso_localizationRestrictionBaseChangeMap_of_isPullback
    (ModuleCat.{u + 1} R) (IsPullback.of_hasPullback p Q.hom).flip
  let bc := (asIso (ProEtale.localizationRestrictionBaseChangeMap
    (ModuleCat.{u + 1} R) (IsPullback.of_hasPullback p Q.hom).flip.toCommSq)).app N
  let Q₀ := (proEtaleBaseChange pQ).obj I
  let Lr := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale r)
  let s : N.obj.obj (op (Lr.obj Q₀)) := bc.hom.hom.app (op I)
    (H.obj.map eI.hom.op yH)
  have : IsAffine ((𝟭 Scheme).obj Q.left) := inferInstanceAs (IsAffine Q.left)
  have : CompactSpace Q₀.left := by
    change CompactSpace ↥(pullback (𝟙 Q.left) (pullback.snd p Q.hom) : Scheme.{u})
    infer_instance
  have : QuasiSeparatedSpace ↥(pullback p Q.hom : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p Q.hom)
  have : QuasiSeparatedSpace Q₀.left := by
    change QuasiSeparatedSpace ↥(pullback (𝟙 Q.left) (pullback.snd p Q.hom) : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst (𝟙 Q.left) (pullback.snd p Q.hom))
  have hloc := ProEtale.openExtension_localSupport R
    (pullback.fst p i) ((sfIntrinsicModuleEquivalence (pullback p i) A).inverse.obj M)
      (Lr.obj Q₀)
  -- Select witnesses without repeatedly eliminating into the large dependent diagram goal.
  let S := (hloc s).choose
  have hS := (hloc s).choose_spec.1
  have hsupport := (hloc s).choose_spec.2
  let U : Q.left.Opens := Q.hom ⁻¹ᵁ i.opensRange
  have hs : ∀ (Z : V.ProEt) (f : Z ⟶ Lr.obj Q₀), S f →
      Set.range (f.left ≫ Q₀.hom ≫ pQ) ⊆ U ∨ N.obj.map f.op s = 0 := by
    intro Z f hf
    rcases hsupport Z f hf with ⟨g, hg⟩ | hz
    · left
      have hf' : f.left ≫ (Q₀.hom ≫ r) = Z.hom := MorphismProperty.Over.w f
      have hw : (f.left ≫ Q₀.hom ≫ pQ) ≫ Q.hom = g ≫ pullback.snd p i ≫ i := by
        calc
          (f.left ≫ Q₀.hom ≫ pQ) ≫ Q.hom =
              (f.left ≫ (Q₀.hom ≫ r)) ≫ p := by
                simp only [pQ, r, Category.assoc, pullback.condition]
          _ = Z.hom ≫ p := congrArg (fun t ↦ t ≫ p) hf'
          _ = (g ≫ pullback.fst p i) ≫ p := congrArg (fun t ↦ t ≫ p) hg.symm
          _ = g ≫ pullback.snd p i ≫ i := by rw [Category.assoc, pullback.condition]
      rintro _ ⟨z, rfl⟩
      exact ⟨(g ≫ pullback.snd p i) z, congrArg (fun t : Z.left ⟶ T ↦ t z) hw.symm⟩
    · exact Or.inr hz
  have hlift := ProEtale.finiteSupport_lifting R r pQ Q₀ U N s S hS hs
  let O := hlift.choose
  have hOc := hlift.choose_spec.1
  have hOU := hlift.choose_spec.2.1
  let t := hlift.choose_spec.2.2.choose
  have ht := hlift.choose_spec.2.2.choose_spec
  have hO : (O : Set Q.left) ⊆ Q.hom ⁻¹' Set.range i := hOU
  let m₀ := (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} R)
    (pullback.fst pQ O.ι)).obj G
  let M₀ := (sfIntrinsicModuleEquivalence (pullback pQ O.ι) A).functor.obj m₀
  refine ⟨O, hOc, hO, M₀, ?_⟩
  let N₀ := (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} R)
    (pullback.fst pQ O.ι)).obj m₀
  let H₀ := (ProEtale.lowerStar (ModuleCat.{u + 1} R) pQ).obj N₀
  let F₀ := (sfIntrinsicExtensionByZero (pullback.fst pQ O.ι) A ⋙
    proEtaleConstantModuleDirectImage pQ A).obj M₀
  let ex₀ : (sfIntrinsicModuleEquivalence (pullback p Q.hom) A).functor.obj N₀ ≅
      (sfIntrinsicExtensionByZero (pullback.fst pQ O.ι) A).obj M₀ :=
    (sfIntrinsicModuleEquivalence (pullback p Q.hom) A).functor.mapIso
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} R)
        (pullback.fst pQ O.ι)).mapIso
          ((sfIntrinsicModuleEquivalence (pullback pQ O.ι) A).unitIso.app m₀))
  let e₀ : (sfIntrinsicModuleEquivalence Q.left A).functor.obj H₀ ≅ F₀ :=
    ((sfIntrinsicDirectImageComparison pQ A).app N₀).symm ≪≫
      (proEtaleConstantModuleDirectImage pQ A).mapIso ex₀
  let eH₀ : H₀ ≅ (sfIntrinsicModuleEquivalence Q.left A).inverse.obj F₀ :=
    (sfIntrinsicModuleEquivalence Q.left A).unitIso.app H₀ ≪≫
      (sfIntrinsicModuleEquivalence Q.left A).inverse.mapIso e₀
  let β : H₀ ⟶ (ProEtale.localizationRestriction
      (ModuleCat.{u + 1} R) Q.hom Q.prop).obj H :=
    (ProEtale.lowerStar (ModuleCat.{u + 1} R) pQ).map
      ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R)
        (pullback.fst pQ O.ι)).counit.app G) ≫ bc.inv
  let bH : H₀.obj.obj (op I) →+ H.obj.obj (op Q) :=
    (H.obj.map eI.inv.op).hom.toAddMonoidHom.comp (β.hom.app (op I)).hom.toAddMonoidHom
  have hty : bH t = yH := by
    change H.obj.map eI.inv.op (bc.inv.hom.app (op I)
      (((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R)
        (pullback.fst pQ O.ι)).counit.app G).hom.app (op Q₀) t)) = _
    rw [ht]
    change H.obj.map eI.inv.op (bc.inv.hom.app (op I)
      (bc.hom.hom.app (op I) (H.obj.map eI.hom.op yH))) = _
    have hb := congrArg (fun f ↦ f.hom.app (op I) (H.obj.map eI.hom.op yH)) bc.hom_inv_id
    change bc.inv.hom.app (op I) (bc.hom.hom.app (op I) _) = _ at hb
    rw [hb]
    change H.obj.map eI.inv.op (H.obj.map eI.hom.op yH) = _
    rw [← Functor.map_comp_apply, ← op_comp, eI.inv_hom_id, op_id, H.obj.map_id]
    rfl
  have hdiag := ProEtale.openCounit_localization_diagram R i H Q O hO H₀ β
  let aS := hdiag.choose
  have haS := hdiag.choose_spec
  let CH := (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} R) i).obj
    ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} R) i).obj H)
  let aH := (CH.obj.map eI.inv.op).hom.toAddMonoidHom.comp
    (aS.hom.app (op I)).hom.toAddMonoidHom
  have hab (x) :
      ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) i).counit.app H).hom.app
        (op Q) (aH x) =
      bH (((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} R) O.ι).counit.app H₀).hom.app (op I) x) := by
    have h := congrArg (fun f ↦ f.hom.app (op I) x) haS
    have hn := NatTrans.naturality_apply
      ((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} R) i).counit.app H).hom eI.inv.op
          (aS.hom.app (op I) x)
    exact hn.trans (congrArg (H.obj.map eI.inv.op) h)
  have hconj := sfIntrinsicCounit_conjugation A i F H eH (op Q)
  let eC := hconj.choose
  have heC := hconj.choose_spec
  have hconj₀ := sfIntrinsicCounit_conjugation A O.ι F₀ H₀ eH₀ (op I)
  let eC₀ := hconj₀.choose
  have heC₀ := hconj₀.choose_spec
  let z := (ProEtale.fixedSectionEquiv R eH (op Q)).trans
    (sfIntrinsicSectionEquiv A T F (op Q))
  let z₀ := (ProEtale.fixedSectionEquiv R eH₀ (op I)).trans
    (sfIntrinsicSectionEquiv A Q.left F₀ (op I))
  refine ⟨eC.toAddMonoidHom.comp (aH.comp eC₀.symm.toAddMonoidHom),
    z.toAddMonoidHom.comp (bH.comp z₀.symm.toAddMonoidHom), z₀ t, ?_, ?_⟩
  · intro x
    change _ = z (bH (z₀.symm _))
    refine (heC (aH (eC₀.symm x))).trans ?_
    change z _ = z _
    rw [hab]
    have hx := heC₀ (eC₀.symm x)
    change _ = z₀ _ at hx
    rw [eC₀.apply_symm_apply] at hx
    rw [hx, z₀.symm_apply_apply]
  · change z (bH (z₀.symm (z₀ t))) = y
    rw [z₀.symm_apply_apply, hty]
    exact z.apply_symm_apply y

end AlgebraicGeometry.Scheme
