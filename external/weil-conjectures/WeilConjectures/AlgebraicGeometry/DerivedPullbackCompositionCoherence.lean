/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! Canonical derived pullback comparison: Stacks Project, Tag 0D5S. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

-- Resolve the source representative; invertibility of its localization descends equality.
private theorem derived_natTrans_ext_kflat
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u₁}} {F G : schemeDerivedCategory X ⥤ schemeDerivedCategory Y}
    (τ τ' : F ⟶ G)
    (h : ∀ P : CochainComplex (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) P →
      τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
      τ'.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) : τ = τ' := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  intro A
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective A
  obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) P
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  have := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (q.map s)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs)
  rw [← cancel_epi (F.map (DerivedCategory.Qh.map (q.map s))),
    τ.naturality, τ'.naturality, h K hK]

-- The identity counit is globally invertible, since the underived identity inverts quasi-isos.
private theorem derivedPullbackIdentity_normalized
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    : ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _,
      ∀ X : Scheme.{u₁},
        Functor.whiskerLeft (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) (i X).hom ≫
            (Functor.rightUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom =
          ε (𝟙 X) ≫
            Functor.whiskerRight
              (NatTrans.mapHomotopyCategory
                (Adjunction.leftAdjointIdIso
                  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
                  (Scheme.Modules.pushforwardId X)).hom (ComplexShape.up ℤ))
              (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            Functor.whiskerRight
              (Functor.mapHomotopyCategoryIdIso
                (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
                (ComplexShape.up ℤ)).hom (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            (Functor.leftUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom := by
  classical
  have one (X : Scheme.{u₁}) : ∃ i : derivedPullback (𝟙 X) ≅ 𝟭 _,
        Functor.whiskerLeft (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) i.hom ≫
            (Functor.rightUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom =
          ε (𝟙 X) ≫
            Functor.whiskerRight
              (NatTrans.mapHomotopyCategory
                (Adjunction.leftAdjointIdIso
                  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
                  (Scheme.Modules.pushforwardId X)).hom (ComplexShape.up ℤ))
              (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            Functor.whiskerRight
              (Functor.mapHomotopyCategoryIdIso
                (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
                (ComplexShape.up ℤ)).hom (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            (Functor.leftUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom := by
    let e := Adjunction.leftAdjointIdIso
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
      (Scheme.Modules.pushforwardId X)
    let eh : (Scheme.Modules.tensorPullback (𝟙 X)).mapHomotopyCategory
        (ComplexShape.up ℤ) ≅ 𝟭 _ :=
      { hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
        inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
        hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id]
                         exact NatTrans.mapHomotopyCategory_id _ _
        inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id]
                         exact NatTrans.mapHomotopyCategory_id _ _ } ≪≫
        Functor.mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)
    let eqh := Functor.isoWhiskerRight eh (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≪≫
      Functor.leftUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
    let W := HomotopyCategory.quasiIso
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    have hinv : W.IsInvertedBy
        ((Scheme.Modules.tensorPullback (𝟙 X)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))) :=
      (MorphismProperty.IsInvertedBy.iff_of_iso W eqh).2
        (Localization.inverts (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) W)
    let := hL (𝟙 X)
    have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      (derivedPullback (𝟙 X)) (ε (𝟙 X)) hinv
    let ei := asIso (ε (𝟙 X)) ≪≫ eqh ≪≫ (Functor.rightUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).symm
    let i := ((Functor.whiskeringLeft _ _ _).obj (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).preimageIso ei
    refine ⟨i, ?_⟩
    have hi : Functor.whiskerLeft (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) i.hom = ei.hom :=
      ((Functor.whiskeringLeft _ _ _).obj
        (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).map_preimage ei.hom
    rw [hi]
    simp [ei, eqh, eh, e]
    rfl
  choose i hi using one
  exact ⟨i, hi⟩

/-- Canonical composition comparisons have identity comparisons and satisfy coherence.
Source: Stacks Project, Cohomology, Tag 0D5S, with the tensor unit and associativity laws.
(blueprint: lem-pc-derived-pullback-comparison-coherence).
Proof: the identity tensor pullback is isomorphic to the identity functor by the
conjugate of the pushforward identity comparison under the pinned adjunction.
On a K-flat complex the identity counit is invertible, so this comparison descends
to an isomorphism L(id)* ≅ id by the universal property and K-flat resolutions.
For each unit law, whisker the proposed equality with Qh and compose with the
counit. The defining factorization hc and tensor unit law give equal maps on
K-flat complexes. Resolve every complex to descend the equality; uniqueness of
maps into the left-derived functor gives equality of natural transformations.
For associativity the same factorization rewrites both paths on a K-flat complex
as three successive counits followed by the underived tensor comparison. The
conjugates of pushforwardComp are associative by the adjunction mate calculus
and pushforward associativity. Concretely, use
Adjunction.leftAdjointCompIso_comp_id, Adjunction.leftAdjointCompIso_id_comp,
and Adjunction.leftAdjointCompIso_assoc for the underived comparisons.
Resolve complexes and use naturality and essential surjectivity of Qh
to extend component equalities to all derived objects. Equality of homs implies
equality of the resulting isomorphisms.
Empty schemes and identity morphisms require no extra hypotheses. -/
theorem derivedPullbackComposition_coherence
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hK : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y)
      (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ),
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso ((ε f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
    (hc :∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (c f g).hom =
          (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
    : ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _,
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c (𝟙 X) f ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.id_comp f)) =
            Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
              Functor.rightUnitor (derivedPullback f)) ∧
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c f (𝟙 Y) ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.comp_id f)) =
            Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
              Functor.leftUnitor (derivedPullback f)) ∧
        (∀ {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
          Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
            Functor.associator (derivedPullback g) (derivedPullback f)
                (derivedPullback h) ≪≫
              Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
                eqToIso (congrArg (fun k : W ⟶ Z => derivedPullback k)
                  (Category.assoc h f g))) := by
  obtain ⟨i, hi⟩ := derivedPullbackIdentity_normalized a ε hL
  refine ⟨i, ?_, ?_, ?_⟩
  · intro X Y f
    apply Iso.ext
    apply derived_natTrans_ext_kflat
    intro P hP
    exact (derivedPullbackComposition_unit_kflat a ε hL hK c hc i hi f P hP).1
  · intro X Y f
    apply Iso.ext
    apply derived_natTrans_ext_kflat
    intro P hP
    exact (derivedPullbackComposition_unit_kflat a ε hL hK c hc i hi f P hP).2
  · intro W X Y Z h f g
    apply Iso.ext
    apply derived_natTrans_ext_kflat
    intro P hP
    exact derivedPullbackComposition_assoc_kflat a ε hL hK c hc h f g P hP

end AlgebraicGeometry
