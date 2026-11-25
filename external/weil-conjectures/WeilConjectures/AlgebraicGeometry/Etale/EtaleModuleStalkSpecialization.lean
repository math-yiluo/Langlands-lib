/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Specialization of geometric module stalks

Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The specialization map is characterized on affine pointed neighbourhood germs by
restricting the limit projection along `t`. The quantified lift `v` is the composite
of `t` with the specified projection, not an arbitrary lift of its image in the base.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization). -/
def IsEtaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G) : Prop :=
  ∀ (j : SmallModel.{u} (strictHenselizationNeighbourhoods s))
    (v : (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.obj
      ((AffineEtale.Spec S).obj
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)),
    v.left = t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
      Spec.map (ΓSpecIso
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
          j).1.left.unop).inv →
    (pointSmallEtale s).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
        G.obj ≫ r =
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        v G.obj

/-- There is a unique map with the specified germ formula.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization).

Proof: the structural-map identity for each limit leg makes its composite with `t`
a lift of the image geometric point. Naturality of the cone makes the resulting
maps from neighbourhood sections to the target stalk compatible with every pointed
neighbourhood map. Affine pointed neighbourhoods are initial among all pointed
neighbourhoods, so the stalk colimit gives a map with these components. The colimit
universal property also gives uniqueness, since all affine germs are specified. -/
theorem existsUnique_etaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃! r : (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G,
      IsEtaleModuleStalkSpecialization s t G r := by
  classical
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let F := N ⋙ strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
    (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : F.Initial := (strictHenselization_properties s).1
  let v (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.obj
        ((AffineEtale.Spec S).obj (N.obj j).1) :=
    Over.homMk
      (t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv)
      (by
        change (t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv) ≫
            ((AffineEtale.Spec S).obj (N.obj j).1).hom =
          t ≫ strictHenselizationStructuralMap s
        dsimp only [N]
        rw [Category.assoc, Category.assoc]
        exact congrArg (fun q : strictHenselizationScheme s ⟶ S ↦ t ≫ q)
          (((exists_strictHenselizationStructuralMap s).choose_spec j)))
  have hv {i j : SmallModel.{u} (strictHenselizationNeighbourhoods s)} (f : i ⟶ j) :
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.map
        ((AffineEtale.Spec S).map (N.map f).1) (v i) = v j := by
    apply Over.OverMorphism.ext
    change (t ≫ (strictHenselizationCone s).π.app (op (op i)) ≫
      Spec.map (ΓSpecIso (N.obj i).1.left.unop).inv) ≫
        Spec.map (N.map f).1.left.unop = _
    have h := (strictHenselizationCone s).w (f.op.op)
    let g := (N.map f).1.left.unop
    change (strictHenselizationCone s).π.app (op (op i)) ≫
      Spec.map (Spec.map g).appTop = _ at h
    have hg := congrArg Spec.map (ΓSpecIso_inv_naturality g)
    simp only [Spec.map_comp] at hg
    calc
      _ = t ≫ (strictHenselizationCone s).π.app (op (op i)) ≫
          Spec.map (Spec.map g).appTop ≫
            Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv := by
        simp only [Category.assoc]
        rw [hg]
      _ = _ := by
        rw [← Category.assoc _ _ (Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv), h]
        rfl
  let c := ((pointSmallEtale s).presheafFiberCocone G.obj).whisker F.op
  let hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv F.op _).symm
      ((pointSmallEtale s).isColimitPresheafFiberCocone G.obj)
  let d : Cocone (F.op ⋙ (Functor.Elements.π (pointSmallEtale s).fiber).op ⋙
      G.obj) :=
    { pt := (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G
      ι :=
        { app := fun j ↦
            (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber
              ((AffineEtale.Spec S).obj (N.obj j.unop).1) (v j.unop) G.obj
          naturality := by
            intro i j f
            dsimp
            rw [Category.comp_id]
            change G.obj.map ((AffineEtale.Spec S).map (N.map f.unop).1).op ≫ _ = _
            rw [GrothendieckTopology.Point.toPresheafFiber_w, hv] } }
  refine ⟨hc.desc d, ?_, ?_⟩
  · intro j w hw
    have he : w = v j := by
      apply Over.OverMorphism.ext
      exact hw
    subst w
    exact hc.fac d (op j)
  · intro r hr
    apply hc.hom_ext
    intro j
    change (pointSmallEtale s).toPresheafFiber
      ((AffineEtale.Spec S).obj (N.obj j.unop).1) (N.obj j.unop).2 G.obj ≫ r = _
    rw [hr j.unop (v j.unop) rfl]
    exact (hc.fac d j).symm

/-- Specialization of geometric module stalks, the unique map carrying each affine
pointed-neighbourhood germ to its germ along the strict-localization projection.
Only the proof of its unique characterization is postponed; the object is determined.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization). -/
noncomputable def etaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G :=
  Classical.choose (existsUnique_etaleModuleStalkSpecialization s t G)

end AlgebraicGeometry.Scheme
