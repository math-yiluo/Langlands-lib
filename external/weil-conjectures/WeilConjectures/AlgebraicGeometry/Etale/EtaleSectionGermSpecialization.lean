/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricSpecializationStrictLocalLift

/-! # Specialization invariance of the bijectivity locus of a section map

Source: Stacks Project, Tags 0GJ2, 0GJ5, 0GJ6 and 0GKC.
(blueprint: lem-weil-pbc-etale-section-germ-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

private noncomputable def affinePointedInclusion
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :=
  (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left)

private noncomputable def pointedSchemeDiagram
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :=
  Functor.Elements.π (pointSmallEtale s).fiber ⋙ Etale.forget S ⋙ Over.forget S

private noncomputable def affineSchemeCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Cone (affinePointedInclusion s ⋙ pointedSchemeDiagram s) := by
  let D := affinePointedInclusion s ⋙ pointedSchemeDiagram s
  have hAff (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      IsAffine (D.obj j) := by
    change IsAffine (Spec _)
    infer_instance
  let _ : ∀ j, IsAffine (D.obj j) := hAff
  let E := (opOpEquivalence (SmallModel.{u} (strictHenselizationNeighbourhoods s))).symm
  let cR := (strictHenselizationCone s).whisker E.functor
  let α : D ⟶ E.functor ⋙ (strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec :=
    Functor.whiskerLeft D ΓSpec.adjunction.unit
  have hIso (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      IsIso (α.app j) := by
    exact inferInstanceAs (IsIso (ΓSpec.adjunction.unit.app (D.obj j)))
  let : IsIso α := NatIso.isIso_of_isIso_app α
  exact (Cone.postcompose (asIso α).inv).obj cR

private noncomputable def affineSchemeCone_isLimit
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsLimit (affineSchemeCone s) := by
  dsimp only [affineSchemeCone]
  exact (IsLimit.postcomposeInvEquiv _ _).symm
    ((strictHenselization_properties s).2.2.some.whiskerEquivalence _)

private theorem affineSchemeCone_leg
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (affineSchemeCone s).π.app j =
      (strictHenselizationCone s).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
            j).1.left.unop).inv := by
  dsimp [affineSchemeCone]
  rw [NatIso.isIso_inv_app]
  change _ ≫ inv (Spec _).toSpecΓ = _
  congr 1
  change (Spec _).isoSpec.inv = _
  exact isoSpec_Spec_inv _

private noncomputable def allSchemeCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cone (pointedSchemeDiagram s) := by
  letI : (affinePointedInclusion s).Initial := (strictHenselization_properties s).1
  exact (Functor.Initial.extendCone (F := affinePointedInclusion s)).obj
    (affineSchemeCone s)

private noncomputable def allSchemeCone_isLimit
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsLimit (allSchemeCone s) := by
  letI : (affinePointedInclusion s).Initial := (strictHenselization_properties s).1
  exact (Functor.Initial.isLimitExtendConeEquiv (affinePointedInclusion s) _).symm
    (affineSchemeCone_isLimit s)

private theorem allSchemeCone_affine
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (allSchemeCone s).π.app ((affinePointedInclusion s).obj j) =
      (affineSchemeCone s).π.app j := by
  let : (affinePointedInclusion s).Initial := (strictHenselization_properties s).1
  calc
    _ = (affineSchemeCone s).π.app j ≫
        (pointedSchemeDiagram s).map (𝟙 ((affinePointedInclusion s).obj j)) :=
      Functor.Initial.extendCone_obj_π_app' (affineSchemeCone s) _
    _ = _ := by simp

private theorem allSchemeCone_over
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (n : (pointSmallEtale s).fiber.Elements) :
    (allSchemeCone s).π.app n ≫ n.1.hom = strictHenselizationStructuralMap s := by
  let : (affinePointedInclusion s).Initial := (strictHenselization_properties s).1
  let j := Functor.Initial.lift (affinePointedInclusion s) n
  let k := Functor.Initial.homToLift (affinePointedInclusion s) n
  rw [show (allSchemeCone s).π.app n =
      (affineSchemeCone s).π.app j ≫ (pointedSchemeDiagram s).map k from
    Functor.Initial.extendCone_obj_π_app' (affineSchemeCone s) k]
  change ((affineSchemeCone s).π.app j ≫ k.1.left) ≫ n.1.hom = _
  have hw : k.1.left ≫ n.1.hom = ((affinePointedInclusion s).obj j).1.hom := k.1.w
  rw [Category.assoc, hw, affineSchemeCone_leg]
  exact ((exists_strictHenselizationStructuralMap s).choose_spec j)

private noncomputable def specializationPointHom
    {S : Scheme.{u}} {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω]
    [Field Ξ] [IsAlgClosed Ξ] (s : Spec (.of Ω) ⟶ S)
    (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s) :
    pointSmallEtale (t ≫ strictHenselizationStructuralMap s) ⟶ pointSmallEtale s where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun a ↦
        Over.homMk (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U a))
          (by
            change (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U a)) ≫ U.hom =
              t ≫ strictHenselizationStructuralMap s
            rw [Category.assoc, allSchemeCone_over])
      naturality := by
        intro U V f
        ext a
        apply Over.OverMorphism.ext
        symm
        change (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U a)) ≫ f.left =
          t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ V ((pointSmallEtale s).fiber.map f a))
        rw [Category.assoc]
        congr 1
        let k : (pointSmallEtale s).fiber.elementsMk U a ⟶
            (pointSmallEtale s).fiber.elementsMk V
              ((pointSmallEtale s).fiber.map f a) := ⟨f, rfl⟩
        exact (allSchemeCone s).w k }

private theorem specializationPointHom_germ
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : S.Etale) (a : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U a G.obj ≫
        (specializationPointHom s t).sheafFiber.app G =
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber U
        (Over.homMk (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U a))
          (by
            change (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U a)) ≫ U.hom =
              t ≫ strictHenselizationStructuralMap s
            rw [Category.assoc, allSchemeCone_over])) G.obj := by
  simp only [GrothendieckTopology.Point.Hom.sheafFiber, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

private theorem specializationPointHom_eq
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (specializationPointHom s t).sheafFiber.app G =
      etaleModuleStalkSpecialization s t G := by
  apply (Classical.choose_spec (existsUnique_etaleModuleStalkSpecialization s t G)).2
  intro j v hv
  rw [specializationPointHom_germ]
  congr 1
  apply Over.OverMorphism.ext
  change t ≫ (allSchemeCone s).π.app ((affinePointedInclusion s).obj j) = v.left
  rw [allSchemeCone_affine, affineSchemeCone_leg]
  exact hv.symm

private noncomputable def pullbackPointedFunctor
    {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U.left) :
    (pointSmallEtale (b ≫ U.hom)).fiber.Elements ⥤ (pointSmallEtale b).fiber.Elements where
  obj n :=
    Functor.elementsMk _ ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj n.1)
      (Over.homMk (pullback.lift n.2.left b n.2.w) (pullback.lift_snd _ _ _))
  map {n m} f :=
    ⟨(MorphismProperty.Over.pullback @Etale ⊤ U.hom).map f.1, by
      apply Over.OverMorphism.ext
      change pullback.lift n.2.left b n.2.w ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).map f.1).left =
          pullback.lift m.2.left b m.2.w
      apply pullback.hom_ext
      · rw [MorphismProperty.Over.pullback_map_left]
        erw [Category.assoc, pullback.lift_fst, ← Category.assoc,
          pullback.lift_fst, pullback.lift_fst]
        exact congrArg Over.Hom.left f.2
      · rw [MorphismProperty.Over.pullback_map_left]
        erw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
        exact (pullback.lift_snd _ _ _).symm⟩
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

private noncomputable def strictLocalRelativeCone
    {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U.left) :
    Cone (pointedSchemeDiagram (b ≫ U.hom)) where
  pt := strictHenselizationScheme b
  π :=
    { app := fun n ↦ (allSchemeCone b).π.app ((pullbackPointedFunctor U b).obj n) ≫
        pullback.fst n.1.hom U.hom
      naturality := by
        intro n m f
        change _ = _ ≫ f.1.left
        simp only [Category.assoc]
        let k := (pullbackPointedFunctor U b).map f
        have hk : k.1.left ≫ pullback.fst m.1.hom U.hom =
            pullback.fst n.1.hom U.hom ≫ f.1.left := by
          exact pullback.lift_fst _ _ _
        rw [← hk, ← Category.assoc]
        exact congrArg (fun q ↦ q ≫ pullback.fst m.1.hom U.hom)
          ((allSchemeCone b).w k).symm }

private noncomputable def strictLocalRelativeMap
    {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U.left) :
    strictHenselizationScheme b ⟶ strictHenselizationScheme (b ≫ U.hom) :=
  (allSchemeCone_isLimit (b ≫ U.hom)).lift (strictLocalRelativeCone U b)

private theorem strictLocalRelativeMap_fst
    {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U.left) :
    strictLocalRelativeMap U b ≫
      (allSchemeCone (b ≫ U.hom)).π.app (Functor.elementsMk _ U (Over.homMk b rfl)) =
        strictHenselizationStructuralMap b := by
  rw [show strictLocalRelativeMap U b ≫
      (allSchemeCone (b ≫ U.hom)).π.app (Functor.elementsMk _ U (Over.homMk b rfl)) =
      (strictLocalRelativeCone U b).π.app (Functor.elementsMk _ U (Over.homMk b rfl)) from
    (allSchemeCone_isLimit (b ≫ U.hom)).fac (strictLocalRelativeCone U b) _]
  let T : U.left.Etale := Etale.mk (𝟙 U.left)
  let n := (pointSmallEtale b).fiber.elementsMk T (Over.homMk b (Category.comp_id b))
  let m := (pullbackPointedFunctor U b).obj (Functor.elementsMk _ U (Over.homMk b rfl))
  let δ : n ⟶ m :=
    ⟨MorphismProperty.Over.homMk (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl)
      (pullback.lift_snd _ _ _), by
      apply Over.OverMorphism.ext
      change b ≫ pullback.lift (𝟙 U.left) (𝟙 U.left) rfl =
        pullback.lift b b rfl
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]⟩
  change (allSchemeCone b).π.app m ≫ pullback.fst U.hom U.hom = _
  rw [← (allSchemeCone b).w δ, Category.assoc]
  change (allSchemeCone b).π.app n ≫
    pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom = _
  rw [pullback.lift_fst]
  exact allSchemeCone_over b n

private theorem germ_bijective_normalize
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : S.Etale) (M : ModuleCat.{u + 1} Λ) (f : M ⟶ G.obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (b : Spec (.of Ω) ⟶ U.left) (hb : b ≫ U.hom = s) :
    Function.Bijective
      (f ≫ (pointSmallEtale s).toPresheafFiber U (Over.homMk b hb) G.obj) ↔
    Function.Bijective (f ≫ (pointSmallEtale (b ≫ U.hom)).toPresheafFiber U
      (Over.homMk b rfl) G.obj) := by
  subst s
  rfl

/-- A section map which is bijective on a geometric stalk remains bijective on every
geometric stalk above a comparable point of the same etale neighbourhood.

Source: Stacks Project, Tag 0GKC, bijectivity-locus paragraph, with Tags 0GJ2, 0GJ5 and
0GJ6 (blueprint: lem-weil-pbc-etale-section-germ-specialization).

Proof: Transport the spectrum cone along the Gamma-Spec isomorphism and the
double-opposite equivalence. Affine initiality extends it to a limiting cone over all
pointed etale neighbourhoods. Its projections give a morphism of point fibre functors;
the induced stalk map satisfies the defining affine germ formula, hence equals the
specified specialization by uniqueness. Base change of pointed neighbourhoods along
U to S gives a cone with vertex the strict localization of U at b. The limit property
provides its map to the strict localization of S at b followed by U to S. The diagonal
U to U times_S U shows that its projection to the pointed neighbourhood (U,b) is the
structural map of the strict localization of U. Lift the prescribed geometric point a
to that strict localization using the geometric-specialization lift theorem. Composing
with the comparison map gives a specialization on S that carries the germ at b of every
section over U to its germ at a. This specialization is bijective by hypothesis, so a
section map is bijective at one germ precisely when it is bijective at the other.
The argument also works when the underlying points agree and uses neither finiteness
nor Noetherian hypotheses. -/
theorem etale_section_germ_bijective_specializes_iff
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hsp : ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
      (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s),
      Function.Bijective (etaleModuleStalkSpecialization s t G))
    (U : S.Etale) (M : ModuleCat.{u + 1} Λ) (f : M ⟶ G.obj.obj (op U))
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (a : Spec (.of Ω) ⟶ U.left) (b : Spec (.of Ξ) ⟶ U.left)
    (h : a (IsLocalRing.closedPoint Ω) ⤳ b (IsLocalRing.closedPoint Ξ)) :
    Function.Bijective (f ≫ (pointSmallEtale (a ≫ U.hom)).toPresheafFiber U
      (Over.homMk a rfl) G.obj) ↔
    Function.Bijective (f ≫ (pointSmallEtale (b ≫ U.hom)).toPresheafFiber U
      (Over.homMk b rfl) G.obj) := by
  obtain ⟨tU, htU⟩ := exists_geometricPoint_strictHenselization_lift
    (a (IsLocalRing.closedPoint Ω)) (b (IsLocalRing.closedPoint Ξ)) h a b rfl rfl
  let s := b ≫ U.hom
  let t := tU ≫ strictLocalRelativeMap U b
  have ht : t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U (Over.homMk b rfl)) = a := by
    dsimp only [t, s]
    rw [Category.assoc, strictLocalRelativeMap_fst]
    exact htU
  let v : (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.obj U :=
    Over.homMk (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U (Over.homMk b rfl)))
      (by
        change (t ≫ (allSchemeCone s).π.app (Functor.elementsMk _ U (Over.homMk b rfl))) ≫ U.hom =
          t ≫ strictHenselizationStructuralMap s
        rw [Category.assoc, allSchemeCone_over])
  have hg := specializationPointHom_germ s t G U (Over.homMk b rfl)
  rw [specializationPointHom_eq] at hg
  have hbij : Function.Bijective
        (f ≫ (pointSmallEtale s).toPresheafFiber U (Over.homMk b rfl) G.obj) ↔
      Function.Bijective
        (f ≫ (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber U
          v G.obj) := by
    rw [← hg, ← Category.assoc]
    exact (Function.Bijective.of_comp_iff' (hsp Ξ Ω s t) _).symm
  have hn := germ_bijective_normalize G U M f
    (t ≫ strictHenselizationStructuralMap s) v.left v.w
  have hh := hbij.trans hn
  change Function.Bijective
      (f ≫ (pointSmallEtale s).toPresheafFiber U (Over.homMk b rfl) G.obj) ↔
    Function.Bijective (f ≫ (pointSmallEtale (v.left ≫ U.hom)).toPresheafFiber U
      (Over.homMk v.left rfl) G.obj) at hh
  have hv : v.left = a := ht
  rw [hv] at hh
  exact hh.symm

end AlgebraicGeometry.Scheme
