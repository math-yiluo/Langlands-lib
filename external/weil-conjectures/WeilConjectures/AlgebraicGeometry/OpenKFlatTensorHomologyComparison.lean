/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIso
import WeilConjectures.Algebra.Homology.OpenRestrictionKFlat
public import WeilConjectures.Algebra.Homology.OpenRestrictionTensorHomology
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Open restriction and comparison of K-flat tensor homology

Source: Stacks Project, Tags 06YH, 08CG and 06YB.
(blueprint: lem-pc-open-kflat-tensor-homology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CochainComplex

/-- Open restriction preserves zero maps, since its maps are sectionwise restrictions. -/
instance openRestrictionPreservesZero
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : TopologicalSpace.Opens X) :
    (SheafOfModules.overFunctor.{u} A U).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext W x
  rfl

attribute [local instance] localizedTensorPreadditive

-- The cone-and-square argument of Stacks Tag 06YT applies to every ringed site.
-- These helpers generalize the proved one-point-site argument in KFlatTensorQuasiIso;
-- they do not import that specialized module or change its interface.
private theorem quasiIso_of_commuting_square
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {A B C D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (k : C ⟶ D)
    (hf : QuasiIso f) (hg : QuasiIso g) (hh : QuasiIso h)
    (comm : f ≫ h = g ≫ k) : QuasiIso k := by
  have := hf
  have := hg
  have := hh
  have hcomp : QuasiIso (g ≫ k) := by
    rw [← comm]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_left g k

private theorem kFlat_tensor_right_of_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (mapBifunctorMappingCone₁Iso α K (curriedTensor _))

private theorem kFlat_tensor_left_of_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((mappingCone α).d p p') (K.X q)).symm)
  have ht' : (mapBifunctor K (mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (mappingCone α) F (.up ℤ))
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (mapBifunctorMappingCone₂Iso K α F)

private theorem site_kFlat_tensor_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {E E' N : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E')
    (hα : QuasiIso α)
    (hE : E.IsKFlatTensor)
    (hE' : E'.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  obtain ⟨K, s, hK, _, hs, _⟩ := exists_isKFlatResolution N
  let f := HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ)
  let g := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor _) (.up ℤ)
  let h := HomologicalComplex.mapBifunctorMap (𝟙 E') s (curriedTensor _) (.up ℤ)
  let k := HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ)
  apply quasiIso_of_commuting_square f g h k
  · exact kFlat_tensor_right_of_quasiIso α hα hK
  · exact kFlat_tensor_left_of_quasiIso s hs hE
  · exact kFlat_tensor_left_of_quasiIso s hs hE'
  · change ((curriedTensor _).map₂CochainComplex.map α).app K ≫
        ((curriedTensor _).map₂CochainComplex.obj E').map s =
      ((curriedTensor _).map₂CochainComplex.obj E).map s ≫
        ((curriedTensor _).map₂CochainComplex.map α).app N
    exact (((curriedTensor _).map₂CochainComplex.map α).naturality s).symm


private theorem quasiIso_common_roof
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P Q T H : CochainComplex C ℤ}
    (q : P ⟶ Q) (s : H ⟶ Q) (t : H ⟶ T)
    [QuasiIso q] [QuasiIso s] [QuasiIso t] :
    ∃ (L : CochainComplex C ℤ) (a : L ⟶ P) (b : L ⟶ T), QuasiIso a ∧ QuasiIso b := by
  let DQ := DerivedCategory.Q (C := C)
  let e : DQ.obj P ≅ DQ.obj T :=
    asIso (DQ.map q) ≪≫ (asIso (DQ.map s)).symm ≪≫ asIso (DQ.map t)
  obtain ⟨L, a, ha, b, he⟩ := DerivedCategory.right_fac e.hom
  have : IsIso (DQ.map a) := ha
  have ha' : QuasiIso a := (DerivedCategory.isIso_Q_map_iff_quasiIso C a).1 ha
  have hb : IsIso (DQ.map b) := by
    have hb' : DQ.map b = DQ.map a ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hb']
    infer_instance
  exact ⟨L, a, b, ha', (DerivedCategory.isIso_Q_map_iff_quasiIso C b).1 hb⟩

private theorem site_kFlat_tensor_homology_iso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {P T L : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (hP : P.IsKFlatTensor) (hT : T.IsKFlatTensor)
    (a : L ⟶ P) (b : L ⟶ T) (ha : QuasiIso a) (hb : QuasiIso b)
    (N : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (i : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    Nonempty ((mapBifunctor P N (curriedTensor _)).homology i ≅
      (mapBifunctor T N (curriedTensor _)).homology i) := by
  classical
  let := SheafOfModules.monoidalCategory R
  obtain ⟨K, r, hK, _, hr, _⟩ := exists_isKFlatResolution (R := R) L
  have : QuasiIso a := ha
  have : QuasiIso b := hb
  have : QuasiIso r := hr
  let α := HomologicalComplex.mapBifunctorMap (r ≫ a) (𝟙 N) (curriedTensor _) (.up ℤ)
  let β := HomologicalComplex.mapBifunctorMap (r ≫ b) (𝟙 N) (curriedTensor _) (.up ℤ)
  have : QuasiIso α := site_kFlat_tensor_quasiIso (r ≫ a) inferInstance hK hP
  have : QuasiIso β := site_kFlat_tensor_quasiIso (r ≫ b) inferInstance hK hT
  exact ⟨(asIso (HomologicalComplex.homologyMap α i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap β i)⟩

/-- A roof identifying a local K-flat complex T with the restriction of Q identifies
its tensor homology with the open restriction of the tensor homology of any global
K-flat resolution P of Q. Source: Stacks Project, Tags 06YH, 08CG and 06YB.

Proof: open restriction is exact and commutes naturally with sheaf tensor.
The single-complex comparison therefore identifies tensor homology before and
after restriction. It preserves K-flatness, so the
restriction of P is a K-flat resolution of the restriction of Q. The roof s,t
identifies that restriction with T in the derived category. Use DerivedCategory.right_fac to
express the resulting isomorphism by a common
roof from L to the restricted P and T. Both legs are quasi-isomorphisms, since
localization reflects them. Take a K-flat resolution K of L. Its composites with
the two legs are quasi-isomorphisms between K-flat complexes.
To see why a quasi-isomorphism between K-flat complexes remains a quasi-isomorphism
after tensoring with the arbitrary sheaf F restricted to U, first take a K-flat
resolution B of that sheaf in degree zero. Tensoring the map with B preserves
quasi-isomorphisms by the acyclic-cone criterion and symmetry. Tensoring B to F[0]
with either K-flat endpoint also preserves quasi-isomorphisms. The resulting
commutative square and two-of-three prove the claim for F[0]. Taking homology of
the zigzag gives an isomorphism to the tensor with T. Compose it with the open
restriction homology and total-tensor comparisons. The construction is valid for
unbounded complexes,
empty opens, and arbitrary coefficient sheaves; it needs no degree bounds.
(blueprint: lem-pc-open-kflat-tensor-homology-comparison). -/
theorem open_kFlat_tensor_homology_comparison
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hP : IsKFlatTensor (R := R) P) (q : P ⟶ Q) (hq : QuasiIso q)
    (T H : CochainComplex (SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ)
    (hT : IsKFlatTensor (R := R.over U) T)
    (s : H ⟶ ((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q) (t : H ⟶ T) (hs : QuasiIso s) (ht : QuasiIso t)
    (F : SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (i : ℤ) :
    Nonempty (((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj
      ((mapBifunctor P ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) ≅
      ((mapBifunctor T ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj F))
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (R.over U)))).homology i)) := by
  classical
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let V := SheafOfModules.overFunctor.{u} A U
  let VC := V.mapHomologicalComplex (.up ℤ)
  have hVP : IsKFlatTensor (R := R.over U) (VC.obj P) :=
    open_localized_restriction_isKFlat R U inferInstance P hP
  have : QuasiIso q := hq
  have hVq : QuasiIso (VC.map q) :=
    localizedModule_restriction_quasiIso A U inferInstance q
  have : QuasiIso (VC.map q) := hVq
  have : QuasiIso s := hs
  have : QuasiIso t := ht
  let M := SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))
  let := HasDerivedCategory.standard M
  obtain ⟨L, a, b, ha, hb⟩ := quasiIso_common_roof (C := M) (VC.map q) s t
  let N := (HomologicalComplex.single M (.up ℤ) 0).obj (V.obj F)
  obtain ⟨d⟩ := site_kFlat_tensor_homology_iso hVP hT a b ha hb N i
  obtain ⟨c⟩ := open_localized_tensor_homology_iso R U inferInstance P F i
  exact ⟨c ≪≫ d⟩

end CochainComplex
