/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.AffinePushforwardIdealProduct
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Ideal subobjects of finite affine pushforwards

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YQ, steps using
Tags 01YP, 089W and 01XB
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construction of the coherent ideal-product subobject and its stalk property.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YQ, devissage paragraph.
The proof constructs the image of `J ⊗ f_*F → f_*F`, uses quasi-coherence and
local Noetherian coherence of images, and computes its stalk image as `JₓGₓ`.
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage) -/
private theorem finite_affine_pushforward_ideal_devissage_coherent
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsAffine Y]
    [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) (x : X)
    {J : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    [Mono ι] [J.IsQuasicoherent]
    (hι : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) :
    ∃ G' : Subobject ((pushforward f).obj F),
      RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
      (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι ((pushforward f).obj F),
        G'.arrow = h ≫ idealModuleProductι ι ((pushforward f).obj F)) ∧
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map G'.arrow).hom ∧
      Nonempty ((G' : X.Modules) ≅ idealModuleProduct ι ((pushforward f).obj F)) := by
  classical
  let G := (pushforward f).obj F
  have hG : RingedSpace.IsCoherent X.toRingedSpace G :=
    (isCoherent_pushforward_of_isFinite f F hF).1
  have : G.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG).1
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let m : MonoidalCategory.tensorObj J G ⟶ G :=
    MonoidalCategory.whiskerRight ι G ≫ (MonoidalCategory.leftUnitor G).hom
  have : (MonoidalCategory.tensorObj J G).IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections J G).1
  have : (Abelian.image m).IsQuasicoherent :=
    (quasiCoherent_cokernel_image m).2.2.2.2.2.2.2.1
  have hK : (idealModuleProduct ι G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage m) inferInstance
  have hm : Mono (idealModuleProductι ι G) := by
    dsimp [idealModuleProductι]
    infer_instance
  let i := idealModuleProductι ι G
  let e := Subobject.underlyingIso i
  have hqc : (Subobject.mk i : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hK
  refine ⟨Subobject.mk i,
    ((isCoherent_kernel_cokernel_biprod_and_submodule X).2 G _
      (Subobject.mk i).arrow hG inferInstance hqc).1,
    ⟨e.hom, (Subobject.underlyingIso_hom_comp_eq_mk i).symm⟩, ?_, ⟨e⟩⟩
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨es, hes, hJ, hinj, hrange, hrest⟩ := ideal_module_product_stalk ι G x
  have hepi : Function.Surjective (S.map ι ≫ es.hom).hom :=
    ((ModuleCat.epi_iff_surjective es.hom).mp inferInstance).comp hι
  have htop : LinearMap.range (S.map ι ≫ es.hom).hom = ⊤ :=
    LinearMap.range_eq_top.mpr hepi
  have hi : Function.Surjective (S.map i).hom := by
    apply LinearMap.range_eq_top.mp
    change LinearMap.range (S.map (idealModuleProductι ι G)).hom = ⊤
    rw [hrange, htop, Submodule.top_smul]
  rw [← Subobject.underlyingIso_hom_comp_eq_mk i, S.map_comp]
  exact hi.comp ((ModuleCat.epi_iff_surjective (S.map e.hom)).mp inferInstance)

private noncomputable def topCohomologyEquiv (X : TopCat.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    Sheaf.H' F q ⊤ ≃+ Sheaf.H.{u} F q := by
  let e : yoneda.obj (⊤ : TopologicalSpace.Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (TopologicalSpace.Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      let : Unique (U.unop ⟶ (⊤ : TopologicalSpace.Opens X)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  exact (Abelian.Ext.precompAddEquiv eS F q).symm

/-- Vanishing of first cohomology for the coherent ideal-product subobject.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YQ, using 089W and 01XB.
The affine projection formula identifies the ideal product with the pushforward of
`(f*J)F`; affine cohomology comparison and affine vanishing then give `IsZero`.
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage) -/
private theorem finite_affine_pushforward_ideal_devissage_cohomology
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsAffine Y]
    [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F)
    {J : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    [Mono ι] [J.IsQuasicoherent] :
    IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (idealModuleProduct ι ((pushforward f).obj F))) := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType Y F).mp hF).1
  let L := idealModuleProduct
    ((tensorPullback f).map ι ≫ tensorPullbackObjUnitToUnit f) F
  obtain ⟨hq, heq⟩ := affine_pushforward_ideal_product f F ι
  have : L.IsQuasicoherent := hq
  have hm : Mono (idealModuleProductι ι ((pushforward f).obj F)) := by
    dsimp [idealModuleProductι]; infer_instance
  have hn : Mono (idealModuleProductι
      ((tensorPullback f).map ι ≫ tensorPullbackObjUnitToUnit f) F) := by
    dsimp [idealModuleProductι]; infer_instance
  let i := idealModuleProductι ι ((pushforward f).obj F)
  let j := (pushforward f).map (idealModuleProductι
    ((tensorPullback f).map ι ≫ tensorPullbackObjUnitToUnit f) F)
  let e := (imageMonoIsoSource i).symm ≪≫
    (Subobject.isoOfMkEqMk (image.ι i) (image.ι j) heq) ≪≫ imageMonoIsoSource j
  have hv : Subsingleton (L.H 1) := subsingleton_H_succ_of_isAffine L 0
  have : Subsingleton (CategoryTheory.Sheaf.H
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj L) 1) := hv
  obtain ⟨c⟩ := module_cohomology_iso_underlying_abelian Y L 1
  have : Subsingleton ((RingedSpace.moduleCohomology Y.toRingedSpace 1).obj L) := by
    let d := (topCohomologyEquiv Y.carrier
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj L) 1)
    have : Subsingleton (CategoryTheory.Sheaf.H'
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj L) 1 ⊤) :=
      d.injective.subsingleton
    exact c.addCommGroupIsoToAddEquiv.injective.subsingleton
  have he := (affine_morphism_cohomology_edge f L).2 1
  have : IsIso (moduleCohomologyEdgeMap f L 1) := he.1
  have hz' : IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      ((pushforward f).obj L)) := by
    have hza := (AddCommGrpCat.isZero_of_subsingleton _).of_iso
      (asIso (moduleCohomologyEdgeMap f L 1))
    have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        ((pushforward f).obj L)) := AddCommGrpCat.subsingleton_of_isZero hza
    exact ModuleCat.isZero_of_subsingleton _
  exact hz'.of_iso ((RingedSpace.moduleCohomology X.toRingedSpace 1).mapIso e)

/-- The ideal product in a finite pushforward from an affine scheme provides the
coherent, generically full, acyclic subobject required for coherent devissage.
No support or generic-point hypothesis is required: the full-stalk conclusion holds
at any point where the ideal has full stalk.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YQ, the paragraph
beginning "Let J be a quasi-coherent sheaf of ideals", using Tags 01YP, 089W and 01XB.
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage).

Proof:
Put G = f_*F and K = JG, constructed as the image of multiplication. Finite
pushforward preserves coherence (01Y6); on the locally Noetherian schemes X and Y,
coherent modules are quasi-coherent of finite type (01XZ). Tensor products and images
of quasi-coherent modules are quasi-coherent (01I8), so K is quasi-coherent. Its
inclusion into coherent G is monic, hence K is coherent (01Y0). Take G' to be the
subobject represented by this inclusion. The canonical underlying isomorphism
identifies its arrow with the inclusion of K.
Stalks commute with tensor products and images (01AG, 01CB). Thus the range of
K_x → G_x is J_x G_x. Surjectivity of J_x → O_X,x says J_x is the unit ideal,
so that range is all G_x. The underlying isomorphism gives surjectivity for G'.
By the affine projection formula for ideals (01YP), K is isomorphic to f_*L,
where L = (f^*J)F is quasi-coherent. The subobject equality in 01YP, together
with the image-of-monomorphism isomorphisms, gives this isomorphism of modules.
Affine-morphism cohomology comparison (089W) identifies H¹(X,f_*L) with
H¹(Y,L), which vanishes because Y is affine and L is quasi-coherent (01XB).
Transport zero cohomology along the two module isomorphisms to obtain H¹(X,G') = 0.
The argument also covers zero F, the empty scheme, and the unit ideal. -/
theorem finite_affine_pushforward_ideal_devissage
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsAffine Y]
    [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) (x : X)
    {J : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    [Mono ι] [J.IsQuasicoherent]
    (hι : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) :
    ∃ G' : Subobject ((pushforward f).obj F),
      RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
      (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι ((pushforward f).obj F),
        G'.arrow = h ≫ idealModuleProductι ι ((pushforward f).obj F)) ∧
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map G'.arrow).hom ∧
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (G' : X.Modules)) := by
  obtain ⟨G', hG, hfac, hsurj, ⟨e⟩⟩ :=
    finite_affine_pushforward_ideal_devissage_coherent f F hF x ι hι
  refine ⟨G', hG, hfac, hsurj, ?_⟩
  exact (finite_affine_pushforward_ideal_devissage_cohomology f F hF ι).of_iso
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).mapIso e)

end AlgebraicGeometry.Scheme.Modules
