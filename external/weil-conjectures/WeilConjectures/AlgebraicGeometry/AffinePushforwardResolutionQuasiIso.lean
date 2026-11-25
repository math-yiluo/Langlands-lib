/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Affine pushforward of an unbounded quasi-coherent resolution

Source: Stacks Project, Tags 08C2 and 0AVW.
(blueprint: lem-pc-affine-pushforward-resolution-quasi-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

private theorem stalk_iso_of_basis (Y : Scheme.{u})
    {F G : Y.carrier.Presheaf AddCommGrpCat.{u}} (a : F ⟶ G)
    (h : ∀ V : Y.Opens, IsAffineOpen V → IsIso (a.app (op V))) (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis Y.isBasis_affineOpens
    intro V hV
    have := h V hV
    exact (ConcreteCategory.bijective_of_isIso (a.app (op V))).1
  · intro t
    obtain ⟨V, hyV, hV, t, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis Y.isBasis_affineOpens G y t
    have := h V hV
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (a.app (op V))).2 t
    exact ⟨F.germ V y hyV s, TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _⟩

private instance stalk_limits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) := by
  let W := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
    (OpenNhds.inclusion y).op
  have : PreservesFiniteLimits W := ⟨fun J _ _ ↦ by
    dsimp [W]
    infer_instance⟩
  exact comp_preservesFiniteLimits W colim
private instance stalk_colimits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) := by
  let W := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
    (OpenNhds.inclusion y).op
  have : PreservesFiniteColimits W := ⟨fun J _ _ ↦ by
    dsimp [W]
    infer_instance⟩
  exact comp_preservesFiniteColimits W colim
private theorem homology_map_iso_of_mapped
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.Additive] [T.PreservesHomology]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    [QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f)] :
    IsIso (T.map (HomologicalComplex.homologyMap f n)) := by
  let φ := (HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f
  have hi : IsIso ((T.mapShortComplex ⋙ ShortComplex.homologyFunctor D).map φ) :=
    inferInstanceAs (IsIso
      (HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map f) n))
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso T) φ).mp hi

private theorem quasiIso_of_affine_sections (Y : Scheme.{u})
    {K L : CochainComplex Y.Modules ℤ} (f : K ⟶ L)
    (h : ∀ V : Y.Opens, IsAffineOpen V →
      QuasiIso (((SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _ ⋙
        (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex
          (.up ℤ)).map f)) : QuasiIso f := by
  let U := SheafOfModules.forget Y.ringCatSheaf ⋙ PresheafOfModules.toPresheaf _
  let g := (U.mapHomologicalComplex (.up ℤ)).map f
  have hg (y : Y) : QuasiIso
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapHomologicalComplex
        (.up ℤ)).map g) := by
    constructor
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    let φ := (HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map g
    have hi : IsIso (S.map (HomologicalComplex.homologyMap g n)) := by
      apply stalk_iso_of_basis Y
      intro V hV
      let E := (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
      have : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map g) := h V hV
      exact homology_map_iso_of_mapped E g n
    exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso S) φ).mpr hi
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_stalkLinearMap
  intro y
  let T := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  have : T.Additive := by
    constructor
    intro M N a b
    ext x
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf _).map (a + b).val) x = _
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf _).map (a.val + b.val)) x = _
    rw [Functor.map_add, Functor.map_add]
    rfl
  have : T.PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro S hS
    exact ((RingedSpace.module_stalk_exact Y.toRingedSpace S.f).2.2.2.2
      S.X₃ S.f S.g S.zero).mp hS y
  let A := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  have hi : QuasiIso ((A.mapHomologicalComplex (.up ℤ)).map
      ((T.mapHomologicalComplex (.up ℤ)).map f)) := hg y
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ A).mp hi
  have := homology_map_iso_of_mapped T f n
  change Function.Bijective (ConcreteCategory.hom
    (T.map (HomologicalComplex.homologyMap f n)))
  exact ConcreteCategory.bijective_of_isIso _

/-- Applying affine pushforward to a K-injective resolution of a termwise
quasi-coherent complex gives a quasi-isomorphism.
Source: Stacks Project, Tag 08C2 (singleton affine covering) and Tag 0AVW
(affine cohomology calculation).
(blueprint: lem-pc-affine-pushforward-resolution-quasi-iso).

Proof: On every affine open V of Y the inverse image f⁻¹V is affine. Apply
`affineOpenSections_resolution_quasiIso` to s on f⁻¹V: its source is termwise
quasi-coherent and its target is K-injective, so its section map is a
quasi-isomorphism. Forgetting scalars identifies this map with Γ(V,f_*s).
For any y in Y, affine neighborhoods of y form a cofinal system of neighborhoods.
The stalk complex of f_*s is therefore the filtered colimit of these section
complexes. Filtered colimits of abelian groups are exact and hence preserve
homology, so f_*s induces an isomorphism on every stalk of every homology sheaf.
The module-stalk functors are exact and jointly reflect isomorphisms; consequently
f_*s is a quasi-isomorphism. No boundedness or quasi-coherence of the terms of J
is used. Empty schemes and empty inverse-image opens cause no exception: their
section complexes are zero and the stalk detection criterion is vacuous. -/
theorem affinePushforward_resolution_quasiIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (s : F ⟶ J) [QuasiIso s] :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map s) := by
  apply quasiIso_of_affine_sections Y
  intro V hV
  have h := affineOpenSections_resolution_quasiIso X (f ⁻¹ᵁ V) (hV.preimage f) F J hF s
  let B := forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  have := h
  have h' : QuasiIso ((B.mapHomologicalComplex (.up ℤ)).map
      (((alternatingCechModulePresheaf (X := X) ⋙
        (evaluation X.Opensᵒᵖ
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
            (op (f ⁻¹ᵁ V))).mapHomologicalComplex (.up ℤ)).map s)) := by
    infer_instance
  exact h'


end AlgebraicGeometry
