/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExistence

/-! # Extending the affine Hom comparison from its global generators

Source: Stacks Project, Tag 01I7 and Tag 01HV (4)-(5).
(blueprint: lem-sc-k4-affine-hom-generator-extension). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The associated-sheaf functor in the affine chart. -/
noncomputable def affineHomComparisonFunctor {Y : Scheme.{u}} (U : Y.affineOpens) :
    ModuleCat.{u} Γ(Y, U.1) ⥤ U.1.toScheme.Modules :=
  tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom

/-- The chart functor equation, used without unfolding its localization data. -/
theorem affineHomComparisonFunctor_eq {Y : Scheme.{u}} (U : Y.affineOpens) :
    affineHomComparisonFunctor U =
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom := rfl

/-- The rank-one associated sheaf is the structure sheaf of the chart. -/
noncomputable def affineHomComparisonUnitIso {Y : Scheme.{u}} (U : Y.affineOpens) :
    (affineHomComparisonFunctor U).obj (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ≅
      SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso (tildeSelf) ≪≫
    Scheme.Modules.restrictUnitIso U.2.isoSpec.hom

/-- The map from the free rank-one module sending one to a given element. -/
def affineHomElement {A : Type u} [CommRing A] (H : ModuleCat.{u} A) (h : H) :
    ModuleCat.of A A ⟶ H :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A H h)

section
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

/-- The unit generator associated to an element and a rank-one identification. -/
noncomputable def comparisonGenerator {A : Type u} [CommRing A]
    (T : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (e : T.obj (ModuleCat.of A A) ≅ SheafOfModules.unit _)
    (H : ModuleCat.{u} A) (h : H) : SheafOfModules.unit _ ⟶ T.obj H :=
  e.inv ≫ T.map (affineHomElement H h)

end

/-- The global generator of an associated sheaf represented by an element. -/
noncomputable def affineHomGenerator {Y : Scheme.{u}} (U : Y.affineOpens)
    (H : ModuleCat.{u} Γ(Y, U.1)) (h : H) :
    SheafOfModules.unit U.1.toScheme.ringCatSheaf ⟶
      (affineHomComparisonFunctor U).obj H :=
  comparisonGenerator (R := U.1.toScheme.sheaf)
    (affineHomComparisonFunctor U) (affineHomComparisonUnitIso U) H h

/-- A sheaf morphism regarded as a global section of internal Hom. -/
noncomputable def affineHomSection {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (h : M ⟶ N) : SheafOfModules.unit _ ⟶ SheafOfModules.homObj (R := R) M N :=
  (SheafOfModules.homObj (R := R) M N).unitHomEquiv.symm
    ((SheafOfModules.homObjSectionsEquiv M N).symm h)

private theorem hom_ext_of_elements {A : Type u} [CommRing A]
    {D : Type (u + 1)} [Category.{u} D]
    (T : ModuleCat.{u} A ⥤ D) (S : D ⥤ ModuleCat.{u} A) (adj : T ⊣ S)
    (H : ModuleCat.{u} A) (N : D) (f g : T.obj H ⟶ N)
    (h : ∀ x : H, T.map (affineHomElement H x) ≫ f =
      T.map (affineHomElement H x) ≫ g) : f = g := by
  apply (adj.homEquiv H N).injective
  ext x
  have hx := congrArg (adj.homEquiv (ModuleCat.of A A) N) (h x)
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at hx
  have hy := congrArg (fun k : ModuleCat.of A A ⟶ S.obj N ↦ k.hom 1) hx
  simpa [affineHomElement] using hy

/-- The images of global linear maps extend uniquely to the affine Hom comparison.
Source: Stacks Project, Tag 01I7, the mapping property, and Tag 01HV (4)-(5).
(blueprint: lem-sc-k4-affine-hom-generator-extension).

Proof: Work first on Spec A. The assignment h to the sheaf morphism tilde(h) is
A-linear. By the tilde/global-sections adjunction, this linear map into the global
sections of internal Hom extends uniquely to a morphism from tilde(Hom_A(M,N)).
Equivalently, on D(a), it sends h/a^r to the map taking m/a^s to h(m)/a^(r+s).
Localization makes this well defined and the maps compatible with restriction.
Transport the map along isoSpec. Its values on the displayed generators are the
specified global sections. For uniqueness, the generators give every global
section of the associated source, since the tilde adjunction unit is invertible;
localization then determines the map on every principal open. No finiteness of M
or quasi-coherence of internal Hom is required. The zero ring and zero modules
are covered by the same adjunction and localization construction. -/
theorem existsUnique_affineHom_generator_extension {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) :
    ∃! c : (affineHomComparisonFunctor U).obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
          ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N),
      ∀ h : M ⟶ N,
        affineHomGenerator U (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) h ≫ c =
          affineHomSection (R := U.1.toScheme.toRingedSpace.sheaf)
            ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N)
            ((affineHomComparisonFunctor U).map h) := by
  have hex : ∃ c :
      (affineHomComparisonFunctor U).obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
          ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N),
      ∀ h : M ⟶ N,
      affineHomGenerator U (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) h ≫ c =
        affineHomSection (R := U.1.toScheme.toRingedSpace.sheaf)
          ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N)
          ((affineHomComparisonFunctor U).map h) := by
    exact exists_affineHom_generator_extension U M N
      (affineHomComparisonFunctor U) (affineHomComparisonUnitIso U) rfl HEq.rfl
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, ?_⟩
  intro d hd
  have hAdj : (affineHomComparisonFunctor U).IsLeftAdjoint := by
    rw [affineHomComparisonFunctor_eq]
    infer_instance
  apply hom_ext_of_elements (affineHomComparisonFunctor U)
    (affineHomComparisonFunctor U).rightAdjoint
    (Adjunction.ofIsLeftAdjoint (affineHomComparisonFunctor U)) _ _ d c
  intro x
  have hx := hd x
  have hx' := hc x
  dsimp only [affineHomGenerator, comparisonGenerator] at hx hx'
  apply (cancel_epi (affineHomComparisonUnitIso U).inv).mp
  simpa only [Category.assoc] using hx.trans hx'.symm

/-- The comparison uniquely determined by its values on global generators.
The preceding unique-existence theorem determines this morphism up to equality;
its proof is postponed, while its full generator normalization is specified. -/
noncomputable def affineHomComparison {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) :
    (affineHomComparisonFunctor U).obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
      SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
        ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N) :=
  Classical.choose (existsUnique_affineHom_generator_extension U M N).exists

/-- Normalization of the uniquely chosen affine comparison. -/
theorem affineHomComparison_generator {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) (h : M ⟶ N) :
    affineHomGenerator U (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) h ≫
        affineHomComparison U M N =
      affineHomSection (R := U.1.toScheme.toRingedSpace.sheaf)
        ((affineHomComparisonFunctor U).obj M) ((affineHomComparisonFunctor U).obj N)
        ((affineHomComparisonFunctor U).map h) :=
  Classical.choose_spec (existsUnique_affineHom_generator_extension U M N).exists h

/-- Functoriality of the global generators. -/
theorem affineHomGenerator_map {Y : Scheme.{u}} (U : Y.affineOpens)
    {H H' : ModuleCat.{u} Γ(Y, U.1)} (f : H ⟶ H') (x : H) :
    affineHomGenerator U H x ≫ (affineHomComparisonFunctor U).map f =
      affineHomGenerator U H' (f.hom x) := by
  dsimp only [affineHomGenerator, comparisonGenerator]
  rw [Category.assoc, ← Functor.map_comp]
  congr 2
  ext
  simp [affineHomElement]

/-- Morphisms from an associated module are detected by its global generators.
This follows from the tilde adjunction: adjoint maps are linear maps, and a
linear map is determined by its composites with the maps sending one to x. -/
theorem affineHomGenerator_ext {Y : Scheme.{u}} (U : Y.affineOpens)
    (H : ModuleCat.{u} Γ(Y, U.1)) (N : U.1.toScheme.Modules)
    (f g : (affineHomComparisonFunctor U).obj H ⟶ N)
    (h : ∀ x : H, affineHomGenerator U H x ≫ f = affineHomGenerator U H x ≫ g) :
    f = g := by
  have : (affineHomComparisonFunctor U).IsLeftAdjoint := by
    rw [affineHomComparisonFunctor_eq]
    infer_instance
  apply hom_ext_of_elements (affineHomComparisonFunctor U)
    (affineHomComparisonFunctor U).rightAdjoint
    (Adjunction.ofIsLeftAdjoint (affineHomComparisonFunctor U)) H N f g
  intro x
  have hx := h x
  dsimp only [affineHomGenerator, comparisonGenerator] at hx
  exact (cancel_epi (affineHomComparisonUnitIso U).inv).mp hx

/-- Internal-Hom sections respect precomposition and postcomposition. -/
theorem affineHomSection_comp {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    {M M' N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (h : M ⟶ N) (f : M' ⟶ M) (g : N ⟶ N') :
    affineHomSection M N h ≫ SheafOfModules.homObjMap (R := R) f g =
      affineHomSection M' N' (f ≫ h ≫ g) := by
  apply (SheafOfModules.homObj (R := R) M' N').unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  simp only [affineHomSection, Equiv.apply_symm_apply]
  apply (SheafOfModules.homObjSectionsEquiv M' N').injective
  ext X x
  rfl

end AlgebraicGeometry
