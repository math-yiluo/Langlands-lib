/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.IdentityResolutionHomology
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-! # Identity property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-identity).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private instance schemeEnoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules :=
  inferInstance

private instance sectionsAdditive (X : Scheme.{u}) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
  inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)

noncomputable section

open Opposite

-- Prove naturality before specializing the resolution and homology types to scheme modules.
private theorem resolution_homology_naturality {C : Type*} [Category* C] [Abelian C]
    [HasInjectiveResolutions C] {R : Type u} [Ring R]
    (Γ : C ⥤ ModuleCat.{u} R) [Γ.Additive] {G F : C} (ψ : G ⟶ F)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (p : ℕ) :
    let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    let Γc := (Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    U.map (J.isoRightDerivedObj Γ p).hom ≫
        ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).sc p).mapHomologyIso
          U).inv ≫ H.map (Γc.map (InjectiveResolution.desc ψ I J)) =
      U.map ((Γ.rightDerived p).map ψ) ≫ U.map (I.isoRightDerivedObj Γ p).hom ≫
        ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
          U).inv := by
  dsimp only
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let α := InjectiveResolution.desc ψ I J
  have hn := J.isoRightDerivedObj_hom_naturality ψ I α
    (InjectiveResolution.desc_commutes_zero ψ I J) Γ p
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map α)) U
  change U.map ((Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map α) ≫ _ = _ at hs
  erw [← hs, ← U.map_comp_assoc, ← hn, U.map_comp, Category.assoc]

private theorem identity_diagram_cancel {C : Type*} [Category* C]
    {A B C₁ D E K L : C} (rJ : A ≅ B) (sJ : C₁ ≅ B) (rI : D ≅ E) (sI : K ≅ E)
    (β : C₁ ⟶ L) (μ : K ⟶ L) [IsIso μ] (α : C₁ ⟶ K) (ψ : A ⟶ D)
    (hsplit : β = α ≫ μ)
    (hn : rJ.hom ≫ sJ.inv ≫ α = ψ ≫ rI.hom ≫ sI.inv) :
    rJ.hom ≫ sJ.inv ≫ β ≫ inv μ ≫ sI.hom ≫ rI.inv = ψ := by
  rw [hsplit]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc, reassoc_of% hn, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

-- Resolution transports compare both module-valued and additive-group-valued homology.
set_option backward.isDefEq.respectTransparency.types false in
/-- Identity property of the cohomology map induced by an h-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB;
Derived Categories, Tags 013P, 013S, 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-identity).

Proof (argument specialized from the parent node):
Steps 1--3 are packaged in `moduleCohomologyFMap_identity_resolution_homology`;
the Lean proof combines that factorization with cancellation and Step 4.
1. For the choices D defining the identity-scheme map, take the ordinary resolution
   descent alpha of psi from D.J to D.I. The pushforward-identity natural isomorphism
   identifies the source of D.lambda with D.I; call the resulting map l.
2. The augmentation equations say that D.beta and alpha followed by l agree after
   D.J.ι. Extend by zero to integer indices and apply uniqueness of maps into a bounded
   below injective complex after a quasi-isomorphism (Stacks Tag 013S). Restrict the
   resulting homotopy to natural indices. Applying additive global sections gives the
   same map on homology for beta and alpha followed by l.
3. The pinned sections comparison D.a is the global-sections map of the inverse
   pushforward-identity comparison. Consequently homology of l is the invertible
   vertical map in the definition. Cancel it against its inverse.
4. Naturality of the forgetful homology comparison and of isoRightDerivedObj identifies
   the remaining composite with the underlying map of H^p(Z,psi). This argument uses
   the arbitrary choices defining the map and needs no independence theorem.
-/
theorem moduleCohomologyFMap_basic_identity {Z : Scheme.{u}}
    (GZ FZ : SheafOfModules.{u} Z.ringCatSheaf) (ψ : GZ ⟶ FZ) (p : ℕ) :
    moduleCohomologyFMap (𝟙 Z) ψ p =
        (forget₂ _ AddCommGrpCat).map ((Z.toRingedSpace.moduleCohomology p).map ψ) := by
  unfold moduleCohomologyFMap
  generalize Classical.choice _ = D
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let U := forget₂ (ModuleCat.{u}
    ((moduleRings Z.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let Γc := (Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)
  let α := InjectiveResolution.desc ψ D.I D.J
  have := D.invertible p
  change D.map p = _
  dsimp only [ModuleCohomologyFMapData.map]
  refine identity_diagram_cancel (U.mapIso (D.J.isoRightDerivedObj Γ p))
    (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso U)
    (U.mapIso (D.I.isoRightDerivedObj Γ p))
    (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso U)
    (H.map (Γc.map D.β)) (H.map (D.a.hom ≫ Γc.map D.lambda)) (H.map (Γc.map α))
    (U.map ((Γ.rightDerived p).map ψ)) ?_ ?_
  · exact moduleCohomologyFMap_identity_resolution_homology GZ FZ ψ D p
  · exact resolution_homology_naturality Γ ψ D.I D.J p


end

end AlgebraicGeometry.Scheme.Modules
