/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Free module objects on the underlying sheaf of sets

The free abelian sheaf functor followed by the free module-object functor is left adjoint
to forgetting both structures. Its counit provides canonical generators of any module.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]

/-- Free module objects on sheaves of sets, using the two existing free adjunctions.
Source: the free abelian group and free module adjunctions, sheafified. -/
noncomputable def moduleObjectGeneratorAdjunction :
    Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙ Mod.free R ⊣
      Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1}) :=
  (Sheaf.adjunction (Scheme.ProEt.topology X) AddCommGrpCat.adj.{u + 1}).comp
    (Mod.freeForgetAdjunction R)

/-- The actual free module object on the underlying sheaf of sets of a module.
Source: free abelian sheaf followed by free module object. -/
noncomputable def moduleObjectFreeGenerators
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R :=
  (Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙ Mod.free R).obj
    ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj M)

/-- Send a free generator to the corresponding section of the module.
Source: the counit of the composite free-forgetful adjunction. -/
noncomputable def moduleObjectFreeGeneratorsπ
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    moduleObjectFreeGenerators R M ⟶ M :=
  (moduleObjectGeneratorAdjunction R).counit.app M

/-- The canonical map from the free module on all local sections is epimorphic.
Source: Mathlib's counit-epimorphism theorem for a faithful right adjoint.

Proof: the underlying-set sheaf functor is faithful, as are the module-object and
abelian-group forgetful functors. Therefore the right adjoint of the composed free
functor is faithful. Every counit of such an adjunction is an epimorphism. -/
instance moduleObjectFreeGeneratorsπ_epi
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Epi (moduleObjectFreeGeneratorsπ R M) :=
  (moduleObjectGeneratorAdjunction R).counit_epi_of_R_faithful M

end AlgebraicGeometry.ProEtale

open MonoidalCategory

namespace AlgebraicGeometry.ProEtale
variable (X : Scheme.{u})
private noncomputable def freeAbConstantIso :
    constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
        Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ≅
      AddCommGrpCat.free.{u + 1} ⋙ constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} := by
  let a := (constantSheafAdj (Scheme.ProEt.topology X) (Type (u + 1))
    terminalIsTerminal).comp (Sheaf.adjunction _ AddCommGrpCat.adj.{u + 1})
  let b := AddCommGrpCat.adj.{u + 1}.comp
    (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1} terminalIsTerminal)
  exact a.leftAdjointUniq b
private noncomputable def freeRegularIso
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).obj (𝟙_ _) ≅ Mod.regular R := by
  apply Mod.isoMk (ρ_ R)
  change (α_ R R (𝟙_ _)).inv ≫ MonObj.mul ▷ _ ≫ (ρ_ R).hom =
    R ◁ (ρ_ R).hom ≫ MonObj.mul
  rw [rightUnitor_naturality, ← Category.assoc]
  congr 1
  monoidal
private noncomputable def freeAbUnitIso : AddCommGrpCat.free.obj PUnit.{u + 2} ≅ 𝟙_ Ab.{u + 1} :=
  ((FreeAbelianGroup.uniqueEquiv PUnit).trans ULift.ringEquiv.toAddEquiv.symm).toAddCommGrpIso
private noncomputable def freeGeneratorConstUnitIso
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙
      Mod.free R).obj ((constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        PUnit.{u + 2}) ≅ Mod.regular R :=
  (Mod.free R).mapIso ((freeAbConstantIso X).app _ ≪≫
      (constantSheaf _ Ab.{u + 1}).mapIso freeAbUnitIso) ≪≫
    (Mod.free R).mapIso (Functor.Monoidal.εIso (presheafToSheaf _ Ab.{u + 1})).symm ≪≫
    freeRegularIso X R

attribute [local instance] comp_preservesColimits
private noncomputable def freeGeneratorConstFinIso
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] (n : ℕ) :
    (Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙
      Mod.free R).obj ((constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) ≅ Mod.finiteFree R n := by
  let F := constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
    Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙
      Mod.free R
  let adj := (constantSheafAdj (Scheme.ProEt.topology X) (Type (u + 1))
    terminalIsTerminal).comp (moduleObjectGeneratorAdjunction R)
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  let e : (Σ _ : Fin n, PUnit.{u + 2}) ≅ ULift.{u + 1} (Fin n) :=
    ((Equiv.sigmaPUnit (Fin n)).trans Equiv.ulift.symm).toIso
  exact F.mapIso e.symm ≪≫
    F.mapIso (Types.coproductIso (fun _ : Fin n ↦ PUnit.{u + 2})).symm ≪≫
    PreservesCoproduct.iso F (fun _ : Fin n ↦ PUnit.{u + 2}) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n ↦ F.obj PUnit.{u + 2})).symm ≪≫
    biproduct.mapIso (fun _ ↦ freeGeneratorConstUnitIso X R)

private noncomputable def generatorPullbackIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙
      Mod.free R) ⋙ (upperStar Ab.{u + 1} f).mapMod R ≅
    Scheme.proEtaleSheafInverseImage f (Type (u + 1)) ⋙
      (Sheaf.composeAndSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.free.{u + 1} ⋙
        Mod.free ((upperStar Ab.{u + 1} f).obj R)) := by
  let a := (moduleObjectGeneratorAdjunction R).comp
    ((upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction R)
  let b := (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).comp
    (moduleObjectGeneratorAdjunction ((upperStar Ab.{u + 1} f).obj R))
  exact a.leftAdjointUniq b

/-- Finite locally constant generators give a locally finite free module object.
Source: free-forgetful adjunctions and finite coproduct preservation.

Proof: uniqueness of left adjoints compares pullback followed by the free functor
with the free functor followed by pullback. The corresponding right adjoints are
identical on sections. For a finite constant sheaf, commute the free abelian sheaf
functor with constant sheaves, again by uniqueness of left adjoints. The free
abelian group on one point is the tensor unit. The free module on that unit is the
regular module by the right unitor. Both left adjoints preserve finite coproducts,
so a set of n generators gives the biproduct of n regular modules. This includes
n = 0 and the empty cover. -/
theorem moduleObjectFreeGenerators_locallyFree
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      ∃ n : ℕ, Nonempty
        ((Scheme.proEtaleSheafInverseImage (C.f i) (Type (u + 1))).obj
          ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X)
            (forget Ab.{u + 1})).obj M) ≅
          (constantSheaf (Scheme.ProEt.topology (C.X i)) (Type (u + 1))).obj
            (ULift.{u + 1} (Fin n)))) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f i)).obj R)
        (((upperStar Ab.{u + 1} (C.f i)).mapMod R).obj
          (moduleObjectFreeGenerators R M)) := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC i
  exact ⟨n, ⟨(generatorPullbackIso X (C.f i) R).app _ ≪≫
    (Sheaf.composeAndSheafify (Scheme.ProEt.topology (C.X i))
      AddCommGrpCat.free.{u + 1} ⋙
      Mod.free ((upperStar Ab.{u + 1} (C.f i)).obj R)).mapIso e ≪≫
    freeGeneratorConstFinIso (C.X i) _ n⟩⟩
end AlgebraicGeometry.ProEtale
