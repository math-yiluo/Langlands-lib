/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Presentations of ringed tensor squares

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D and 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option linter.checkUnivs false in
/-- A small ringed site and a model of its derived tensor on flat K-flat representatives.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
structure RingedTensorCorner where
  site : Type u
  [category : Category.{u} site]
  topology : GrothendieckTopology site
  ring : Sheaf topology CommRingCat.{u}
  [derived : HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))]
  tensor : (DerivedCategory (SheafOfModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))) ×
    (DerivedCategory (SheafOfModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))) ⥤
    DerivedCategory (SheafOfModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))

attribute [instance] RingedTensorCorner.category RingedTensorCorner.derived

/-- The representative identification specifying the derived tensor functor.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
structure RingedTensorModel (A : RingedTensorCorner.{u, w}) where
  representative : ((ObjectProperty.ι (fun P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧
      ∀ n : ℤ, (P.X n).IsFlat : ObjectProperty _)).prod (ObjectProperty.ι (fun P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      A.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat : ObjectProperty _))) ⋙
    Functor.uncurry.obj
      ((@MonoidalCategory.curriedTensor (SheafOfModules.{u} ((sheafCompose A.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj A.ring)) _ (monoidalCategory A.ring)).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    (((ObjectProperty.ι (fun P : CochainComplex (SheafOfModules.{u} ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧
      ∀ n : ℤ, (P.X n).IsFlat
      : ObjectProperty _)) ⋙ DerivedCategory.Q).prod
      ((ObjectProperty.ι (fun P : CochainComplex (SheafOfModules.{u} ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧
      ∀ n : ℤ, (P.X n).IsFlat
      : ObjectProperty _)) ⋙ DerivedCategory.Q)) ⋙ A.tensor

/-- A ringed-topos inverse image and its total derived module pullback. All comparisons
are the existing canonical comparisons, with no chosen arbitrary tensor isomorphism.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
structure RingedTensorEdge (A B : RingedTensorCorner.{u, w}) where
  inverse : Sheaf A.topology (Type u) ⥤ Sheaf B.topology (Type u)
  direct : Sheaf B.topology (Type u) ⥤ Sheaf A.topology (Type u)
  adjunction : inverse ⊣ direct
  [finiteLimits : PreservesFiniteLimits inverse]
  inverseRing : Sheaf B.topology CommRingCat.{u}
  algebraic : AlgebraicInverseImage inverse A.ring inverseRing
  ringMap : inverseRing ⟶ B.ring
  pullback : SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A.ring) ⥤ SheafOfModules.{u} ((sheafCompose B.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj B.ring)
  object_eq : ∀ M, pullback.obj M = changeOfRings ringMap (algebraic.modules.obj M)
  map_eq : ∀ {M N : SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A.ring)} (a : M ⟶ N),
    pullback.map a = eqToHom (object_eq M) ≫
      changeOfRingsHom ringMap (algebraic.modules.obj M) (algebraic.modules.map a) ≫
      eqToHom (object_eq N).symm
  [additive : pullback.Additive]
  ordinaryTensor : CanonicalRingedTensorComparison A.ring B.ring inverseRing inverse algebraic
    ringMap pullback object_eq
  pushforward : SheafOfModules.{u} ((sheafCompose B.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj B.ring) ⥤ SheafOfModules.{u} ((sheafCompose A.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj A.ring)
  moduleAdjunction : pullback ⊣ pushforward
  left : DerivedCategory (SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A.ring)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose B.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj B.ring))
  epsilon : DerivedCategory.Qh ⋙ left ⟶
    pullback.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  isLeftDerived : left.IsLeftDerivedFunctor epsilon
    (HomotopyCategory.quasiIso (SheafOfModules.{u} ((sheafCompose A.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj A.ring)) (ComplexShape.up ℤ))
  right : DerivedCategory (SheafOfModules.{u} ((sheafCompose B.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj B.ring)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))
  derivedAdjunction : left ⊣ right

attribute [instance] RingedTensorEdge.finiteLimits RingedTensorEdge.additive

/-- The canonical derived tensor comparison from its unique representative characterization.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
noncomputable def RingedTensorEdge.tensorComparison
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (a : RingedTensorModel A) (b : RingedTensorModel B) :
    A.tensor ⋙ e.left ≅ (e.left.prod e.left) ⋙ B.tensor :=
  ringedTopoiCanonicalDerivedTensorComparison e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived
    (fun P : CochainComplex (SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat
      : ObjectProperty _) (fun
      P : CochainComplex (SheafOfModules.{u} ((sheafCompose B.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj B.ring)) ℤ ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat
      : ObjectProperty _) (fun
      _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    A.tensor B.tensor a.representative b.representative e.ordinaryTensor
    e.pushforward e.moduleAdjunction

/-- The canonical map of underlying sheaves m ↦ 1 tensor m, after inverse image.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
noncomputable def RingedTensorEdge.insertion
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (M : SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      A.ring)) :
    e.inverse.obj ((toSheaf ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      A.ring) ⋙ sheafCompose A.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
      (toSheaf ((sheafCompose B.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj B.ring) ⋙
      sheafCompose B.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj (e.pullback.obj M) :=
  e.algebraic.moduleUnderlying.inv.app M ≫ e.ordinaryTensor.q M

/-- A commutation isomorphism of ringed topoi, presented by its set-sheaf square and
its linear module comparison. The insertion equation fixes the latter on generators,
and linearity enforces compatibility with the structural ring maps. No tensor or
derived coherence equation is assumed.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation). -/
structure RingedTensorSquare
    (Y X Y' X' : RingedTensorCorner.{u, w})
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Y Y')
    (h : RingedTensorEdge X X') (k : RingedTensorEdge Y' X') where
  sets : g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse
  modules : g.pullback ⋙ k.pullback ≅ f.pullback ⋙ h.pullback
  insertion : ∀ M : SheafOfModules.{u} ((sheafCompose Y.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj Y.ring),
    k.inverse.map (g.insertion M) ≫ k.insertion (g.pullback.obj M) ≫
      (toSheaf ((sheafCompose X'.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X'.ring) ⋙
      sheafCompose X'.topology (CategoryTheory.forget AddCommGrpCat.{u})).map (modules.hom.app M) =
    sets.hom.app ((toSheaf ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      Y.ring) ⋙ sheafCompose Y.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
      h.inverse.map (f.insertion M) ≫ h.insertion (f.pullback.obj M)

end SheafOfModules
