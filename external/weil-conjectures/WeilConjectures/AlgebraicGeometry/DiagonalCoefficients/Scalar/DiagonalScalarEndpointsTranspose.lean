/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRealizedEndpointTranspose

/-! # Normalized scalar endpoint composition

Source: the exact functor single comparisons and adjunction triangle identities.
(blueprint: lem-diagonal-scalar-endpoints-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local irreducible] Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive
open RootEndpointTranspose RootEndpointTranspose.ShiftHelpers

private theorem shifted_composition
    {C D K : Type*} [Category C] [Category D] [Category K]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift K ℤ]
    (F : C ⥤ D) (G : D ⥤ K) [F.CommShift ℤ] [G.CommShift ℤ]
    {M : C} {N : D} {P : K} (f : F.obj M ⟶ N) (g : G.obj N ⟶ P) (k : ℤ) :
    G.map ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (G.commShiftIso k).hom.app N ≫ g⟦k⟧' =
      ((F ⋙ G).commShiftIso k).hom.app M ≫ (G.map f ≫ g)⟦k⟧' := by
  simp only [Functor.map_comp, Functor.commShiftIso_comp_hom_app,
    (shiftFunctor K k).map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]

/-- Degree-zero scalar endpoint normalizations compose under the actual adjunction.
Source: diagonal tower coefficient changes (1), successive scalar extension
(blueprint: lem-diagonal-scalar-endpoints-transpose).
Proof: expand the collected-right composite adjunction. Apply exact-single
transposition of composite adjunctions to the two endpoint normalizations. Naturality
of the exact single comparison combines the two ordinary semilinear insertions. -/
theorem scalarEndpoints_transpose
    {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
    [MonObj R₂] [IsCommMonObj R₂]
    {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
    {Y : Scheme.{u}}
    {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
    {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
    {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
    {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
    {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
    {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
    (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂) :
    (ScalarCompatibility.compositeAdjunction s t).homEquiv _ _
      ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫ t.lineW.iso.hom) =
      (DerivedCategory.singleFunctor _ 0).map
        (s.lineW.semilinear.hom ≫
          (Mod.comap (coefficientMap a (diagonalSurface Y))).map t.lineW.semilinear.hom) ≫
        ((ScalarCompatibility.compositeRestriction s t).mapDerivedCategorySingleFunctor 0).inv.app
          (L₂ (diagonalSurface Y)) := by
  unfold ScalarCompatibility.compositeAdjunction
  exact composite_single_transpose
    (Mod.comap (coefficientMap a (diagonalSurface Y)))
    (Mod.comap (coefficientMap b (diagonalSurface Y)))
    (ScalarCompatibility.scalarAdjunction a (diagonalSurface Y))
    (ScalarCompatibility.scalarAdjunction b (diagonalSurface Y))
    s.lineW.iso.hom t.lineW.iso.hom s.lineW.semilinear.hom t.lineW.semilinear.hom
    (compatibilityEndpoint_transpose a s.lineW) (compatibilityEndpoint_transpose b t.lineW)

/-- Successive scalar endpoint shifts form the shift of the degree-zero composite.
Source: diagonal tower coefficient changes (1), exact shift comparisons
(blueprint: lem-diagonal-scalar-endpoints-transpose).
Proof: unfold the two shifted endpoints and the composite target, and apply
naturality of the second functor's shift comparison to the first endpoint. -/
theorem scalarEndpoints_shift
    {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
    [MonObj R₂] [IsCommMonObj R₂]
    {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
    {Y : Scheme.{u}}
    {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
    {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
    {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
    {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
    {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
    {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
    (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂) :
    ScalarCompatibility.compositeTarget s t =
      ((ScalarCompatibility.compositeFunctor s t).commShiftIso (2 : ℤ)).hom.app _ ≫
        ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫
          t.lineW.iso.hom)⟦(2 : ℤ)⟧' := by
  unfold ScalarCompatibility.compositeTarget Endpoint.shift
  exact shifted_composition (derivedScalars a (diagonalSurface Y))
    (derivedScalars b (diagonalSurface Y)) s.lineW.iso.hom t.lineW.iso.hom (2 : ℤ)

/-- Successive scalar normalizations prescribe the endpoint after finite realization.
Source: diagonal tower coefficient changes (1), root insertion normalization
(blueprint: lem-diagonal-scalar-endpoints-transpose).
Proof: compose the two scalar endpoint normalizations, then transpose through finite
realization. Substitute the supplied equality of ordinary insertions before forming
the exact single comparison, so the resulting formula uses its prescribed insertion. -/
theorem scalarRealizedEndpoints_transpose
    {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
    [MonObj R₂] [IsCommMonObj R₂]
    {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
    {Y : Scheme.{u}}
    {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
    {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
    {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
    {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
    {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
    {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
    (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂)
    {B : Type (u + 1)} [CommRing B]
    (e : FiniteRealization R₂ B (diagonalSurface Y))
    {P : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} B)}
    (i : e.F.obj (L₂ (diagonalSurface Y)) ≅ P)
    (w : L₀ (diagonalSurface Y) ⟶
      (e.F.asEquivalence.inverse ⋙ ScalarCompatibility.compositeRestriction s t).obj P)
    (hw : (s.lineW.semilinear.hom ≫
        (Mod.comap (coefficientMap a (diagonalSurface Y))).map t.lineW.semilinear.hom) ≫
      (ScalarCompatibility.compositeRestriction s t).map
        (e.rootInsertion (L₂ (diagonalSurface Y)) i) = w) :
    (((ScalarCompatibility.compositeAdjunction s t).comp
      (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
        (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse
          (ScalarCompatibility.compositeRestriction s t))).homEquiv _ _
      (e.F.mapDerivedCategory.map
          ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫ t.lineW.iso.hom) ≫
        (e.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map i.hom) =
      (DerivedCategory.singleFunctor _ 0).map w ≫
        ((e.F.asEquivalence.inverse ⋙
          ScalarCompatibility.compositeRestriction s t).mapDerivedCategorySingleFunctor
            0).inv.app P := by
  exact realizedEndpoint_transpose_eq e (ScalarCompatibility.compositeRestriction s t)
    (ScalarCompatibility.compositeAdjunction s t)
    ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫ t.lineW.iso.hom)
    (s.lineW.semilinear.hom ≫
      (Mod.comap (coefficientMap a (diagonalSurface Y))).map t.lineW.semilinear.hom)
    (scalarEndpoints_transpose s t) i w hw

/-- Finite realization preserves the successive shifted endpoint normalization.
Source: diagonal tower coefficient changes (1), exact shift comparisons
(blueprint: lem-diagonal-scalar-endpoints-transpose).
Proof: rewrite the successive scalar endpoint as its degree-zero shift, then apply
finite realization shift naturality to collect the composite shift comparison. -/
theorem scalarRealizedEndpoints_shift
    {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
    [MonObj R₂] [IsCommMonObj R₂]
    {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
    {Y : Scheme.{u}}
    {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
    {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
    {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
    {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
    {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
    {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
    (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂)
    {B : Type (u + 1)} [CommRing B]
    (e : FiniteRealization R₂ B (diagonalSurface Y))
    {P : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} B)}
    (i : e.F.obj (L₂ (diagonalSurface Y)) ≅ P) :
    finiteTargetMap e (ScalarCompatibility.compositeTarget s t) i =
      (((ScalarCompatibility.compositeFunctor s t) ⋙
        e.F.mapDerivedCategory).commShiftIso (2 : ℤ)).hom.app _ ≫
      (e.F.mapDerivedCategory.map
          ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫ t.lineW.iso.hom) ≫
        (e.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map i.hom)⟦(2 : ℤ)⟧' := by
  exact (congrArg (fun f ↦ finiteTargetMap e f i) (scalarEndpoints_shift s t)).trans
    (realizedEndpoint_shift e (ScalarCompatibility.compositeFunctor s t)
      ((derivedScalars b (diagonalSurface Y)).map s.lineW.iso.hom ≫ t.lineW.iso.hom) i)

attribute [local semireducible] ScalarCompatibility.scalarAdjunction
  UniformizerSquareData.scalarAdjunction

/-- The actual scalar and finite composite adjunction commutes with shifts.
Source: diagonal tower coefficient changes (1), exact derived adjunctions
(blueprint: lem-diagonal-scalar-endpoints-transpose).
Proof: the two scalar adjunctions and the finite equivalence adjunction commute
with shifts. Compose these structures and transport the result across the exact
right-functor composition comparison. -/
theorem scalarRealizedAdjunction_commShift
    {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
    [MonObj R₂] [IsCommMonObj R₂]
    {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
    {Y : Scheme.{u}}
    {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
    {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
    {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
    {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
    {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
    {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
    (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂)
    {B : Type (u + 1)} [CommRing B]
    (e : FiniteRealization R₂ B (diagonalSurface Y)) :
    (((ScalarCompatibility.compositeAdjunction s t).comp
      (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
        (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse
          (ScalarCompatibility.compositeRestriction s t))).CommShift ℤ := by
  let : (ScalarCompatibility.scalarAdjunction a (diagonalSurface Y)).CommShift ℤ :=
    scalarAdjunction_commShift _ _
  let : (ScalarCompatibility.scalarAdjunction b (diagonalSurface Y)).CommShift ℤ :=
    scalarAdjunction_commShift _ _
  let : (ScalarCompatibility.compositeAdjunction s t).CommShift ℤ := by
    unfold ScalarCompatibility.compositeAdjunction
    exact rightIso_commShift _ _ (by infer_instance)
  let : (UniformizerSquareData.finiteAdjunction e).CommShift ℤ :=
    finiteAdjunction_commShift _
  have hcomp : ((ScalarCompatibility.compositeAdjunction s t).comp
      (UniformizerSquareData.finiteAdjunction e)).CommShift ℤ := by
    convert Adjunction.CommShift.instComp (ScalarCompatibility.compositeAdjunction s t) ℤ
      (UniformizerSquareData.finiteAdjunction e) using 1
  exact rightIso_commShift _
    (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse
      (ScalarCompatibility.compositeRestriction s t)) hcomp

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
