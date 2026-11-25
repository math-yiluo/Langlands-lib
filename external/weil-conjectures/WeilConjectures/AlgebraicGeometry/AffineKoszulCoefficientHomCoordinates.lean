/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.AffineClosedImmersionCoefficientSquare
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomCoefficientHomologySquare

/-! # Underived affine coordinates for the Koszul coefficient square

Source: Stacks Project, Tag 0BQZ, the map between the two Hom complexes. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem transport_coefficient_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y V W : C} (a : X ⟶ Y) (q : V ⟶ W) (b : X ≅ V) (c : Y ≅ W)
    (hb : a ≫ c.hom = b.hom ≫ q) {P Q : D}
    (d : F.obj V ≅ P) (e : F.obj W ≅ Q) (t : P ⟶ Q)
    (hc : F.map q ≫ e.hom = d.hom ≫ t) :
    ∃ (bO : F.obj X ≅ P) (bQ : F.obj Y ≅ Q),
      F.map a ≫ bQ.hom = bO.hom ≫ t := by
  refine ⟨F.mapIso b ≪≫ d, F.mapIso c ≪≫ e, ?_⟩
  have sq₁ : CommSq (F.map a) (F.map b.hom) (F.map c.hom) (F.map q) :=
    ⟨(F.map_comp _ _).symm.trans
      ((congrArg (fun t ↦ F.map t) hb).trans (F.map_comp _ _))⟩
  have sq₂ : CommSq (F.map q) d.hom e.hom t := ⟨hc⟩
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using (sq₁.vert_comp sq₂).w


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_coefficient_coordinates_for_H
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (n m : ℕ) (f : Fin n → Γ(Y, U.1))
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom)
    (H : CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ)
    (hH : H =
      let A := (Γ(Y, U.1) : Type u)
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
      let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
      (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let R := Scheme.Modules.restrictFunctor U.1.ι
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let D := HomologicalComplex.homologyFunctor U.1.toScheme.Modules
      (ComplexShape.up ℤ) (m : ℤ)
    let P := (ExteriorAlgebra.koszulDualComplex A n f).homology m
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m
    let q := HomologicalComplex.homologyMap
      (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m
    ∃ (eF : D.obj (H.obj (S.obj (R.obj (SheafOfModules.unit Y.ringCatSheaf)))) ≅ T.obj P)
      (eG : D.obj (H.obj (S.obj (R.obj B))) ≅ T.obj Q),
      D.map (H.map (S.map (R.map a))) ≫ eG.hom = eF.hom ≫ T.map q := by
  let A := (Γ(Y, U.1) : Type u)
  let I := i.ker.ideal U
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let R := Scheme.Modules.restrictFunctor U.1.ι
  let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
  let D := HomologicalComplex.homologyFunctor U.1.toScheme.Modules
    (ComplexShape.up ℤ) (m : ℤ)
  let G := S ⋙ H ⋙ D
  obtain ⟨eO, eB, hb⟩ := affine_closedImmersion_coefficient_square i U a ha
  obtain ⟨cO, cQ, hc⟩ := affine_koszul_hom_coefficient_homology_square U I n m f H hH
  exact transport_coefficient_square G (R.map a)
    (T.map (ModuleCat.ofHom I.mkQ)) eO eB hb cO cQ _ hc


/-- The underived Hom complexes of the explicit sheafified Koszul complex give
precisely the coefficient reduction on dual Koszul homology.
Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5, the displayed map of
Hom complexes; Tag 01HV, exactness of associated sheafification.
(blueprint: lem-sc-affine-koszul-coefficient-hom-coordinates).

Proof: Identify the restriction of i_*O_Z with the associated sheaf of A/I,
where A = Gamma(Y,U) and I = ker(i)(U), using the affine quotient presentation.
Identify the restricted structure sheaf with the associated sheaf of A. On each
basic open, the adjunction unit is the localized quotient map A_g -> (A/I)_g;
the hypothesis ha therefore identifies the coefficient map under these two
identifications. In Hom degree k the coefficient single complex has only its
zero term. Projection to source degree -k identifies the Hom term with internal
Hom from the sheafification of wedge^k(A^n) to the coefficient sheaf. The finite
wedge basis identifies this with the associated sheaf of the corresponding
module Hom, by localization of the functional's values. The identifications
commute with the coefficient quotient map, since both maps reduce these values.
The source differential acts by precomposition multiplied by -(-1)^k, which is
(-1)^(k+1); the coefficient differentials are zero. Thus the identifications
form a commuting square of integer-indexed complexes. Tilde and chart transport
are exact, so their homology comparison is natural in this square. Finally the
extension from natural to integer cochain degrees has its canonical natural
homology comparison at m. Compose these comparisons to obtain the two stated
isomorphisms and their square. This argument does not use Koszul regularity,
ideal generation by f, or any derived category. For n=0 the complexes have only
degree zero; for m>n their homology vanishes; zero rings and empty charts give
the unique maps of zero objects. -/
theorem affine_koszul_coefficient_hom_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (n m : ℕ) (f : Fin n → Γ(Y, U.1))
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let R := Scheme.Modules.restrictFunctor U.1.ι
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
    let H := (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)
    let D := HomologicalComplex.homologyFunctor U.1.toScheme.Modules
      (ComplexShape.up ℤ) (m : ℤ)
    let P := (ExteriorAlgebra.koszulDualComplex A n f).homology m
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m
    let q := HomologicalComplex.homologyMap
      (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m
    ∃ (eF : D.obj (H.obj (S.obj (R.obj (SheafOfModules.unit Y.ringCatSheaf)))) ≅ T.obj P)
      (eG : D.obj (H.obj (S.obj (R.obj B))) ≅ T.obj Q),
      D.map (H.map (S.map (R.map a))) ≫ eG.hom = eF.hom ≫ T.map q := by
  exact affine_coefficient_coordinates_for_H i U n m f a ha _ rfl

end AlgebraicGeometry
