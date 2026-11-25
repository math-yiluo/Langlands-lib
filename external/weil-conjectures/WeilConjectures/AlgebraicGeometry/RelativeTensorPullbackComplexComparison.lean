/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
import WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackBalancedNaturality
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Balanced tensor pullback for ordinary complexes

Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.
(blueprint: lem-pc-relative-tensor-pullback-complex-comparison)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

noncomputable local instance complexComparisonModuleTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf


/-- The balanced module tensor identity extends to total complexes after forgetting
scalars. No K-flatness, quasi-isomorphism or derived category occurs in this statement.
Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.

Proof: in bidegree (p,q), identify
A^p tensor over O_X (O_X tensor over f-inverse O_S f-inverse L^q)
with A^p restricted to f-inverse O_S tensor f-inverse L^q by
 a tensor (b tensor l) maps to (b*a) tensor l; the inverse sends
 a tensor l to a tensor (1 tensor l). The balancing relations prove
well-definedness and the two inverse identities. These identities on sections
commute with restrictions, so they sheafify to module tensor isomorphisms.
Naturality in both factors makes them commute with the two differentials.
In total degree n both sides use the coproduct over p+q=n, and the second
differential has the same sign (-1)^p. Forgetting scalars preserves these
coproducts. Taking the coproduct of the summand isomorphisms in each degree
therefore gives mutually inverse chain maps of abelian sheaves. No bound on
A or L is needed; zero modules and empty schemes satisfy the same identities.
(blueprint: lem-pc-relative-tensor-pullback-complex-comparison) -/
theorem relativeTensorPullback_complex_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
    (hGmap : ∀ {M N} (a : M ⟶ N),
      G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm)
    [G.Additive]
    (A : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    Nonempty
      (((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor A
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))) ≅
        ((SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
          (CochainComplex.mapBifunctor
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj A)
            (((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L)
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))))) := by
  let R := ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
  let U := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let V := SheafOfModules.toSheaf R
  let H := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
  let T := @curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)
  let T' := @curriedTensor _ _ (SheafOfModules.monoidalCategory
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
  let B := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
    ((G.mapHomologicalComplex (.up ℤ)).obj L)
  let B' := ((T'.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
    ((H.mapHomologicalComplex (.up ℤ)).obj A)).obj
      ((I.mapHomologicalComplex (.up ℤ)).obj L)
  have : U.PreservesTotalComplex B (.up ℤ) := fun _ ↦ inferInstance
  have : V.PreservesTotalComplex B' (.up ℤ) := fun _ ↦ inferInstance
  obtain ⟨e, h₁, h₂⟩ := exists_relativeTensorPullback_balanced_natural f G hG hGmap
  let eB : ((U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj B) ≅
      ((V.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj B') :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ e (A.X p) (L.X q)) (by
          intro q q' hq
          exact (h₂ (A.X p) (L.X q) (L.X q') (L.d q q')).symm)) (by
        intro p p' hp
        ext1 q
        exact (h₁ (A.X p) (A.X p') (A.d p p') (L.X q)).symm)
  exact ⟨(HomologicalComplex₂.mapTotalIso U B (.up ℤ)).symm ≪≫
    HomologicalComplex₂.total.mapIso eB (.up ℤ) ≪≫
      HomologicalComplex₂.mapTotalIso V B' (.up ℤ)⟩

end AlgebraicGeometry.Scheme
