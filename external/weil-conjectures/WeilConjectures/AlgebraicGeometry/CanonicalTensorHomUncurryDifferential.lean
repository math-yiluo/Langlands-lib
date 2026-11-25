/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Differential compatibility of componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-differential).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- The signed chain-map equation transported through the additive tensor-Hom adjunction.
private theorem uncurry_differential {C : Type*} [Category* C] [Preadditive C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    {A A' B B' N N' : C} (a : A ⟶ A') (b : B ⟶ B') (d : N ⟶ N')
    (f : A ⟶ (ihom B).obj N) (f₁ : A' ⟶ (ihom B).obj N')
    (f₂ : A ⟶ (ihom B').obj N') (s : ℤˣ)
    (h : f ≫ (ihom B).map d - s • (f₂ ≫ (MonoidalClosed.pre b).app N') = a ≫ f₁) :
    (β_ A B).hom ≫ MonoidalClosed.uncurry f ≫ d =
      a ▷ B ≫ (β_ A' B).hom ≫ MonoidalClosed.uncurry f₁ +
        s • (A ◁ b ≫ (β_ A B').hom ≫ MonoidalClosed.uncurry f₂) := by
  open MonoidalClosed in
    have hu := congrArg (fun g ↦ (β_ A B).hom ≫ uncurry g) h
    rw [uncurry_sub, uncurry_units_smul, Preadditive.comp_sub,
      Linear.comp_units_smul, uncurry_natural_right, uncurry_pre_app,
      uncurry_natural_left] at hu
    simp only [← BraidedCategory.braiding_naturality_left_assoc,
      ← BraidedCategory.braiding_naturality_right_assoc] at hu
    exact sub_eq_iff_eq_add.mp hu

-- Mathlib's total differential restricted to one tensor summand, with its exact sign.
private theorem tensor_total_d {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
        (HomologicalComplex.mapBifunctor P L (curriedTensor _) (.up ℤ)).d n (n + 1) =
      P.d p (p + 1) ▷ L.X q ≫
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ)
            (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega) +
        p.negOnePow • (P.X p ◁ L.d q (q + 1) ≫
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ)
            p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  let := SheafOfModules.monoidalCategory R
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = n + 1 by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = n + 1 by omega)]
  simp

-- Work with abstract projections so rewrites do not unfold their existence specification.
private theorem graded_uncurry_comm {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P L I H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (π : ∀ (p q n : ℤ), q + p = n → (H.X p ⟶ SheafOfModules.homObj (L.X q) (I.X n)))
    (hπ : ∀ (p q n : ℤ) (h : p + q = n),
      H.d p (p + 1) ≫ π (p + 1) q (n + 1) (by omega) =
        π p q n (by omega) ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (I.d n (n + 1)) -
          p.negOnePow • (π p (q + 1) (n + 1) (by omega) ≫
            SheafOfModules.homObjMap (R := R) (L.d q (q + 1)) (𝟙 _)))
    (φ : P ⟶ H) (n m : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    let U (k : ℤ) := HomologicalComplex.mapBifunctorDesc
      (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
      (j := k) (fun a b h ↦ (β_ (P.X a) (L.X b)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (L.X b) (P.X a) (I.X k)).symm
          (φ.f a ≫ π a b k (by change a + b = k at h; omega)))
    U n ≫ I.d n m =
      (HomologicalComplex.mapBifunctor P L (curriedTensor _) (.up ℤ)).d n m ≫ U m := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed (R := R)
  have : MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  dsimp only
  let U (k : ℤ) := HomologicalComplex.mapBifunctorDesc
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
    (j := k) (fun a b h ↦ (β_ (P.X a) (L.X b)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) (L.X b) (P.X a) (I.X k)).symm
        (φ.f a ≫ π a b k (by change a + b = k at h; omega)))
  change U n ≫ I.d n m = _ ≫ U m
  by_cases hnm : n + 1 = m
  · subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq' : p + q = n := hpq
    have hc := congrArg (fun f ↦ f ≫ π (p + 1) q (n + 1) (by omega))
      (φ.comm p (p + 1))
    simp only [Category.assoc] at hc
    rw [hπ p q n hpq', Preadditive.comp_sub, Linear.comp_units_smul] at hc
    have hu := uncurry_differential (P.d p (p + 1)) (L.d q (q + 1))
      (I.d n (n + 1)) (φ.f p ≫ π p q n (by omega))
      (φ.f (p + 1) ≫ π (p + 1) q (n + 1) (by omega))
      (φ.f p ≫ π p (q + 1) (n + 1) (by omega)) p.negOnePow (by
        rw [SheafOfModules.pre_app (R := R)]
        exact hc)
    rw [← Category.assoc
      (HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n hpq)
      _ (U (n + 1)), tensor_total_d R P L p q n hpq']
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, U,
      HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc]
    simp only [← SheafOfModules.uncurry_eq_tensorHomEquiv_symm (R := R)]
    exact hu
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm]
    simp

-- Specialize to the fixed Hom-complex projections, using the small projection API.
-- Its choice is definitionally the original choice, by proof irrelevance.
private theorem hom_uncurry_comm {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (φ : P ⟶ homComplex (R := R) L I) (n m : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
    let U (k : ℤ) := HomologicalComplex.mapBifunctorDesc
      (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
      (j := k) (fun a b h ↦ (β_ (P.X a) (L.X b)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (L.X b) (P.X a) (I.X k)).symm
          (φ.f a ≫ π L I a b k (by change a + b = k at h; omega)))
    U n ≫ I.d n m =
      (HomologicalComplex.mapBifunctor P L (curriedTensor _) (.up ℤ)).d n m ≫ U m := by
  classical
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
  exact graded_uncurry_comm R P L I (homComplex (R := R) L I) (π L I)
    (fun p q n h ↦ (Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (R := R))).2.1
        L I p (p + 1) q (n + 1) n (q + 1) rfl (by omega) (by omega) (by omega)) φ n m

/-- The actual coproduct extension of the uncurried components in total degree `n`.
Source: Stacks Project, Tag 0A90 (degreewise evaluation).
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
def schemeTensorHomUncurryGraded (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) (n : ℤ) :
    (pullbackTensorTotal X P L).X n ⟶ ((schemeHomKInjectiveResolution X).obj M).X n := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  exact HomologicalComplex.mapBifunctorDesc
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
    (fun p q h ↦ schemeTensorHomUncurryComponent X P L M φ p q n (by
      change p + q = n at h
      omega))

/-- The coproduct evaluation commutes with the total tensor differential.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, differential calculation,
and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-differential).

Proof: Test equality on every coproduct summand P^p tensor L^q, p+q=n.
For m=n+1 the total differential is d_P tensor 1 plus (-1)^p times 1 tensor d_L.
Project the chain-map equation for φ to Hom(L^q,I(M)^m). The Hom differential
projection formula gives d_I φ_p minus (-1)^p φ_p d_L, while the other side is
φ_(p+1) d_P. Apply the sheaf tensor-Hom adjunction and its symmetry to this
identity. Naturality and additivity of the adjunction identify its three terms
with evaluation followed by d_I and the two total differential summands.
Move the signed L term to the other side. The coproduct universal property
then gives the displayed equality. For m different from n+1 both complex
differentials vanish by the shape axiom. This argument applies in all integer
degrees, to unbounded complexes, and also to zero complexes and zero φ. -/
theorem schemeTensorHomUncurryGraded_comm (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) (n m : ℤ) :
    schemeTensorHomUncurryGraded X P L M φ n ≫
        ((schemeHomKInjectiveResolution X).obj M).d n m =
      (pullbackTensorTotal X P L).d n m ≫
        schemeTensorHomUncurryGraded X P L M φ m := by
  exact hom_uncurry_comm X.sheaf P L ((schemeHomKInjectiveResolution X).obj M) φ n m

/-- The chain map obtained by extending evaluation over the tensor coproducts.
Its data are explicit; only differential compatibility uses the preceding theorem.
Source: Stacks Project, Tag 0A90.
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
def schemeTensorHomUncurry (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    pullbackTensorTotal X P L ⟶ (schemeHomKInjectiveResolution X).obj M where
  f := schemeTensorHomUncurryGraded X P L M φ
  comm' n m _ := schemeTensorHomUncurryGraded_comm X P L M φ n m

/-- Restricting coproduct evaluation to a summand recovers exactly the specified component.
Source: Stacks Project, Tag 0A90, coproduct universal property.
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
theorem schemeTensorHomUncurry_component (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
        (schemeTensorHomUncurry X P L M φ).f n =
      schemeTensorHomUncurryComponent X P L M φ p q n h' := by
  let _ := SheafOfModules.monoidalCategory X.sheaf
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
    (fun p q h ↦ schemeTensorHomUncurryComponent X P L M φ p q n (by
      change p + q = n at h
      omega)) p q h

end AlgebraicGeometry
