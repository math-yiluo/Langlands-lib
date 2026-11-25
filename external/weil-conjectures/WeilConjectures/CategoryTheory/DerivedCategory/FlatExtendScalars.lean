/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChange

/-!
# Extension of scalars along a flat ring morphism on derived categories

Let `f : R →+* S` be a flat morphism of commutative rings. Extension of scalars
`S ⊗_R - : ModuleCat R ⥤ ModuleCat S` is exact, so it induces a triangulated functor
`ModuleCat.derivedExtendScalars f hf : D(R) ⥤ D(S)` which commutes with cohomology. It carries
`Dᵇ_fg(R)` into `Dᵇ_fg(S)`, and the multiplication by `r : R` to the multiplication by `f r`.

## Main definitions and statements

- `CategoryTheory.Functor.mapDerivedCategory_map_smul_id`: an exact functor sending the
  multiplication by `r` to the multiplication by `s` does so on derived categories.
- `ModuleCat.derivedExtendScalars`: the functor `D(R) ⥤ D(S)`.
- `ModuleCat.derivedExtendScalars_map_smul_id`: it sends `r • 𝟙` to `f r • 𝟙`.
- `ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj`: it preserves `Dᵇ_fg`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {R S : Type*} [Ring R] [Ring S] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear S C₂]

/-- If an exact functor `F` sends the multiplication by `r` on every object to the
multiplication by `s`, so does the induced functor on derived categories. -/
lemma mapDerivedCategory_map_smul_id {r : R} {s : S}
    (h : ∀ M : C₁, F.map (r • 𝟙 M) = s • 𝟙 (F.obj M)) (X : DerivedCategory C₁) :
    F.mapDerivedCategory.map (r • 𝟙 X) = s • 𝟙 (F.mapDerivedCategory.obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  have h₁ : r • 𝟙 X = e.inv ≫ DerivedCategory.Q.map (r • 𝟙 K) ≫ e.hom := by
    rw [Functor.map_smul, Functor.map_id, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
      e.inv_hom_id]
  have h₂ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 K) = s • 𝟙 _ := by
    ext n
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.smul_f_apply,
      HomologicalComplex.id_f]
    exact h (K.X n)
  have key : F.mapDerivedCategory.map (DerivedCategory.Q.map (r • 𝟙 K)) = s • 𝟙 _ := by
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app K),
      mapDerivedCategoryFactors_hom_naturality, h₂, Functor.map_smul, Functor.map_id]
    simp
  rw [h₁, Functor.map_comp, Functor.map_comp, key, Linear.smul_comp, Category.id_comp,
    Linear.comp_smul, ← Functor.map_comp, e.inv_hom_id, Functor.map_id]

end CategoryTheory.Functor

namespace ModuleCat

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (f : R →+* S)

open ChangeOfRings

/-- Extension of scalars sends the multiplication by `r` to the multiplication by `f r`. -/
lemma extendScalars_map_smul_id (r : R) (M : ModuleCat.{u + 1} R) :
    (extendScalars.{u + 1, u + 1, u + 1} f).map (r • 𝟙 M) =
      f r • 𝟙 ((extendScalars.{u + 1, u + 1, u + 1} f).obj M) := by
  ext m
  change (1 : S) ⊗ₜ[R, f] (r • m) = f r • ((1 : S) ⊗ₜ[R, f] m)
  rw [ExtendScalars.smul_tmul]
  exact (TensorProduct.smul_tmul (R := R) (M := (restrictScalars f).obj (of S S)) r (1 : S) m).symm

variable (hf : f.Flat)

/-- The extension of scalars `D(R) ⥤ D(S)` along a flat ring morphism `f : R →+* S`, induced by
the exact functor `S ⊗_R -`. -/
noncomputable def derivedExtendScalars :
    DerivedCategory (ModuleCat.{u + 1} R) ⥤ DerivedCategory (ModuleCat.{u + 1} S) :=
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  (extendScalars.{u + 1, u + 1, u + 1} f).mapDerivedCategory

noncomputable instance : (derivedExtendScalars f hf).CommShift ℤ := by
  unfold derivedExtendScalars
  infer_instance

instance : (derivedExtendScalars f hf).IsTriangulated := by
  unfold derivedExtendScalars
  infer_instance

/-- The derived extension of scalars sends the multiplication by `r` to the multiplication by
`f r`. -/
lemma derivedExtendScalars_map_smul_id (r : R) (X : DerivedCategory (ModuleCat.{u + 1} R)) :
    (derivedExtendScalars f hf).map (r • 𝟙 X) = f r • 𝟙 ((derivedExtendScalars f hf).obj X) :=
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  (extendScalars.{u + 1, u + 1, u + 1} f).mapDerivedCategory_map_smul_id
    (extendScalars_map_smul_id f r) X

/-- The derived extension of scalars is semilinear along `f`. -/
lemma derivedExtendScalars_map_smul (r : R) {X Y : DerivedCategory (ModuleCat.{u + 1} R)}
    (φ : X ⟶ Y) :
      (derivedExtendScalars f hf).map (r • φ) = f r • (derivedExtendScalars f hf).map φ := by
  rw [show r • φ = (r • 𝟙 X) ≫ φ by rw [Linear.smul_comp, Category.id_comp], Functor.map_comp,
    derivedExtendScalars_map_smul_id, Linear.smul_comp, Category.id_comp]

/-- The derived extension of scalars commutes with cohomology. -/
noncomputable def derivedExtendScalarsHomologyIso (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u + 1} R)) :
    (extendScalars.{u + 1, u + 1, u + 1} f).obj
        ((DerivedCategory.homologyFunctor _ n).obj X) ≅
      (DerivedCategory.homologyFunctor _ n).obj ((derivedExtendScalars f hf).obj X) :=
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  ((extendScalars.{u + 1, u + 1, u + 1} f).mapDerivedCategoryHomologyFunctorIso n).app X

/-- The derived extension of scalars carries `Dᵇ_fg(R)` into `Dᵇ_fg(S)`. -/
lemma boundedFiniteCohomology_derivedExtendScalars_obj
    {X : DerivedCategory (ModuleCat.{u + 1} R)}
    (hX : DerivedCategory.boundedFiniteCohomology R X) :
    DerivedCategory.boundedFiniteCohomology S ((derivedExtendScalars f hf).obj X) := by
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  refine ⟨(extendScalars.{u + 1, u + 1, u + 1} f).bounded_mapDerivedCategory_obj hX.1,
    fun n ↦ ?_⟩
  have := hX.2 n
  have : Module.Finite S ((extendScalars.{u + 1, u + 1, u + 1} f).obj
      ((DerivedCategory.homologyFunctor _ n).obj X)) := by
    let := f.toAlgebra
    exact inferInstanceAs (Module.Finite S (TensorProduct R S _))
  exact Module.Finite.equiv (derivedExtendScalarsHomologyIso f hf n X).toLinearEquiv

end ModuleCat
