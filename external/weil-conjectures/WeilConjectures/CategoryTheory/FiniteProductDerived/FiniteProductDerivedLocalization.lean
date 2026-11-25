/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived localization of an exact finite-product equivalence

Source: Stacks Project, Tags 015F and 05RU.
(blueprint: lem-pur-exact-finite-product-derived-equivalence)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors
namespace CategoryTheory.FiniteProductDerived

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

private def tupleComplex : (∀ i, CochainComplex (B i) ℤ) ⥤ CochainComplex A ℤ where
  obj P :=
    { X n := G.obj (fun i ↦ (P i).X n)
      d n m := G.map (fun i ↦ (P i).d n m)
      shape n m h := by
        have he : (fun i ↦ (P i).d n m) = (fun i ↦ (0 : (P i).X n ⟶ (P i).X m)) := by
          funext i
          exact (P i).shape n m h
        rw [he, hzero]
      d_comp_d' n m k _ _ := by
        rw [← G.map_comp]
        have he : (fun i ↦ (P i).d n m ≫ (P i).d m k) =
            (fun i ↦ (0 : (P i).X n ⟶ (P i).X k)) := by
          funext i
          exact (P i).d_comp_d n m k
        change G.map (fun i ↦ (P i).d n m ≫ (P i).d m k) = 0
        rw [he, hzero] }
  map f :=
    { f n := G.map (fun i ↦ (f i).f n)
      comm' n m _ := by
        rw [← G.map_comp, ← G.map_comp]
        congr 1
        funext i
        exact (f i).comm n m }
  map_id P := by
    ext n
    exact G.map_id _
  map_comp f g := by
    ext n
    exact G.map_comp _ _

private def tupleUnit : 𝟭 (CochainComplex A ℤ) ≅
    Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ)) ⋙ tupleComplex G hzero :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ η.app (P.X n)) (by
      intro n m _
      exact (η.hom.naturality (P.d n m)).symm)) (by
    intro P Q f
    ext n
    exact η.hom.naturality (f.f n))

private def tupleCounit : tupleComplex G hzero ⋙
    Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ Pi.isoMk (fun i ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Pi.eval _ i).mapIso (ε.app (fun k ↦ (P k).X n))) (by
      intro n m _
      exact (congrFun (ε.hom.naturality (fun k ↦ (P k).d n m)) i).symm))) (by
    intro P Q f
    funext i
    ext n
    exact congrFun (ε.hom.naturality (fun k ↦ (f k).f n)) i)

private def tupleEquivalence : CochainComplex A ℤ ≌ (∀ i, CochainComplex (B i) ℤ) :=
  CategoryTheory.Equivalence.mk _ _ (tupleUnit r G hzero η) (tupleCounit r G hzero ε)

include G hzero η ε in
/-- Localize an exact finite-product equivalence coordinatewise.
Source: Stacks Project, Tags 015F and 05RU, finite-product localization calculation
(blueprint: lem-pur-exact-finite-product-derived-equivalence).

Proof: form the inverse complex degreewise with the given zero-preserving inverse functor.
The unit and counit make it inverse to the tuple of exact complex restrictions. Joint
reflection of isomorphisms, the exact-derived factorization, and the localization test
identify the source quasi-isomorphisms with the coordinate quasi-isomorphisms. Descend
both directions through the product localization. The localized unit and counit give
the derived tuple functor an equivalence structure. No boundedness is used. -/
theorem derivedPi_isEquivalence
    (hr : JointlyReflectIsomorphisms r) :
    (Functor.pi' (fun i ↦ (r i).mapDerivedCategory)).IsEquivalence := by
  let rc := Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ))
  let rd := Functor.pi' (fun i ↦ (r i).mapDerivedCategory)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Wi := MorphismProperty.pi (fun i ↦ HomologicalComplex.quasiIso (B i) (.up ℤ))
  let Qi := Functor.pi (fun i ↦ (DerivedCategory.Q : CochainComplex (B i) ℤ ⥤ _))
  let E := tupleEquivalence r G hzero η ε
  have hd := Functor.jointlyReflectIsomorphisms_mapDerivedCategory hr
  have hrc {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
      W f ↔ Wi (rc.map f) := by
    change QuasiIso f ↔
      ∀ i, QuasiIso (((r i).mapHomologicalComplex (.up ℤ)).map f)
    change QuasiIso f ↔ ∀ i, QuasiIso _
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso A f]
    simp_rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    rw [hd.isIso_iff]
    exact forall_congr' fun i ↦
      NatIso.isIso_map_iff (r i).mapDerivedCategoryFactors f
  have hinv : Wi.IsInvertedBy (E.inverse ⋙ DerivedCategory.Q) := by
    intro P Q f hf
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mpr
    apply (hrc (E.inverse.map f)).mpr
    intro i
    let e := (Pi.eval _ i).mapIso (E.counitIso.app P)
    let e' := (Pi.eval _ i).mapIso (E.counitIso.app Q)
    have hn : ((r i).mapHomologicalComplex (.up ℤ)).map (E.inverse.map f) ≫ e'.hom =
        e.hom ≫ f i := congrFun (E.counitIso.hom.naturality f) i
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk e e' hn.symm)).mpr (hf i)
  let Gd := Localization.lift (E.inverse ⋙ DerivedCategory.Q) hinv Qi
  let α : DerivedCategory.Q ⋙ rd ≅ rc ⋙ Qi :=
    NatIso.pi' (fun i ↦ (r i).mapDerivedCategoryFactors)
  let β : (E.inverse ⋙ DerivedCategory.Q) ⋙ rd ≅ Qi :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso Qi ≪≫ Functor.leftUnitor Qi
  let γ : (rc ⋙ Qi) ⋙ Gd ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft rc (Localization.fac (E.inverse ⋙ DerivedCategory.Q) hinv Qi) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q
  let : Localization.Lifting DerivedCategory.Q W (rc ⋙ Qi) rd := ⟨α⟩
  exact Localization.isEquivalence DerivedCategory.Q W Qi Wi (rc ⋙ Qi) rd
    (E.inverse ⋙ DerivedCategory.Q) Gd γ β

end DerivedPi

end CategoryTheory.FiniteProductDerived
