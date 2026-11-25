/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Natural endomorphisms of the identity of a derived category

A natural endomorphism `σ : 𝟭 A ⟶ 𝟭 A` of the identity functor of an abelian category `A`
(for instance the multiplication by a central scalar) induces, by applying it levelwise, a natural
endomorphism `HomologicalComplex.natTransId σ c` of the identity of the category of homological
complexes, and then a natural endomorphism `DerivedCategory.natTransId σ` of the identity of the
derived category of `A`. On the image of a cochain complex `K` it is the image of the levelwise
endomorphism (`DerivedCategory.natTransId_app_Q_obj`), and similarly on the image of an object of
the homotopy category (`DerivedCategory.natTransId_app_Qh_obj_quotient_obj`).
-/

@[expose] public section

open CategoryTheory Limits

variable {A : Type*} [Category* A]

namespace HomologicalComplex

variable [Preadditive A]

/-- The natural endomorphism of the identity of the category of homological complexes in `A`
which is given in each degree by a natural endomorphism `σ` of the identity of `A`. -/
@[simps]
def natTransId (σ : 𝟭 A ⟶ 𝟭 A) {ι : Type*} (c : ComplexShape ι) :
    𝟭 (HomologicalComplex A c) ⟶ 𝟭 (HomologicalComplex A c) where
  app K :=
    { f n := σ.app (K.X n)
      comm' i j _ := (σ.naturality (K.d i j)).symm }
  naturality _ _ f := by
    ext n
    exact σ.naturality (f.f n)

end HomologicalComplex

namespace DerivedCategory

variable [Abelian A] [HasDerivedCategory A]

/-- The natural endomorphism of the identity of the derived category of `A` induced by a natural
endomorphism `σ` of the identity of `A`, applied levelwise to complexes. -/
noncomputable def natTransId (σ : 𝟭 A ⟶ 𝟭 A) : 𝟭 (DerivedCategory A) ⟶ 𝟭 (DerivedCategory A) :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) Q Q
    (𝟭 (DerivedCategory A)) (𝟭 (DerivedCategory A))
    (Functor.whiskerRight (HomologicalComplex.natTransId σ (ComplexShape.up ℤ)) Q)

/-- On the image of a cochain complex `K`, `DerivedCategory.natTransId σ` is the image of the
levelwise endomorphism `σ` of `K`. -/
lemma natTransId_app_Q_obj (σ : 𝟭 A ⟶ 𝟭 A) (K : CochainComplex A ℤ) :
    (natTransId σ).app (Q.obj K) =
      Q.map ((HomologicalComplex.natTransId σ (ComplexShape.up ℤ)).app K) := by
  simp [natTransId, Localization.liftNatTrans_app, Localization.Lifting.iso]

/-- On the image of an object `K` of the homotopy category, `DerivedCategory.natTransId σ` is the
image of the levelwise endomorphism `σ` of `K`. -/
lemma natTransId_app_Qh_obj_quotient_obj (σ : 𝟭 A ⟶ 𝟭 A) (K : CochainComplex A ℤ) :
    (natTransId σ).app (Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((HomologicalComplex.natTransId σ (ComplexShape.up ℤ)).app K)) := by
  have h := (natTransId σ).naturality ((quotientCompQhIso A).hom.app K)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, natTransId_app_Q_obj] at h
  rw [← cancel_mono ((quotientCompQhIso A).hom.app K)]
  exact h.symm.trans (quotientCompQhIso_hom_naturality _).symm

end DerivedCategory
