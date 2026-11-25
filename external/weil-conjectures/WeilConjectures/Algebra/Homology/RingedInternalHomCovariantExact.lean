/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Covariant exactness of derived internal Hom

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Covariant exactness, including the coherent integer shift structure.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(auxiliary; not a blueprint node).

Proof: Fix a complex A representing L. Represent the first arrow of a distinguished target triangle
by a map g between K-injective complexes J and I. Its cone is K-injective: apply Hom from every
acyclic test complex to the cone triangle and use exactness and shift-stability of K-injectives. The
finite graded splitting of Hom(A,Cone(g)) identifies it with Cone(Hom(A,g)), preserving the
inclusion, projection and connecting morphism under the unsigned target-shift reindexing. The
product projections prove that this reindexing is natural, equals the identity at zero, and composes
under addition. Descend the coherent structure and cone comparison through localization, using the
fixed K-injective augmentation. Every distinguished triangle is isomorphic to a localized cone
triangle by TR3 and two-out-of-three for isomorphisms, so transfer the distinguished-triangle
property through that isomorphism. No boundedness or infinite-product exactness is needed.
-/
theorem ringedInternalHom_covariant_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ L : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op
    L)).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L)).IsTriangulated) := by
  let : HasSheafify J AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian J AddCommGrpCat.{u}
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let : MonoidalCategory A := SheafOfModules.cochainModulesMonoidal R
  let : SymmetricCategory A := SheafOfModules.cochainModulesSymmetric R
  let : MonoidalPreadditive A := SheafOfModules.cochainModulesPreadditive R
  let : MonoidalClosed A :=
    (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : Abelian.HasFunctorialFlatResolution A :=
    SheafOfModules.hasFunctorialFlatResolution_kfi _
  obtain ⟨S, hS, _⟩ := RingedDerivedNative.closedAdjunction.{u, u, u, w} J R
  let : MonoidalCategory (DerivedCategory A) := RingedDerivedNative.monoidal.{u, u, u, w} J R
  intro L
  have adj := S.adjunction L
  rw [hS] at adj
  change MonoidalCategory.tensorRight L ⊣
    (Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L) at adj
  let F := MonoidalCategory.tensorRight L
  let : F.CommShift ℤ := DerivedCategory.commShiftTensorRight A L
  have : F.IsTriangulated := DerivedCategory.isTriangulated_tensorRight A L
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact ⟨inferInstance, adj.isTriangulated_rightAdjoint⟩

end CategoryTheory
