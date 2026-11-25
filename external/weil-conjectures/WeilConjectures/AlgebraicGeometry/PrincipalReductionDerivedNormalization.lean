/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.AlgebraicGeometry.PrincipalConeTensorNormalization
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension

/-! # Normalized derived principal quotient cones

(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PrincipalNormalization

attribute [local irreducible] upperStarFromPoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical extension followed by restriction, with positive level n+1.
Source: blueprint Cones paragraph
(auxiliary; not a blueprint node). -/
abbrev reduction (n : ℕ) :=
  AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n

/-- The scalar principal cone computes the canonical derived quotient functor,
with the quotient maps and adjunction units, and with its standard signed shifts.

(auxiliary; not a blueprint node).

Proof: the scalar formula identifies d with multiplication by the uniformizer.
The resolution theorem gives the short exact sequence R --d^(n+1)--> R --> B_n.
Its cone augments to B_n[0], and its two free terms make it K-flat. Tensoring an
arbitrary complex with this resolution gives the scalar cone, by the signed
cone--tensor interchange. On K-flat complexes, tensoring the augmentation is a
quasi-isomorphism and agrees with extension of scalars followed by restriction:
both balanced maps send a tensor of coefficients and a module section to its
scalar extension. The universal left-derived comparison extends this equality
to all complexes and all derived morphisms. The quotient coefficient map lifts
to (d,id) on the two-term resolutions, so the normalized tensor comparison
identifies its cone map with integralStep. The degree-zero inclusion is the
ordinary scalar-extension unit and hence descends to the specified derived
adjunction unit. The tensor shift comparison has coordinates (x,(-1)^r y),
which is the inverse of mappingCone.shiftIso. Its coherence descends through
localization and gives sF. Tensoring is additive and takes cone triangles to
cone triangles with this boundary sign, proving exactness. These constructions
include zero complexes and empty sites and use no boundedness assumption. -/
theorem derived_principal_normalization
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s)
    (hs : ∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
      DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M =
        DerivedNakayama.scalarOnComplex l E X d M ≫
          DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) :
    ∃ (sF : ∀ n : ℕ, (reduction l E X n).CommShift ℤ)
      (κ : ∀ n : ℕ, DerivedNakayama.coneFunctor l E X (d ^ (n + 1)) ≅
        DerivedCategory.Q ⋙ reduction l E X n),
      (∀ n : ℕ, (reduction l E X n).Additive ∧
        @Functor.IsTriangulated _ _ _ _ _ _ (reduction l E X n)
          (sF n) _ _ _ _ _ _ _ _) ∧
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.map
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X d M) (𝟙 M)
          ((Category.comp_id _).trans (hs n M))) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫
              AdicCompletion.integralStep l E X (DerivedCategory.Q.obj M) n) ∧
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            (κ n).hom.app M =
          (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app (DerivedCategory.Q.obj M)) ∧
      (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map
            (CochainComplex.mappingCone.shiftIso
              (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) r).inv ≫
            (DerivedCategory.Q.commShiftIso r).hom.app
              (CochainComplex.mappingCone
                (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            ((κ n).hom.app M)⟦r⟧' =
          (κ n).hom.app (M⟦r⟧) ≫
            (reduction l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
            (Functor.commShiftIso (self := sF n) (reduction l E X n) r).hom.app
              (DerivedCategory.Q.obj M)) := by
  let (n : ℕ) : (DerivedNakayama.reductionFunctor l E X (n + 1)).CommShift ℤ :=
    tensorReductionShift l E X n
  let (n : ℕ) : (DerivedNakayama.reductionFunctor l E X (n + 1)).Additive := by
    change (tensorRight _).Additive
    infer_instance
  let (n : ℕ) : (DerivedNakayama.reductionFunctor l E X (n + 1)).IsTriangulated := by
    change (tensorRight _).IsTriangulated
    infer_instance
  obtain ⟨c, hc, hu, hsigned⟩ := principal_cone_tensor_normalization l E X d hd hs
  obtain ⟨e, he, hunit⟩ := principal_tensor_scalar_extension l E X
  let e' (n : ℕ) : DerivedNakayama.reductionFunctor l E X (n + 1) ≅
      reduction l E X n := e n
  let sF (n : ℕ) : (reduction l E X n).CommShift ℤ :=
    Functor.CommShift.ofIso (e' n) ℤ
  let κ (n : ℕ) : DerivedNakayama.coneFunctor l E X (d ^ (n + 1)) ≅
      DerivedCategory.Q ⋙ reduction l E X n :=
    c n ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q (e' n)
  refine ⟨sF, κ, ?_, ?_, ?_, ?_⟩
  · intro n
    let := sF n
    have : NatTrans.CommShift (e' n).hom ℤ :=
      Functor.CommShift.ofIso_compatibility (e' n) ℤ
    exact ⟨Functor.additive_of_iso (e' n), Functor.isTriangulated_of_iso (e' n)⟩
  · intro n M
    change _ ≫ ((c n).hom.app M ≫ (e' n).hom.app (DerivedCategory.Q.obj M)) =
      ((c (n + 1)).hom.app M ≫ (e' (n + 1)).hom.app (DerivedCategory.Q.obj M)) ≫ _
    rw [← Category.assoc, hc, Category.assoc, he, ← Category.assoc]
  · intro n M
    change _ ≫ ((c n).hom.app M ≫ (e' n).hom.app (DerivedCategory.Q.obj M)) = _
    rw [← Category.assoc, hu, hunit]
  · intro n r M
    let := sF n
    have : NatTrans.CommShift (e' n).hom ℤ :=
      Functor.CommShift.ofIso_compatibility (e' n) ℤ
    change _ ≫ _ ≫ ((c n).hom.app M ≫
      (e' n).hom.app (DerivedCategory.Q.obj M))⟦r⟧' =
        ((c n).hom.app (M⟦r⟧) ≫ (e' n).hom.app (DerivedCategory.Q.obj (M⟦r⟧))) ≫ _ ≫ _
    calc
      _ = (c n).hom.app (M⟦r⟧) ≫
          (DerivedNakayama.reductionFunctor l E X (n + 1)).map
            ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
          (Functor.commShiftIso (DerivedNakayama.reductionFunctor l E X (n + 1)) r).hom.app
            (DerivedCategory.Q.obj M) ≫
          ((e' n).hom.app (DerivedCategory.Q.obj M))⟦r⟧' := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun f ↦ f ≫ ((e' n).hom.app (DerivedCategory.Q.obj M))⟦r⟧')
            (hsigned n r M)
      _ = _ := by
        rw [NatTrans.shift_app_comm (e' n).hom r (DerivedCategory.Q.obj M)]
        simp only [Category.assoc]
        congr 1
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        exact (e' n).hom.naturality ((DerivedCategory.Q.commShiftIso r).hom.app M)

end AlgebraicGeometry.ProEtale.PrincipalNormalization
