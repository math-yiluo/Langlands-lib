/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsHeartBound
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.Integral.IntegralConstantModelLocalResolution
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! Bounded-heart devissage for the continuous integral coefficient.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace CategoryTheory

/-- Bounded-heart section bound for an arbitrary bounded classical local-torsion complex.
Source: blueprint latest, `part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the dual-tensor and filtration steps; Stacks Tag 08J5. The proof applies
bounded-heart amplitude to the heart bound and the triangulated derived sections functor.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions).

The hypothesis `hD` pins `D` to `stratumModuleDual _ S L = RHom(L[0], A[0])`.  Since
`L` has a finite constant local model, `L[0]` is dualizable (local length-one free
resolutions and pro-étale descent), so `RHom(L[0], -) ≅ D ⊗ -`; this identifies the
conclusion with degree-`r` cohomology of `RΓ(D ⊗ K)`.

Proof plan: regard derived tensor by `D` and derived sections as triangulated
functors, using a K-flat representative for the former.  Apply
`DerivedCategory.bounded_heart_amplitude` to the truncation triangles of `K`;
the supplied `hheart` is the heart case, while `hK` and `hab` give the lower and
upper truncation bounds.  The resulting sections object has no homology above
`b+s+1`.  Since `hr` is larger than this bound, commute the shift by `r` through
the triangulated functors and evaluate at degree zero, yielding the displayed
zero object for the internal Hom from `L[0]`.
-/
theorem integralStratumFiniteCdReductions_sections_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (hD : D = stratumModuleDual (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (hheart : ∀ F,
      IsClassicalAbelian F.X ∧ IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X →
      ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
          ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
            (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
              ((DerivedCategory.singleFunctor _ 0).obj F)))))
    (r : ℤ) (hr : b + (s : ℤ) + 1 < r) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
        (((derivedHom (IntegralQuotient.integral l E) S).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj (K⟦r⟧)))) := by
  have _hcd := hs
  let A := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)
  have hd : IsDualizable ((DerivedCategory.singleFunctor A 0).obj L) := by
    let Q (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
      ∀ [IsCommMonObj R.X] (M : supportModules R.X S),
        HasFiniteConstantLocalModel R.X S M →
          IsDualizable ((DerivedCategory.singleFunctor _ 0).obj M)
    have hQ : Q (Mon.mk (DerivedNakayama.integerRing l E)) := by
      intro _ M hM
      obtain ⟨V, hV⟩ := integral_constantModel_localResolution l E S M hM
      apply (condensed_dualizable_iff_proetale_cover
        (⟨integralCoefficientRing l E⟩ : Profinite.CondensedRing.{u}) S V
        ((DerivedCategory.singleFunctor _ 0).obj M)).mpr
      intro j
      obtain ⟨C, hC, h₁, h₂, ⟨e⟩⟩ := hV j
      have h := DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hC h₁ h₂
      exact h.of_iso
        ((DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
          (((upperStar (integralCoefficientRing l E) (V.f j)).mapDerivedCategorySingleFunctor
            0).app M).symm)
    have hQ' : Q (sfbCondensedIntegers l E) :=
      @Eq.mp (Q (Mon.mk (DerivedNakayama.integerRing l E)))
        (Q (sfbCondensedIntegers l E))
        (congrArg Q (IntegralConstantModel.pointEquality l E)) (@hQ)
    exact hQ' L hL
  let G := stratumModuleDerivedSections (IntegralQuotient.integral l E) S
  let U := (derivedTensor (IntegralQuotient.integral l E) S).obj D
  let T := U ⋙ G
  let : G.CommShift ℤ := by
    dsimp only [G, stratumModuleDerivedSections]
    infer_instance
  let : G.IsTriangulated := by
    dsimp only [G, stratumModuleDerivedSections]
    infer_instance
  let : U.CommShift ℤ := by
    dsimp only [U, CondensedRing.derivedTensor]
    infer_instance
  let : U.IsTriangulated := by
    dsimp only [U, CondensedRing.derivedTensor]
    infer_instance
  let : T.CommShift ℤ := Functor.CommShift.comp U G
  let : T.IsTriangulated := by infer_instance
  let P : A → Prop := fun F ↦
    ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))
  have hb := DerivedCategory.bounded_heart_amplitude A Ab.{u + 1} T P
    (fun M N e h i hi ↦ (h i hi).of_iso
      ((DerivedCategory.homologyFunctor Ab.{u + 1} i).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e.symm))))
    (fun i _ ↦ (DerivedCategory.homologyFunctor Ab.{u + 1} i).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A))))
    0 ((s : ℤ) + 1) (by omega)
    (fun _ h ↦ h)
    a b hab K hK (fun q i hi ↦ hheart _ (hclass q) i hi)
  have hz := hb r (Or.inr (by omega : b + ((s : ℤ) + 1) < r))
  have e₁ : (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        ((shiftFunctor _ r).obj (T.obj K)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} r).obj (T.obj K) := by
    exact ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).shiftIso r 0 r (by omega)).app
      (T.obj K)
  have e₂ : (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        (T.obj (K⟦r⟧)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        ((shiftFunctor _ r).obj (T.obj K)) := by
    simpa only [Functor.comp_obj] using
      (DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso ((T.commShiftIso r).app K)
  have hz' := (hz.of_iso e₁).of_iso e₂
  obtain ⟨hdual⟩ := hd
  let := hdual
  let := BraidedCategory.exactPairing_swap
    ((DerivedCategory.singleFunctor A 0).obj L)
    (((DerivedCategory.singleFunctor A 0).obj L)ᘁ)
  let := MonoidalClosed.isIso_ihomUnitTensorToIhom
    (((DerivedCategory.singleFunctor A 0).obj L)ᘁ)
    ((DerivedCategory.singleFunctor A 0).obj L) (K⟦r⟧)
  have ec := asIso (MonoidalClosed.ihomUnitTensorToIhom
    ((DerivedCategory.singleFunctor A 0).obj L) (K⟦r⟧))
  subst D
  exact hz'.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso
    (G.mapIso ec.symm))


end CategoryTheory
