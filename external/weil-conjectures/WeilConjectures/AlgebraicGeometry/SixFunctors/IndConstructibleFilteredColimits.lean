/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Filtered colimits and sums of ind-constructible module sheaves

Let `X` be a separated scheme of finite type over a field `k` of characteristic `p > 0`, and
`ℓ ≠ p` a prime. Ind-constructible sheaves of modules on the pro-étale site of `X` (IndCons,
`ObjectProperty.ind.{u + 1}` of `IsConstantModelConstructible`) are closed under filtered
colimits and arbitrary sums, for coefficients a finite extension `E/ℚ_ℓ`
(`AlgebraicGeometry.ProEtale.indConstructible_filteredColimits_and_sums`) and for the condensed
algebraic closure
(`AlgebraicGeometry.ProEtale.indConstructible_filteredColimits_and_sums_padicAlgCl`).
Sums are stated using arbitrary colimit cofans, including the empty one.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

private theorem ind_finite_coproduct
    {C : Type*} [Category.{u + 1} C] [HasColimitsOfSize.{u + 1, u + 1} C]
    (P : ObjectProperty C)
    (hfin : ∀ (S : Type (u + 1)) [Finite S] (B : S → C),
      (∀ s, P (B s)) → P (∐ B))
    (S : Type (u + 1)) [Finite S] (B : S → C)
    (hB : ∀ s, P.ind.{u + 1} (B s)) : P.ind.{u + 1} (∐ B) := by
  classical
  choose J _ _ pres hpres using hB
  let F : (∀ s, J s) ⥤ (S → C) := Functor.pi (fun s ↦ (pres s).diag)
  let c : Cocone F := pi.coconeOfCoconeCompEval
    (fun s ↦ (pres s).cocone.whisker (Pi.eval J s))
  have hc : IsColimit c := pi.coconeOfCoconeEvalIsColimit
    (fun s ↦ (Functor.Final.isColimitWhiskerEquiv (Pi.eval J s)
      (pres s).cocone).symm (pres s).isColimit)
  let : PreservesColimitsOfShape (∀ s, J s) (Sigma.functor S : (S → C) ⥤ C) := by
    rw [← piEquivalenceFunctorDiscrete_functor_comp_colim]
    infer_instance
  exact ⟨∀ s, J s, inferInstance, inferInstance,
    { diag := F ⋙ Sigma.functor S
      ι := (Sigma.functor S).mapCocone c |>.ι
      isColimit := isColimitOfPreserves (Sigma.functor S) hc },
    fun j ↦ hfin S (fun s ↦ (pres s).diag.obj (j s)) (fun s ↦ hpres s (j s))⟩

private theorem ind_coproduct
    {C : Type*} [Category.{u + 1} C] [LocallySmall.{u + 1} C]
    [HasColimitsOfSize.{u + 1, u + 1} C]
    (P : ObjectProperty C) (hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} C)
    (hfin : ∀ (S : Type (u + 1)) [Finite S] (B : S → C),
      (∀ s, P (B s)) → P (∐ B))
    (S : Type (u + 1)) (B : S → C) (c : Cofan B) (hc : IsColimit c)
    (hB : ∀ s, P.ind.{u + 1} (B s)) : P.ind.{u + 1} c.pt := by
  classical
  apply (P.ind).prop_of_iso ((colimit.isColimit _).coconePointUniqueUpToIso hc)
  rw [← ObjectProperty.ind_ind hfp]
  exact ⟨Finset (Discrete S), inferInstance, inferInstance,
    { diag := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor B)
      ι := (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone B).ι
      isColimit := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone B },
    fun T ↦ ind_finite_coproduct P hfin T (fun t ↦ B t.val.as) (fun t ↦ hB t.val.as)⟩

namespace AlgebraicGeometry.ProEtale

private theorem constructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hloc (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨U, hU⟩ := h
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hU i
    exact ⟨Q, hQ, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eQ⟩⟩
  have hstrat (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hloc _ _ _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  constructor
  intro M N e h
  unfold IsConstantModelConstructible at h ⊢
  split_ifs at h ⊢ with hX
  · exact hstrat _ _ _ e h
  · intro U hU
    exact hstrat _ _ _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (h U hU)

private theorem constructible_finite_coproduct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [HasFiniteColimits (ConstantModelConstructible Λ X)]
    [PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X))]
    (S : Type (u + 1)) [Finite S]
    (B : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ∀ s, IsConstantModelConstructible Λ X (B s)) :
    IsConstantModelConstructible Λ X (∐ B) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
    constructible_iso Λ X
  let : ObjectProperty.IsClosedUnderColimitsOfShape
      (IsConstantModelConstructible Λ X) (Discrete S) :=
    ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _ _
  exact ObjectProperty.prop_colimit (IsConstantModelConstructible Λ X)
    (Discrete.functor B) (fun s ↦ hB s.as)

set_option linter.unusedVariables false in
/-- For finite `E/ℚ_ℓ`, IndCons is closed under ambient filtered colimits and arbitrary sums. -/
theorem indConstructible_filteredColimits_and_sums
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) (B.obj i)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) (B s)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) c.pt) := by
  constructor
  · intro I _ _ B c hc hB
    let : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
    let : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let P : ObjectProperty (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) :=
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X
    have hff := (indHeart_fullFaithfulness ℓ X).1 E
    have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
      intro C hC
      exact hff.1 ⟨C, hC⟩
    rw [← ObjectProperty.ind_ind hfp]
    exact ⟨I, inferInstance, inferInstance,
      { diag := B, ι := c.ι, isColimit := hc }, hB⟩
  · intro S B c hc hB
    let : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
    let : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let P := IsConstantModelConstructible (Profinite.continuousMapRingObj E) X
    have hff := (indHeart_fullFaithfulness ℓ X).1 E
    have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
      intro C hC
      exact hff.1 ⟨C, hC⟩
    let : IsNoetherian X := {}
    have hcoeff := (coefficientHeart_closure ℓ (Profinite.padicSubfieldCondensedRing ℓ E.1)
      (Or.inl ⟨E.1, inferInstance, rfl⟩)).2 X
    let := hcoeff.2.2.2.1.some
    let := hcoeff.2.2.2.2.2.1
    exact ind_coproduct P hfp
      (constructible_finite_coproduct (Profinite.continuousMapRingObj E) X) S B c hc hB

set_option linter.unusedVariables false in
/-- For the condensed algebraic closure, IndCons is closed under ambient filtered colimits
and arbitrary sums. -/
theorem indConstructible_filteredColimits_and_sums_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) (B.obj i)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) (B s)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) c.pt) := by
  constructor
  · intro I _ _ B c hc hB
    let : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
    let : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let P : ObjectProperty (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X
    have hff := (indHeart_fullFaithfulness ℓ X).2
    have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
      intro C hC
      exact hff.1 ⟨C, hC⟩
    rw [← ObjectProperty.ind_ind hfp]
    exact ⟨I, inferInstance, inferInstance,
      { diag := B, ι := c.ι, isColimit := hc }, hB⟩
  · intro S B c hc hB
    let : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
    let : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let P := IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X
    have hff := (indHeart_fullFaithfulness ℓ X).2
    have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
      intro C hC
      exact hff.1 ⟨C, hC⟩
    let : IsNoetherian X := {}
    have hcoeff := (coefficientHeart_closure ℓ (Profinite.padicAlgClCondensedRing ℓ)
      (Or.inr rfl)).2 X
    let := hcoeff.2.2.2.1.some
    let := hcoeff.2.2.2.2.2.1
    exact ind_coproduct P hfp
      (constructible_finite_coproduct (Profinite.padicAlgClRingObj ℓ) X) S B c hc hB

end AlgebraicGeometry.ProEtale
