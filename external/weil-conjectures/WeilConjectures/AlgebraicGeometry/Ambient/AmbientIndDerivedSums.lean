/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedTriangulated
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Sums and truncations for ind-constructible cohomology

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
`sk-cor-ambient-ind-derived-sums.md` and its proof (blueprint: corollary-ambient-ind-derived).

The canonical comparison is written using arbitrary colimit cocones. Its source is a
coproduct of the cohomology objects and its target is the cohomology of the coproduct;
`IsColimit.desc` specifies the comparison by the original coprojections. This avoids
making any additional choice of coproducts or imposing a coproduct-existence hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

universe w v a b

/-- An empty sum supplies the zero object, including for an otherwise arbitrary predicate. -/
private theorem containsZero_of_sums
    {A : Type a} [Category.{v} A] [HasZeroObject A] [HasZeroMorphisms A]
    (P : ObjectProperty A)
    (hsum : ∀ (I : Type w) (K : I → A) (c : Cofan K), IsColimit c →
      (∀ i, P (K i)) → P c.pt) : P.ContainsZero := by
  let K : PEmpty.{w + 1} → A := fun i ↦ i.elim
  let c : Cofan K := Cofan.mk 0 (fun i ↦ i.elim)
  have hc : IsColimit c := Cofan.IsColimit.mk c (fun _ ↦ 0)
    (fun _ i ↦ i.elim) (fun _ _ _ ↦ (isZero_zero A).eq_of_src _ _)
  exact ⟨0, isZero_zero A, hsum _ K c hc (fun i ↦ i.elim)⟩

/-- Exact coproducts and K-injective resolutions make every derived cohomology functor
preserve the specified small coproducts. -/
private theorem homology_preserves_sums
    (A : Type a) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{b} A] (I : Type w) (n : ℤ) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n) := by
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  have : HasColimitsOfSize.{w, w} A := IsGrothendieckAbelian.hasColimits A
  have : HasColimitsOfShape (Discrete I) A :=
    HasColimitsOfShape.of_small.{w, w} A (Discrete I)
  have : HasCoproducts.{w} A := fun J ↦
    HasColimitsOfShape.of_small.{w, w} A (Discrete J)
  have : HasExactColimitsOfShape (Discrete I) A := inferInstance
  exact DerivedCategory.preservesColimitsOfShape_homologyFunctor n

/-- Closure of a heart predicate under sums passes to its cohomology predicate. -/
private theorem homology_closedUnder_sums
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{b} A] (P : ObjectProperty A)
    (hsum : ∀ (I : Type w) (K : I → A) (c : Cofan K), IsColimit c →
      (∀ i, P (K i)) → P c.pt)
    (I : Type w) (K : I → DerivedCategory A) (c : Cofan K) (hc : IsColimit c)
    (hK : ∀ i, DerivedCategory.homologyProperty P (K i)) :
    DerivedCategory.homologyProperty P c.pt := by
  intro n
  let H := DerivedCategory.homologyFunctor A n
  have : PreservesColimitsOfShape (Discrete I) H := homology_preserves_sums A I n
  let d : Cofan (fun i ↦ H.obj (K i)) :=
    Cofan.mk (H.obj c.pt) (fun i ↦ H.map (c.inj i))
  exact hsum I _ d
    ((Cofan.isColimitMapCoconeEquiv H K c) (isColimitOfPreserves H hc)) (fun i ↦ hK i n)

/-- The nonzero coordinate idempotents of an existing coproduct have small support. -/
private theorem coproduct_small_support
    {C : Type a} [Category.{v} C] [Preadditive C] [LocallySmall.{w} C]
    {I : Type b} (K : I → C) (c : Cofan K) (hc : IsColimit c) :
    Small.{w} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : c.pt ⟶ K i := hc.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : c.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    hc.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ c.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
  have hi : c.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

/-- A colimit of any discrete functor gives the cofan with its original legs. -/
private noncomputable def cofanIsColimit
    {C : Type a} [Category.{v} C] {I : Type b} {F : Discrete I ⥤ C}
    {c : Cocone F} (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt (fun i ↦ c.ι.app ⟨i⟩)) := by
  have h := (IsColimit.precomposeInvEquiv (Discrete.natIsoFunctor (F := F)) c).symm hc
  exact h.ofIsoColimit (Cocone.ext (Iso.refl _) (by simp))

/-- For a replete triangulated predicate, small sums suffice for the definition of
localizing, since every existing larger coproduct has small nonzero support. -/
private theorem localizing_of_small_sums
    {C : Type a} [Category.{v} C] [HasZeroObject C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{w} C] (P : ObjectProperty C)
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hsum : ∀ (I : Type w) (K : I → C) (c : Cofan K), IsColimit c →
      (∀ i, P (K i)) → P c.pt) : IsLocalizingSubcategory P := by
  classical
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I F hF hK
  let _ := hF
  let K : I → C := fun i ↦ F.obj ⟨i⟩
  let c : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
  have hc : IsColimit c := cofanIsColimit (colimit.isColimit F)
  have : Small.{w} {i // ¬ IsZero (K i)} := coproduct_small_support K c hc
  let J := {i // ¬ IsZero (K i)}
  let U : J → C := fun j ↦ K j.val
  let r : Cofan U := Cofan.mk c.pt (fun j ↦ c.inj j.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ hc.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s j
      rcases j with ⟨j, hj⟩
      exact (hc.fac _ ⟨j⟩).trans (by simp [hj])
    · intro s m hm
      apply hc.hom_ext
      intro ⟨i⟩
      rw [hc.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let e := Discrete.equivalence (equivShrink.{w} J).symm
  have hr' := cofanIsColimit (hr.whiskerEquivalence e)
  exact hsum _ _ _ hr' (fun j ↦ hK ((equivShrink J).symm j).val)

/-- All three assertions for a finite subextension E.
Source: blueprint main-20261015, `sk-cor-ambient-ind-derived-sums.md`, clauses 1--3;
Stacks Project, Tags 03DB, 07D9 and 0118; the standing separated finite-type
positive-characteristic field setting of `sk-def-sfb-dc-setting`
(blueprint: corollary-ambient-ind-derived).

Proof:
1. The existing module-object Grothendieck instance supplies exact small coproducts
   and K-injective resolutions. The source-library coproduct-preservation instance
   for derived homology sends the given colimit cofan to a colimit cocone. Uniqueness
   of colimits makes the displayed canonical comparison `desc` an isomorphism.
2. Apply the sum clause of `proposition-ind-constructible-sheaves--3` to that image cofan
   degree by degree. The empty sum gives membership of zero in IndCons.
3. Apply the source-library `homologyProperty_truncLE` and `homologyProperty_truncGE`
   lemmas: truncation retains the old cohomology or replaces it by zero.
4. Unpack bounded constructibility and use `ObjectProperty.le_ind` on every
   cohomology object, viewed as its own one-object filtered colimit.
5. Use `corollary-ambient-ind-derived--1` for triangulatedness. Repleteness follows
   from the isomorphism-closure instance for the homology predicate. To apply the
   intersection defining `localizingClosure`, an existing coproduct with larger index
   set is reduced to small nonzero support: distinct nonzero summands give distinct
   coordinate idempotents in the locally small endomorphism set of its vertex.
   Remove the zero summands, shrink the support, and apply step 2. The resulting
   localizing predicate contains Dbc by step 4. The intersection defining Loc(Dbc)
   is therefore contained in Dic.
-/
theorem indConstructibleDerived_sums_and_truncations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
      (c : Cofan K), IsColimit c → ∀ (n : ℤ)
      (d : Cocone (Discrete.functor K ⋙ DerivedCategory.homologyFunctor _ n))
      (hd : IsColimit d),
      IsIso (hd.desc ((DerivedCategory.homologyFunctor _ n).mapCocone c))) ∧
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
      (c : Cofan K), IsColimit c →
      (∀ s : S, ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj (K s))) →
      ∀ m : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ m).obj c.pt)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) (n : ℤ),
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K)))) ∧
    (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) ∧
    (localizingClosure (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObj X ℓ E)
  let P : ObjectProperty A := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
  have hsum := (indConstructible_filteredColimits_and_sums ℓ E k p hp hpl X).2
  have : P.ContainsZero := containsZero_of_sums P hsum
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (indConstructibleDerived_isTriangulated ℓ E k p hp hpl X).1
  have hdbc : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ≤
      DerivedCategory.homologyProperty P := by
    intro K hK m
    exact ObjectProperty.le_ind _ _ (hK.2 m)
  have hlocal : IsLocalizingSubcategory (DerivedCategory.homologyProperty P) :=
    localizing_of_small_sums _ (homology_closedUnder_sums P hsum)
  refine ⟨?_, ?_, ?_, hdbc, ?_⟩
  · intro S K c hc n d hd
    have := homology_preserves_sums A S n
    have hc' := isColimitOfPreserves (DerivedCategory.homologyFunctor A n) hc
    exact hd.nonempty_isColimit_iff_isIso_desc.mp ⟨hc'⟩
  · exact homology_closedUnder_sums P hsum
  · intro K n hK
    exact ⟨DerivedCategory.homologyProperty_truncLE hK n,
      DerivedCategory.homologyProperty_truncGE hK n⟩
  · intro K hK
    exact hK _ hlocal hdbc

/-- All three assertions for the finite-subextension-valued condensed algebraic closure.
Source: blueprint main-20261015, `sk-cor-ambient-ind-derived-sums.md`, clauses 1--3;
Stacks Project, Tags 03DB, 07D9 and 0118; the standing separated finite-type
positive-characteristic field setting of `sk-def-sfb-dc-setting`
(blueprint: corollary-ambient-ind-derived).

Proof:
1. The existing module-object Grothendieck instance supplies exact small coproducts
   and K-injective resolutions. The source-library coproduct-preservation instance
   for derived homology sends the given colimit cofan to a colimit cocone. Uniqueness
   of colimits makes the displayed canonical comparison `desc` an isomorphism.
2. Apply the sum clause of `proposition-ind-constructible-sheaves--3` to that image cofan
   degree by degree. The empty sum gives membership of zero in IndCons.
3. Apply the source-library `homologyProperty_truncLE` and `homologyProperty_truncGE`
   lemmas: truncation retains the old cohomology or replaces it by zero.
4. Unpack bounded constructibility and use `ObjectProperty.le_ind` on every
   cohomology object, viewed as its own one-object filtered colimit.
5. Use `corollary-ambient-ind-derived--1` for triangulatedness. Repleteness follows
   from the isomorphism-closure instance for the homology predicate. To apply the
   intersection defining `localizingClosure`, an existing coproduct with larger index
   set is reduced to small nonzero support: distinct nonzero summands give distinct
   coordinate idempotents in the locally small endomorphism set of its vertex.
   Remove the zero summands, shrink the support, and apply step 2. The resulting
   localizing predicate contains Dbc by step 4. The intersection defining Loc(Dbc)
   is therefore contained in Dic.
-/
theorem indConstructibleDerived_sums_and_truncations_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)))
      (c : Cofan K), IsColimit c → ∀ (n : ℤ)
      (d : Cocone (Discrete.functor K ⋙ DerivedCategory.homologyFunctor _ n))
      (hd : IsColimit d),
      IsIso (hd.desc ((DerivedCategory.homologyFunctor _ n).mapCocone c))) ∧
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)))
      (c : Cofan K), IsColimit c →
      (∀ s : S, ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj (K s))) →
      ∀ m : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ m).obj c.pt)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) (n : ℤ),
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K)))) ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) ∧
    (localizingClosure (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)
  let P : ObjectProperty A := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
  have hsum := (indConstructible_filteredColimits_and_sums_padicAlgCl ℓ k p hp hpl X).2
  have : P.ContainsZero := containsZero_of_sums P hsum
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (indConstructibleDerived_isTriangulated ℓ ⟨⊥, inferInstance⟩ k p hp hpl X).2
  have hdbc : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ≤
      DerivedCategory.homologyProperty P := by
    intro K hK m
    exact ObjectProperty.le_ind _ _ (hK.2 m)
  have hlocal : IsLocalizingSubcategory (DerivedCategory.homologyProperty P) :=
    localizing_of_small_sums _ (homology_closedUnder_sums P hsum)
  refine ⟨?_, ?_, ?_, hdbc, ?_⟩
  · intro S K c hc n d hd
    have := homology_preserves_sums A S n
    have hc' := isColimitOfPreserves (DerivedCategory.homologyFunctor A n) hc
    exact hd.nonempty_isColimit_iff_isIso_desc.mp ⟨hc'⟩
  · exact homology_closedUnder_sums P hsum
  · intro K n hK
    exact ⟨DerivedCategory.homologyProperty_truncLE hK n,
      DerivedCategory.homologyProperty_truncGE hK n⟩
  · intro K hK
    exact hK _ hlocal hdbc

end AlgebraicGeometry.ProEtale
