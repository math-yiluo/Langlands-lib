/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection

/-! # Evaluation comparisons with a K-injective second representative

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-kinjective-evaluation-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem eq_of_two_sided_inverse {C : Type*} [Category C]
    {X Y : C} {f : X ⟶ Y} {r s : Y ⟶ X}
    (hr : f ≫ r = 𝟙 X) (hs : s ≫ f = 𝟙 Y) : r = s := by
  calc
    r = 𝟙 _ ≫ r := (Category.id_comp r).symm
    _ = (s ≫ f) ≫ r := by rw [hs]
    _ = s ≫ (f ≫ r) := Category.assoc _ _ _
    _ = s := by rw [hr, Category.comp_id]

private theorem exists_iso_comparison_of_inverse {C : Type*} [Category C]
    {S T A B : C} (g : S ⟶ T) (f : A ⟶ B) [IsIso f]
    (hr : ∃ r, g ≫ r = 𝟙 S) (hs : ∃ s, s ≫ g = 𝟙 T)
    (hb : Nonempty (T ≅ B)) :
    ∃ a : S ≅ A, ∃ b : T ≅ B, g ≫ b.hom = a.hom ≫ f := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨s, hs⟩ := hs
  have hrs : r = s := eq_of_two_sided_inverse hr hs
  let e : S ≅ T :=
    { hom := g
      inv := r
      hom_inv_id := hr
      inv_hom_id := by rw [hrs]; exact hs }
  obtain ⟨b⟩ := hb
  refine ⟨e ≪≫ b ≪≫ (asIso f).symm, b, ?_⟩
  simp [e, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The restriction and Hom models use equivalent localized-site carriers.
/-- The local evaluation square when its second representative is already K-injective.
This only handles the resolved case; it does not assert the comparison for an arbitrary
second complex.

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-kinjective-evaluation-comparisons).

Proof:
1. Apply the local retraction and section statements to the restricted canonical
   evaluation. If r and s are their respective inverse maps, then
   r = (s followed by R(g)) followed by r = s followed by (R(g) followed by r) = s.
   Thus r is a two-sided inverse and defines an isomorphism e with hom R(g).
2. Restrict derived internal Hom to U by 08DL and transport its arguments through
   eK and eN. Since F is K-injective, derivedInternalHom_obj_iso computes the target
   as Q Hom(P,F), giving b without resolving F again.
3. Ordinary evaluation is degreewise invertible for strictly perfect P. Hence the
   prescribed f is an isomorphism of complexes and Q(f) is an isomorphism.
4. Set a = e followed by b followed by the inverse of Q(f). Associativity and the
   inverse identity give R(g) followed by b = a followed by Q(f). No independently
   prescribed source comparison is required by the statement.
The two local inverse identities remain separate named obligations, following the
ordinary-model calculation of Stacks 08DQ.
-/
theorem exists_strictlyPerfect_kInjective_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    [F.IsKInjective]
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  -- Reuse the statement's models without elaborating their definitions a second time.
  intro R H D g
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  refine exists_iso_comparison_of_inverse (R.map g) (DerivedCategory.Q.map f) ?_ ?_ ?_
  · exact exists_strictlyPerfect_evaluation_local_retraction X K N U P hstrict _eK
  · exact exists_strictlyPerfect_evaluation_local_section X K N U P hstrict _eK
  let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))) _ _
      (inferInstanceAs (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))) :=
    inferInstanceAs (Category.{w}
      (DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))
  obtain ⟨c⟩ := derivedInternalHom_restrict_open X.toRingedSpace U K N
  obtain ⟨d⟩ := @derivedInternalHom_obj_iso.{u, w} (Over U) _
    ((Opens.grothendieckTopology X.toRingedSpace).over U)
    (X.sheaf.over U) (inferInstanceAs
      (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))
    (R.obj K) (R.obj N) P F inferInstance
    _eK.symm _eN.symm
  exact ⟨c.symm ≪≫ d⟩

end AlgebraicGeometry
