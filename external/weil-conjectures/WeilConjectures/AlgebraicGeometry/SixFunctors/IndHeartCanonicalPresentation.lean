/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Canonical presentations of ind-constructible sheaves

For the two canonical condensed coefficient rings, every ind-constructible sheaf `B` is the
filtered colimit of all constructible modules mapping to it, and every small filtered
constructible presentation of `B` is final in this category
(`AlgebraicGeometry.ProEtale.indHeart_canonicalPresentation`).

## Implementation details

`CostructuredArrow` is exactly the category of constructible modules mapping to B.
`Functor.isDenseAt` asserts the colimit property for its tautological cocone, whose
leg at (C,c) is c. Small diagrams and essential smallness use universe u+1, as in
`IndHeartFullFaithfulnessAssertions`. The universal property
over the full essentially small category is equivalent to the one over a small skeleton.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical-presentation assertions for the coefficient ring object Λ on X: for every
ind-constructible `B`, the category J(B) of constructible modules mapping to `B` is essentially
small and filtered, its tautological cocone (with leg `c` at `(C, c)`) is a colimit, and every
small filtered constructible colimit presentation of `B` induces a final functor to J(B). -/
def IndHeartCanonicalPresentationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
    EssentiallySmall.{u + 1}
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    IsFiltered
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    (ObjectProperty.ι (IsConstantModelConstructible Λ X)).isDenseAt B ∧
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (pres : ObjectProperty.ColimitOfShape (IsConstantModelConstructible Λ X) I B),
      pres.toCostructuredArrow.Final

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A filtered presentation of `B` by finitely presentable objects of `P` is final in the
category of objects of `P` over `B`. -/
private theorem final_constructiblePresentation
    {C : Type*} [Category.{u + 1} C] (P : ObjectProperty C)
    (hP : ∀ A : P.FullSubcategory, IsFinitelyPresentable.{u + 1} A.obj)
    {B : C} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (pres : P.ColimitOfShape I B) : pres.toCostructuredArrow.Final := by
  classical
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro f
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit f.hom
    exact ⟨i, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
  · intro f i g h
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨j, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit pres.isColimit
      g.left.hom h.left.hom ((CostructuredArrow.w g).trans (CostructuredArrow.w h).symm)
    refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    change g.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) =
      h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b)
    calc
      _ = (g.left.hom ≫ pres.diag.map a) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = (h.left.hom ≫ pres.diag.map b) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [hab]
      _ = h.left.hom ≫ pres.diag.map (b ≫ IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) := by
        rw [IsFiltered.coeq_condition a b]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble a canonical colimit from essential smallness and finite presentation. -/
private theorem canonicalPresentation_of_finitePresentation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (hsmall : EssentiallySmall.{u + 1}
      (ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X)))
    (hfp : ∀ A : ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X),
      IsFinitelyPresentable.{u + 1} A.obj) :
    IndHeartCanonicalPresentationAssertions Λ X := by
  classical
  intro B hB
  have := hsmall
  obtain ⟨I, hI, hfI, pres, hp⟩ := hB
  let : SmallCategory I := hI
  have : IsFiltered I := hfI
  let p : ObjectProperty.ColimitOfShape (IsConstantModelConstructible Λ X) I B :=
    ⟨pres, hp⟩
  have := final_constructiblePresentation (IsConstantModelConstructible Λ X) hfp p
  refine ⟨inferInstance, IsFiltered.of_final p.toCostructuredArrow, ?_, ?_⟩
  · exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩
  · intro J _ _ q
    exact final_constructiblePresentation (IsConstantModelConstructible Λ X) hfp q

/-- For the two canonical condensed coefficient rings, every ind-constructible sheaf
has its canonical filtered presentation by all constructible objects mapping to it;
every small filtered constructible presentation induces a final functor to this category. -/
theorem indHeart_canonicalPresentation
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartCanonicalPresentationAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartCanonicalPresentationAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  have hsetting : 0 < p ∧ p ≠ ℓ := ⟨hp, hne⟩
  clear hsetting
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  obtain ⟨hE, hbar⟩ := indHeart_fullFaithfulness ℓ X
  constructor
  · intro E
    apply canonicalPresentation_of_finitePresentation _ X _ (hE E).1
    exact coefficientHeart_essentiallySmall ℓ
      (Profinite.padicSubfieldCondensedRing.{u} ℓ E)
      (Or.inl ⟨E.1, E.2, rfl⟩) X
  · apply canonicalPresentation_of_finitePresentation _ X _ hbar.1
    exact coefficientHeart_essentiallySmall ℓ (Profinite.padicAlgClCondensedRing.{u} ℓ)
      (Or.inr rfl) X

end AlgebraicGeometry.ProEtale
