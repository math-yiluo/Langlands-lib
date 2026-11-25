/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ArrowExactColimits
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Kernels and cokernels of ind-constructible sheaves

The square category is `CostructuredArrow ι.mapArrow (Arrow.mk f)`, where ι is the
constructible inclusion. Its tautological arrow cocone is Mathlib's pointwise left
extension cocone. Applying `ker` and `coker` gives exactly the canonical cocones at
ker(f) and coker(f); asserting their colimit properties fixes the comparisons themselves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Source projection of the category of squares from arrows of C to f onto J(B).
This is the standard comma-category map induced by the source functors. -/
def indHeartSquareSource {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    CostructuredArrow ι.mapArrow (Arrow.mk f) ⥤ CostructuredArrow ι B :=
  CostructuredArrow.map₂ (F := Arrow.leftFunc) (G := Arrow.leftFunc) (𝟙 _) (𝟙 _)

/-- Target projection of the category of squares from arrows of C to f onto J(B').
This is the standard comma-category map induced by the target functors. -/
def indHeartSquareTarget {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    CostructuredArrow ι.mapArrow (Arrow.mk f) ⥤ CostructuredArrow ι B' :=
  CostructuredArrow.map₂ (F := Arrow.rightFunc) (G := Arrow.rightFunc) (𝟙 _) (𝟙 _)

/-- The canonical cocone of constructible squares at f, with legs the squares themselves. -/
def indHeartSquareCocone {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    Cocone (CostructuredArrow.proj ι.mapArrow (Arrow.mk f) ⋙ ι.mapArrow) :=
  (Functor.LeftExtension.mk (𝟭 (Arrow M)) ι.mapArrow.rightUnitor.inv).coconeAt
    (Arrow.mk f)

set_option backward.isDefEq.respectTransparency false in
private theorem squareSource_final {C : Type u} [Category.{v} C]
    {M : Type w} [Category.{t} M] (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    (indHeartSquareSource ι f).Final := by
  constructor
  intro j
  let q : CostructuredArrow ι.mapArrow (Arrow.mk f) :=
    CostructuredArrow.mk (Y := Arrow.mk (𝟙 j.left))
      (Arrow.homMk j.hom (j.hom ≫ f) (by simp [Functor.mapArrow]))
  let a : StructuredArrow j (indHeartSquareSource ι f) :=
    StructuredArrow.mk (Y := q) (CostructuredArrow.homMk (𝟙 j.left) (by simp [q,
      indHeartSquareSource]))
  have ha (b : StructuredArrow j (indHeartSquareSource ι f)) : Nonempty (a ⟶ b) := by
    dsimp only [a, q]
    refine ⟨StructuredArrow.homMk (CostructuredArrow.homMk
      (Arrow.homMk b.hom.left (b.hom.left ≫ b.right.left.hom) (by simp)) ?_) ?_⟩
    · apply Arrow.hom_ext
      · simpa [q, indHeartSquareSource] using b.hom.w
      · change ι.map (b.hom.left ≫ b.right.left.hom) ≫ b.right.hom.right = j.hom ≫ f
        have hw : ι.map b.right.left.hom ≫ b.right.hom.right =
            b.right.hom.left ≫ f := b.right.hom.w.symm
        rw [ι.map_comp, Category.assoc, hw, ← Category.assoc]
        simpa [indHeartSquareSource] using congrArg (fun z ↦ z ≫ f) b.hom.w
    · apply CostructuredArrow.hom_ext
      simp [indHeartSquareSource]
  let : Nonempty (StructuredArrow j (indHeartSquareSource ι f)) := ⟨a⟩
  apply zigzag_isConnected
  intro b c
  exact (Relation.ReflTransGen.single (show Zag b a from Or.inr (ha b))).trans
    (Relation.ReflTransGen.single (show Zag a c from Or.inl (ha c)))

set_option backward.isDefEq.respectTransparency false in
private theorem squareTarget_final {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasZeroObject C]
    {M : Type w} [Category.{t} M] [HasZeroMorphisms M] (ι : C ⥤ M)
    [Functor.PreservesZeroMorphisms ι] {B B' : M} (f : B ⟶ B') :
    (indHeartSquareTarget ι f).Final := by
  constructor
  intro j
  let q : CostructuredArrow ι.mapArrow (Arrow.mk f) :=
    CostructuredArrow.mk (Y := Arrow.mk (0 : (0 : C) ⟶ j.left))
      (Arrow.homMk 0 j.hom (by simp [Functor.mapArrow]))
  let a : StructuredArrow j (indHeartSquareTarget ι f) :=
    StructuredArrow.mk (Y := q) (CostructuredArrow.homMk (𝟙 j.left) (by simp [q,
      indHeartSquareTarget]))
  have ha (b : StructuredArrow j (indHeartSquareTarget ι f)) : Nonempty (a ⟶ b) := by
    dsimp only [a, q]
    refine ⟨StructuredArrow.homMk (CostructuredArrow.homMk
      (Arrow.homMk 0 b.hom.left (by simp)) ?_) ?_⟩
    · apply Arrow.hom_ext
      · simp
      · simpa [q, indHeartSquareTarget] using b.hom.w
    · apply CostructuredArrow.hom_ext
      simp [indHeartSquareTarget]
  let : Nonempty (StructuredArrow j (indHeartSquareTarget ι f)) := ⟨a⟩
  apply zigzag_isConnected
  intro b c
  exact (Relation.ReflTransGen.single (show Zag b a from Or.inr (ha b))).trans
    (Relation.ReflTransGen.single (show Zag a c from Or.inl (ha c)))

set_option backward.isDefEq.respectTransparency false in
private theorem mapArrow_preserves {C : Type u} [Category.{v} C]
    {M : Type w} [Category.{t} M] (ι : C ⥤ M)
    {J : Type*} [Category J] [HasColimitsOfShape J C] [PreservesColimitsOfShape J ι] :
    PreservesColimitsOfShape J ι.mapArrow := by
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨Comma.fstSndJointlyReflectColimit ?_ ?_⟩
  · exact isColimitOfPreserves ι (isColimitOfPreserves Arrow.leftFunc hc)
  · exact isColimitOfPreserves ι (isColimitOfPreserves Arrow.rightFunc hc)

private theorem square_filtered {C : Type u} [Category.{v} C]
    {M : Type w} [Category.{t} M] (ι : C ⥤ M)
    [HasFiniteColimits C] [PreservesFiniteColimits ι] {B B' : M} (f : B ⟶ B') :
    IsFiltered (CostructuredArrow ι.mapArrow (Arrow.mk f)) := by
  have : PreservesFiniteColimits ι.mapArrow := ⟨fun _ ↦ mapArrow_preserves ι⟩
  exact IsFiltered.of_hasFiniteColimits _

private theorem square_small {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C]
    {M : Type w} [Category.{v} M] (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    EssentiallySmall.{v} (CostructuredArrow ι.mapArrow (Arrow.mk f)) := by
  have : EssentiallySmall.{v} (Arrow C) :=
    EssentiallySmall.mk' (Functor.mapArrowEquivalence (equivSmallModel C))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem square_isColimit {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasZeroObject C]
    {M : Type w} [Category.{t} M] [HasZeroMorphisms M] (ι : C ⥤ M)
    [Functor.PreservesZeroMorphisms ι] {B B' : M} (f : B ⟶ B')
    (hB : ι.isDenseAt B) (hB' : ι.isDenseAt B') :
    Nonempty (IsColimit (indHeartSquareCocone ι f)) := by
  have : (indHeartSquareSource ι f).Final := squareSource_final ι f
  have : (indHeartSquareTarget ι f).Final := squareTarget_final ι f
  refine ⟨Comma.fstSndJointlyReflectColimit ?_ ?_⟩
  · let c := (Functor.LeftExtension.mk (𝟭 M) ι.rightUnitor.inv).coconeAt B
    have hc : IsColimit c := hB.some
    have h := (Functor.Final.isColimitWhiskerEquiv (indHeartSquareSource ι f) c).symm hc
    exact h.ofIsoColimit (Cocone.ext (Iso.refl _) (by intro j; simp
      [c, indHeartSquareCocone, indHeartSquareSource]))
  · let c := (Functor.LeftExtension.mk (𝟭 M) ι.rightUnitor.inv).coconeAt B'
    have hc : IsColimit c := hB'.some
    have h := (Functor.Final.isColimitWhiskerEquiv (indHeartSquareTarget ι f) c).symm hc
    exact h.ofIsoColimit (Cocone.ext (Iso.refl _) (by intro j; simp
      [c, indHeartSquareCocone, indHeartSquareTarget]))

/-- All clauses for a fixed coefficient ring: P_f is essentially small and filtered,
its two projections are final, its canonical arrow cocone has colimit f, and applying
ker and coker gives colimit cocones at the ambient kernel and cokernel of f. Both
objects belong to the same replete filtered-colimit closure of constructible modules.
Smallness is relative to u+1, as in the canonical-presentation dependency; universal
properties on the full category are equivalent to those on any small skeleton. -/
def IndHeartKernelsCokernelsAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ (B B' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : B ⟶ B'),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B' →
    EssentiallySmall.{u + 1} (CostructuredArrow
      (ObjectProperty.ι (IsConstantModelConstructible Λ X)).mapArrow (Arrow.mk f)) ∧
    IsFiltered (CostructuredArrow
      (ObjectProperty.ι (IsConstantModelConstructible Λ X)).mapArrow (Arrow.mk f)) ∧
    (indHeartSquareSource (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f).Final ∧
    (indHeartSquareTarget (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f).Final ∧
    Nonempty (IsColimit
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f)) ∧
    Nonempty (IsColimit (Functor.mapCocone (ker (C := _))
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f))) ∧
    Nonempty (IsColimit (Functor.mapCocone (coker (C := _))
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f))) ∧
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (kernel f) ∧
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (cokernel f)

set_option backward.isDefEq.respectTransparency false in
private theorem assertions_of_closure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (hsmall : EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X))
    (hab : Nonempty (Abelian (ConstantModelConstructible Λ X)))
    (hfin : PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)))
    (hker : ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ X))
    (hcoker : ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ X))
    (hpres : IndHeartCanonicalPresentationAssertions Λ X) :
    IndHeartKernelsCokernelsAssertions Λ X := by
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstantModelConstructible Λ X
  let M := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : EssentiallySmall.{u + 1} P.FullSubcategory := hsmall
  let : Abelian P.FullSubcategory := hab.some
  let : PreservesFiniteColimits P.ι := hfin
  let : P.IsClosedUnderKernels := hker
  let : P.IsClosedUnderCokernels := hcoker
  intro B B' f hB hB'
  let : EssentiallySmall.{u + 1} (CostructuredArrow P.ι.mapArrow (Arrow.mk f)) :=
    square_small P.ι f
  let : IsFiltered (CostructuredArrow P.ι.mapArrow (Arrow.mk f)) := square_filtered P.ι f
  have hs := squareSource_final P.ι f
  have ht := squareTarget_final P.ι f
  have hf := square_isColimit P.ι f (hpres B hB).2.2.1 (hpres B' hB').2.2.1
  let J := CostructuredArrow P.ι.mapArrow (Arrow.mk f)
  have : HasColimitsOfSize.{u + 1, u + 1} M := IsGrothendieckAbelian.hasColimits M
  let : HasColimitsOfShape J M := HasColimitsOfShape.of_essentiallySmall M J
  have : IsFiltered (SmallModel.{u + 1} J) :=
    IsFiltered.of_equivalence (equivSmallModel.{u + 1} J)
  let : HasExactColimitsOfShape J M :=
    HasExactColimitsOfShape.of_domain_equivalence M (equivSmallModel.{u + 1} J).symm
  obtain ⟨hk, hq⟩ := arrow_exact_colimits M J
  let hk_pres : PreservesColimit
      (CostructuredArrow.proj P.ι.mapArrow (Arrow.mk f) ⋙ P.ι.mapArrow)
      (ker (C := M)) := hk.preservesColimit
  let hq_pres : PreservesColimit
      (CostructuredArrow.proj P.ι.mapArrow (Arrow.mk f) ⋙ P.ι.mapArrow)
      (coker (C := M)) := hq.preservesColimit
  have hkf := @isColimitOfPreserves _ _ _ _ _ _ _
    (ker (C := M)) _ hf.some hk_pres
  have hqf := @isColimitOfPreserves _ _ _ _ _ _ _
    (coker (C := M)) _ hf.some hq_pres
  refine ⟨inferInstance, inferInstance, hs, ht, hf, ⟨hkf⟩, ⟨hqf⟩, ?_, ?_⟩
  · exact ObjectProperty.of_essentiallySmall_index
      ⟨_, _, hkf⟩ (fun j ↦ P.prop_kernel _ j.left.left.property j.left.right.property)
  · exact ObjectProperty.of_essentiallySmall_index
      ⟨_, _, hqf⟩ (fun j ↦ P.prop_cokernel _ j.left.left.property j.left.right.property)

set_option backward.isDefEq.respectTransparency false in
private theorem assertions_of_ring (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)]
    (hR : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ R = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (hpres : IndHeartCanonicalPresentationAssertions
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) X) :
    IndHeartKernelsCokernelsAssertions
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) X := by
  obtain ⟨hk, hq, _, ha, _, hf, _⟩ := (coefficientHeart_closure ℓ R hR).2 X
  exact assertions_of_closure _ X (coefficientHeart_essentiallySmall ℓ R hR X)
    ha hf hk hq hpres

/-- Kernels and cokernels in the ind-constructible heart, with the canonical filtered
presentation by constructible squares, for both canonical coefficient rings. -/
theorem indHeart_kernelsCokernels
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartKernelsCokernelsAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartKernelsCokernelsAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  obtain ⟨hE, hΩ⟩ := indHeart_canonicalPresentation ℓ p k hp hne X
  constructor
  · intro E
    exact assertions_of_ring ℓ (Profinite.padicSubfieldCondensedRing ℓ E.val)
      (Or.inl ⟨E.val, E.property, rfl⟩) X (hE E)
  · exact assertions_of_ring ℓ (Profinite.padicAlgClCondensedRing ℓ)
      (Or.inr rfl) X hΩ

end AlgebraicGeometry.ProEtale
