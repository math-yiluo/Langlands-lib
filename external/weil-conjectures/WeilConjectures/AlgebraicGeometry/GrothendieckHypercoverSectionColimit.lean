/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleSectionColimit
import all WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStages
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverTruncation
public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStages
/-! # Coherent-site continuity of the three hypercover section terms -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

private noncomputable def sectionComplexFunctor {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (V : FiniteSplitEtaleHypercover X) (q : ℕ) :
    (X.Etaleᵒᵖ ⥤ A) ⥤ ShortComplex A :=
  (Functor.whiskeringLeft _ _ _).obj V.simplicial.rightOp ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
    HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℕ) q

private theorem hypercover_term_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (V : FiniteSplitEtaleHypercover X) (n : ℕ) :
    CompactSpace (V.simplicial.obj (op (SimplexCategory.mk n))).left ∧
      QuasiSeparatedSpace (V.simplicial.obj (op (SimplexCategory.mk n))).left := by
  exact truncated_terms_qcqs (V.finiteTruncation n)
    (op ⟨SimplexCategory.mk n, Nat.le_refl n⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionComplexFunctor_map_tail
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]
    (q : ℕ) (i : I) (V : FiniteSplitEtaleHypercover (D.obj i).left) (j : Over i) :
    (sectionComplexFunctor A V q).map (tailSectionMap A D c F i j) =
      tailCochainMap A D c F q i V j := by
  ext <;> exact (Category.assoc _ _ _).symm

/-- The three cochain terms of a pulled-back stage hypercover are a filtered
colimit of their canonical later-stage counterparts.
Source: blueprint étale cohomology continuity, finite-cochain proof, paragraph 2;
the geometric finite-cover argument of étale section continuity, categorified
using exact filtered colimits. No assertion about derived functors is used.

Proof: the over category of a stage is cofiltered and its forgetful functor is
initial, so its pulled-back cone still has the given limit. In each relevant
degree the hypercover term is a finite coproduct of qcqs finite-presentation étale
objects and hence is itself qcqs of finite presentation. Its base changes form
a cartesian system with affine transitions and the stated limit. On the qcqs
étale basis, finite-presentation descent of objects, maps and finite covers
identifies the inverse-image presheaf with the filtered stage colimit. Pass to
sheaves by finite-cover refinement: the sheaf condition is the finite equalizer
of the two restriction maps to pairwise intersections. Filtered colimits in A
commute with these finite limits by AB5, so the unit comparison on each of the
three section objects is colimiting. The degreewise unit comparisons commute
with all cofaces and their alternating sums. They therefore form the asserted
short-complex diagram and cocone; the displayed isomorphisms identify its objects
with the actual stage section terms. Inverse-image composition and pullback
pasting identify the cocone components with tailCochainMap. At q=0 the incoming
differential is zero and the same degree-zero term can be used twice. Empty
étale objects have zero section objects by the empty-cover sheaf condition.
(auxiliary; not a blueprint node) -/
theorem exists_tail_section_shortComplex_colimit
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]
    (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) :
    ∃ (K : (Over i)ᵒᵖ ⥤ ShortComplex A)
      (e : ∀ j, K.obj j ≅ sectionShortComplex A
        ((Etale.upperStar A (D.obj j.unop.left).hom).obj F)
        (tailHypercover D i V j.unop) q)
      (ν : K ⟶ (Functor.const (Over i)ᵒᵖ).obj
        (sectionShortComplex A ((Etale.upperStar A c.pt.hom).obj F)
          (V.baseChange (coneProjection D c i)) q)),
      (∀ j, ν.app j = (e j).hom ≫ tailCochainMap A D c F q i V j.unop) ∧
        Nonempty (IsColimit (ShortComplex.π₁.mapCocone (Cocone.mk _ ν))) ∧
        Nonempty (IsColimit (ShortComplex.π₂.mapCocone (Cocone.mk _ ν))) ∧
        Nonempty (IsColimit (ShortComplex.π₃.mapCocone (Cocone.mk _ ν))) := by
  obtain ⟨P, e, ν, hν, hcol⟩ := exists_tail_section_colimit A D c F hc i
  let T := sectionComplexFunctor A V q
  let K := P ⋙ T
  let ν' : K ⟶ (Functor.const (Over i)ᵒᵖ).obj
      (sectionShortComplex A ((Etale.upperStar A c.pt.hom).obj F)
        (V.baseChange (coneProjection D c i)) q) := Functor.whiskerRight ν T
  refine ⟨K, (fun j ↦ T.mapIso (e j)), ν', ?_, ?_, ?_, ?_⟩
  · intro j
    change T.map (ν.app j) = _
    rw [hν, T.map_comp, sectionComplexFunctor_map_tail]
    rfl
  · obtain ⟨hcU, hsU⟩ := hypercover_term_qcqs V ((ComplexShape.up ℕ).prev q)
    exact hcol _ hcU hsU
  · obtain ⟨hcU, hsU⟩ := hypercover_term_qcqs V q
    exact hcol _ hcU hsU
  · obtain ⟨hcU, hsU⟩ := hypercover_term_qcqs V ((ComplexShape.up ℕ).next q)
    exact hcol _ hcU hsU

end AlgebraicGeometry.FiniteSplitEtaleHypercover
