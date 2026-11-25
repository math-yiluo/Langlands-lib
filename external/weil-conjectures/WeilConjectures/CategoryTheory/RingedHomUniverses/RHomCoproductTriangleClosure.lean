/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RHomContinuityTriangleClosure
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Triangle closure of bounded-target internal-Hom coproduct continuity

Source: Stacks Project, Cohomology on Sites, Tag 08JC, and the formal bounded-target
closure argument extracted from Bhatt--Scholze, Lemmas 6.3.14 and 6.8.12
(blueprint: lem-weil-pbc-rhom-coproduct-triangle-closure).

The predicate below is the P introduced in the statement. Its comparison is the image
under Q of the actual complex-level colimit.post for the existing functor homFixed.
The final theorem transports this comparison to an actual derived coproduct. Every representative
of the source is allowed, and the target bound is cohomological, not termwise.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

-- The bounded-coproduct predicates need termwise colimits of complexes; prefer that
-- instance so the search does not time out through the cocompleteness instances.
attribute [local instance high] HomologicalComplex.instHasColimitsOfShape

/-- The property P of the node: continuity for all uniformly cohomologically bounded-below
discrete complex diagrams, and a uniform lower-bound offset for the target variable.
Source: Stacks 08JC and the bounded-target closure extraction in the node
(blueprint: lem-weil-pbc-rhom-coproduct-triangle-closure).

The canonical map is Q(colimit.post M (homFixed L)); its coprojection at i is the
localized Hom map of the target coprojection. Exact termwise sheaf colimits compute
its source. Quantification over source representatives avoids a choice of an object
or a noncanonical comparison. The colimit structures quantified here exist for small
module-sheaf diagrams and are only the structures needed to form the displayed map. -/
def BoundedCoproductHomContinuous (A : D.{c, v, r, w} J R) : Prop :=
  (∀ (L : Complex.{c, v, r} J R), Nonempty (DerivedCategory.Q.obj L ≅ A) →
    ∀ (I : Type (max c v r))
      [HasColimitsOfShape (Discrete I) (Modules.{c, v, r} J R)]
      (M : Discrete I ⥤ Complex.{c, v, r} J R) (b : ℤ),
      (∀ i : Discrete I, (DerivedCategory.Q.obj (M.obj i)).IsGE b) →
        IsIso (DerivedCategory.Q.map (colimit.post M
          (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)))) ∧
  ∃ d : ℤ, ∀ (b : ℤ) (N : D.{c, v, r, w} J R),
    N.IsGE b → ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d)

private theorem continuous_of_iso {A B : D.{c, v, r, w} J R} (e : A ≅ B)
    (hA : BoundedCoproductHomContinuous.{c, v, r, w} J R A) :
    BoundedCoproductHomContinuous.{c, v, r, w} J R B := by
  refine ⟨?_, ?_⟩
  · intro L hL
    exact hA.1 L (hL.map (fun eL ↦ eL ≪≫ e.symm))
  · obtain ⟨d, hd⟩ := hA.2
    refine ⟨d, fun b N hN ↦ ?_⟩
    have := hd b N hN
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
        e.symm.op).app N) (b + d)

private theorem continuous_shift (A : D.{c, v, r, w} J R)
    (hA : BoundedCoproductHomContinuous.{c, v, r, w} J R A) (n : ℤ) :
    BoundedCoproductHomContinuous.{c, v, r, w} J R (A⟦n⟧) := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ?_⟩
  · intro L hL I _ M b hM
    obtain ⟨eL⟩ := hL
    let K : Complex.{c, v, r} J R := L⟦-n⟧
    let eK : DerivedCategory.Q.obj K ≅ A :=
      (DerivedCategory.Q.commShiftIso (-n)).app L ≪≫
        (shiftFunctor _ (-n)).mapIso eL ≪≫ (shiftEquiv _ n).unitIso.symm.app A
    have hK : QuasiIso (colimit.post M
        (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R K)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp (hA.1 K ⟨eK⟩ I M b hM)
    let F := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R K
    let G := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L
    let eKL : DerivedCategory.Q.obj (K⟦n⟧) ≅ DerivedCategory.Q.obj L :=
      DerivedCategory.Q.mapIso ((shiftEquiv _ n).counitIso.app L)
    let eD : (F ⋙ shiftFunctor _ (-n)) ⋙ DerivedCategory.Q ≅ G ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerLeft F (DerivedCategory.Q.commShiftIso (-n)) ≪≫
      Functor.isoWhiskerRight (homFixed_derivedIso.{c, v, r, w} J R K).symm
        (shiftFunctor _ (-n)) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q
        (sourceShift.{c, v, r, w} J R (DerivedCategory.Q.obj K) n) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q
        (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
          (((DerivedCategory.Q.commShiftIso n).app K).symm ≪≫ eKL).symm.op)) ≪≫
      homFixed_derivedIso.{c, v, r, w} J R L
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact post_quasiIso_derivedIso _ _ eD M
      (post_quasiIso_shift _ M (-n) hK)
  · obtain ⟨d, hd⟩ := hA.2
    exact ⟨d + n, bound_sourceShift.{c, v, r, w} J R A d hd n⟩

private theorem continuous_zero :
    BoundedCoproductHomContinuous.{c, v, r, w} J R 0 := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro L hL I _ M b _
    have hs := isZero_Q_colimit (M ⋙
      WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)
      (fun i ↦ zero_source_hom_isZero.{c, v, r, w} J R L (M.obj i) hL)
    have ht := zero_source_hom_isZero.{c, v, r, w} J R L (colimit M) hL
    exact hs.isIso ht _
  · intro b N _
    simpa only [add_zero] using bound_zero.{c, v, r, w} J R b N

private theorem continuous_middle
    (T : Pretriangulated.Triangle (D.{c, v, r, w} J R))
    (hT : T ∈ distTriang (D.{c, v, r, w} J R))
    (hA : BoundedCoproductHomContinuous.{c, v, r, w} J R T.obj₁)
    (hC : BoundedCoproductHomContinuous.{c, v, r, w} J R T.obj₃) :
    BoundedCoproductHomContinuous.{c, v, r, w} J R T.obj₂ := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ?_⟩
  · intro L hL I _ M b hM
    obtain ⟨eL⟩ := hL
    obtain ⟨K, f, ⟨eK⟩, ⟨eC⟩⟩ := triangle_model_with_middle T hT L eL
    let t := CochainComplex.mappingCone.triangle f
    have ht := DerivedCategory.mappingCone_triangle_distinguished f
    have hrot : DerivedCategory.Q.mapTriangle.obj t.rotate ∈
        distTriang (D.{c, v, r, w} J R) :=
      Pretriangulated.isomorphic_distinguished _ (Pretriangulated.rot_of_distTriang _ ht) _
        (DerivedCategory.Q.mapTriangleRotateIso.app t).symm
    have hinv : DerivedCategory.Q.mapTriangle.obj t.invRotate ∈
        distTriang (D.{c, v, r, w} J R) :=
      Pretriangulated.isomorphic_distinguished _ (Pretriangulated.inv_rot_of_distTriang _ ht) _
        (DerivedCategory.Q.mapTriangleInvRotateIso.app t).symm
    have hcont (A : D.{c, v, r, w} J R)
        (hA : BoundedCoproductHomContinuous.{c, v, r, w} J R A)
        (B : Complex.{c, v, r} J R) (eB : DerivedCategory.Q.obj B ≅ A) :
        QuasiIso (colimit.post M
          (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R B)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp (hA.1 B ⟨eB⟩ I M b hM)
    let H := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact post_quasiIso_fiveLemma (H (K⟦(1 : ℤ)⟧))
      (H (CochainComplex.mappingCone f)) (H L) (H K)
      (H ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧))
      (homFixed_leftMap.{c, v, r} J R t.mor₃) (homFixed_leftMap.{c, v, r} J R t.mor₂)
      (homFixed_leftMap.{c, v, r} J R t.mor₁) (homFixed_leftMap.{c, v, r} J R t.invRotate.mor₁)
      (homFixed_homology_exact.{c, v, r, w} J R t.rotate hrot)
      (homFixed_homology_exact.{c, v, r, w} J R t ht)
      (homFixed_homology_exact.{c, v, r, w} J R t.invRotate hinv) M
      (hcont (T.obj₁⟦(1 : ℤ)⟧) (continuous_shift.{c, v, r, w} J R T.obj₁ hA 1) _
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K ≪≫
          (shiftFunctor _ (1 : ℤ)).mapIso eK))
      (hcont T.obj₃ hC _ eC) (hcont T.obj₁ hA K eK)
      (hcont (T.obj₃⟦(-1 : ℤ)⟧) (continuous_shift.{c, v, r, w} J R T.obj₃ hC (-1)) _
        ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone f) ≪≫
          (shiftFunctor _ (-1 : ℤ)).mapIso eC))
  · obtain ⟨dA, hdA⟩ := hA.2
    obtain ⟨dC, hdC⟩ := hC.2
    exact ⟨min dA dC, bound_triangle.{c, v, r, w} J R T hT dA dC hdA hdC⟩

/-- The sources satisfying P contain zero, are invariant under isomorphisms, and form a
triangulated subcategory. The source shift by n takes any lower-bound offset d to d+n.
Finite iterated extensions of isomorphic shifts of any family satisfying P satisfy P.
Source: Stacks 08JC, with exact coproducts (03DB), the cohomology long exact
sequence (05RS), and the five lemma (05QB)
(blueprint: lem-weil-pbc-rhom-coproduct-triangle-closure).

Proof:
1. Exact coproducts of module sheaves commute with cycles, boundaries and
cohomology. Thus termwise colimits preserve quasi-isomorphisms and common cohomological
lower bounds; the specified complex models compute the comparisons in D(O).
2. Hom(0,N) is zero, its comparison is the zero isomorphism, and offset 0 works.
Precomposition with a source isomorphism identifies both comparison maps and bounds.
3. The signed, natural source-shift isomorphism identifies H(A[n],N) with H(A,N)[-n].
Termwise colimits commute with shifts and exact coproducts commute with cohomology.
The fixed localization comparison transports the shifted continuity comparison degreewise.
Since H^q(K[-n])=H^(q-n)(K), the new offset is d+n.
4. Present the triangle by a cone with the requested middle representative L.
Contravariant Hom exactness for this cone triangle and its two rotations gives
three exact middle cohomology sequences. Naturality of the fixed localization
comparison identifies their arrows with actual homFixed precomposition maps.
5. These form a five-term row with sources K[1], Cone(f), L, K, Cone(f)[-1].
The four outer comparisons are quasi-isomorphisms by P(A), P(C), and shift closure.
Exact coproducts commute with cohomology; the five lemma therefore makes
the comparison for L a quasi-isomorphism, and hence an isomorphism in D(O).
6. Exactness of the three middle cohomology terms gives B the offset min(d_A,d_C),
uniformly in b,N. This proves both clauses of P for the middle vertex.
7. Rotate the triangle. The other two cases follow with offsets min(d_C-1,d_B)
and min(d_B,d_A+1). Thus two-out-of-three holds at every position.
8. Induct on a finite construction. Use zero and source isomorphism invariance at the
base, source-shift closure at each shift, and two-out-of-three at each triangle.
Equivalently, shifts and isomorphisms can be moved through triangles, so finite
constructions are finite iterated extensions of isomorphic shifted initial sources. -/
theorem boundedCoproductHomContinuous_triangle_closure :
    ObjectProperty.IsClosedUnderIsomorphisms
      (BoundedCoproductHomContinuous.{c, v, r, w} J R) ∧
    ObjectProperty.IsTriangulated (BoundedCoproductHomContinuous.{c, v, r, w} J R) ∧
    (∀ (A : D.{c, v, r, w} J R), BoundedCoproductHomContinuous.{c, v, r, w} J R A →
      ∀ d : ℤ,
      (∀ (b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
        ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d)) →
      ∀ (n b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
        ((hom.{c, v, r, w} J R (A⟦n⟧)).obj N).IsGE (b + (d + n))) ∧
    (∀ S : ObjectProperty (D.{c, v, r, w} J R),
      S ≤ BoundedCoproductHomContinuous.{c, v, r, w} J R → ∀ n : ℕ,
        (S.shiftClosure ℤ).extensionProductIter n ≤
          BoundedCoproductHomContinuous.{c, v, r, w} J R) := by
  let hIso : ObjectProperty.IsClosedUnderIsomorphisms
      (BoundedCoproductHomContinuous.{c, v, r, w} J R) :=
    ⟨fun e hA ↦ continuous_of_iso.{c, v, r, w} J R e hA⟩
  suffices hTri : ObjectProperty.IsTriangulated
      (BoundedCoproductHomContinuous.{c, v, r, w} J R) by
    let := hTri
    refine ⟨hIso, hTri, ?_, ?_⟩
    · intro A _ d hd n b N hN
      exact bound_sourceShift.{c, v, r, w} J R A d hd n b N hN
    · intro S hS n
      exact (S.shiftClosure ℤ).extensionProductIter_le_of_isTriangulatedClosed₂
        ((S.shiftClosure_le_iff _).2 hS) n
  refine
    { exists_zero := ⟨0, isZero_zero _, continuous_zero.{c, v, r, w} J R⟩
      isStableUnderShiftBy := fun n ↦
        ⟨fun A hA ↦ continuous_shift.{c, v, r, w} J R A hA n⟩
      ext₂' := ?_ }
  intro T hT hA hC
  exact ⟨T.obj₂, continuous_middle.{c, v, r, w} J R T hT hA hC, ⟨Iso.refl _⟩⟩

/-- The complex-level coproduct property gives preservation of each actual derived
coproduct of uniformly bounded-below objects.
Source: Stacks 07D9 and the representative comparison for RHom
(blueprint: lem-weil-pbc-rhom-coproduct-triangle-closure).
Proof: choose source and target complex representatives. Their termwise coproduct is
also a derived coproduct. The normalized Hom comparison identifies Q followed by RHom
with homFixed followed by Q. The latter carries the coproduct cocone to a colimit:
its comparison factors as the coproduct comparison for Q followed by the localized
homFixed comparison. Both factors are invertible. Transport along the representative
isomorphisms and the natural Hom comparison. -/
theorem boundedCoproductHomContinuous_preservesColimit
    (K : D.{c, v, r, w} J R)
    (hK : BoundedCoproductHomContinuous.{c, v, r, w} J R K)
    (I : Type (max c v r)) (M : I → D.{c, v, r, w} J R) (b : ℤ)
    (hM : ∀ i, (M i).IsGE b) :
    PreservesColimit (Discrete.functor M) (hom.{c, v, r, w} J R K) := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let : Abelian.HasKInjectiveResolutions (Modules.{c, v, r} J R) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max c v r}
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let L := Q.objPreimage K
  let E (i : I) := Q.objPreimage (M i)
  let C := Discrete.functor E
  let F := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L
  have hb (i : Discrete I) : (Q.obj (C.obj i)).IsGE b :=
    DerivedCategory.TStructure.t.isGE_of_iso (Q.objObjPreimageIso (M i.as)).symm b
  have hc : IsIso (Q.map (colimit.post C F)) :=
    hK.1 L ⟨Q.objObjPreimageIso K⟩ I C b hb
  have : IsIso (colimit.post C (F ⋙ Q)) := by
    rw [← colimit.post_post]
    infer_instance
  have : PreservesColimit C (F ⋙ Q) := preservesColimit_of_isIso_post (F ⋙ Q) C
  let e : Q ⋙ hom.{c, v, r, w} J R K ≅ F ⋙ Q :=
    Functor.isoWhiskerLeft Q
      (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
        (Q.objObjPreimageIso K).op)) ≪≫ homFixed_derivedIso.{c, v, r, w} J R L
  have : PreservesColimit C (Q ⋙ hom.{c, v, r, w} J R K) :=
    preservesColimit_of_natIso C e.symm
  have : PreservesColimit (C ⋙ Q) (hom.{c, v, r, w} J R K) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves Q (colimit.isColimit C))
      (isColimitOfPreserves (Q ⋙ hom.{c, v, r, w} J R K) (colimit.isColimit C))
  exact preservesColimit_of_iso_diagram _
    (Discrete.natIso (F := C ⋙ Q) (G := Discrete.functor M)
      fun i ↦ Q.objObjPreimageIso (M i.as))

/-- Derived coproduct preservation and a uniform lower bound imply the representative
comparison used by the triangle closure theorem.
Source: Stacks 07D9; the normalized Hom-resolution comparison
(blueprint: lem-weil-pbc-rhom-coproduct-triangle-closure).
Proof: identify Q followed by derived Hom with homFixed followed by Q. The derived
preservation assumption gives preservation for a discrete diagram of representatives.
The post comparison for the composite factors through the invertible post comparison
for Q. Cancel that factor to obtain the localized homFixed comparison. -/
theorem boundedCoproductHomContinuous_of_preservesColimits
    (K : D.{c, v, r, w} J R)
    (hpres : ∀ (I : Type (max c v r)) (M : I → D.{c, v, r, w} J R) (b : ℤ),
      (∀ i, (M i).IsGE b) →
        PreservesColimit (Discrete.functor M) (hom.{c, v, r, w} J R K))
    (hbound : ∃ d : ℤ, ∀ (b : ℤ) (N : D.{c, v, r, w} J R),
      N.IsGE b → ((hom.{c, v, r, w} J R K).obj N).IsGE (b + d)) :
    BoundedCoproductHomContinuous.{c, v, r, w} J R K := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let : Abelian.HasKInjectiveResolutions (Modules.{c, v, r} J R) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max c v r}
  refine ⟨?_, hbound⟩
  intro L hL I _ M b hb
  obtain ⟨eL⟩ := hL
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let F := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L
  have : PreservesColimit (Discrete.functor fun i : I ↦ Q.obj (M.obj ⟨i⟩))
      (hom.{c, v, r, w} J R K) := hpres I _ b fun i ↦ hb ⟨i⟩
  let eM : Discrete.functor (fun i : I ↦ Q.obj (M.obj ⟨i⟩)) ≅ M ⋙ Q :=
    Discrete.natIso fun _ ↦ Iso.refl _
  have : PreservesColimit (M ⋙ Q) (hom.{c, v, r, w} J R K) :=
    preservesColimit_of_iso_diagram _ eM
  let e : Q ⋙ hom.{c, v, r, w} J R K ≅ F ⋙ Q :=
    Functor.isoWhiskerLeft Q
      (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
        eL.op)) ≪≫ homFixed_derivedIso.{c, v, r, w} J R L
  have : PreservesColimit M (F ⋙ Q) := preservesColimit_of_natIso M e
  have hc : IsIso (colimit.post M (F ⋙ Q)) := inferInstance
  rw [← colimit.post_post] at hc
  exact (isIso_comp_left_iff _ _).mp hc

end CategoryTheory.RingedHomUniverses
