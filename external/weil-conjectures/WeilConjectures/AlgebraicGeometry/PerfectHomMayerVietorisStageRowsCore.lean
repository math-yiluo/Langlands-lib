/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone
import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow

/-! # The geometric diagram before taking the exact filtered colimit

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-stage-rows).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- Functorial geometric rows with distinguished-triangle presentations of every
consecutive short complex, before the categorical exactness argument.

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-stage-rows-core).

Proof: Pull U,V to Y and each stage. Restrict P,Q and the preceding shift;
localized pullback comparisons and thick closure preserve perfectness, and
perfect complexes have quasi-coherent cohomology. Apply the functorial
K-injective Mayer--Vietoris construction to Q. Apply Hom from P and derived
open adjunction. The rotated preceding shifted triangle, inverse rotation, and original triangle
respectively present the three consecutive short complexes as covariant Hom of distinguished
triangles. The triangle maps give zero composites. Direct-image naturality
followed by the unit gives transition and cocone maps; the adjunction triangle
identity identifies their central terms with perfectStageMap and perfectLimitMap.
The local terms retain their restricted perfect pairs and canonical stage Hom
systems. Underlying-set colimit preservation and finite-product preservation
identify the intersection comparisons with basic local comparisons and the
two-open comparisons with their products, transported by the adjunction
identifications. Empty opens give zero groups and satisfy the same argument.
No exactness of a filtered colimit is asserted. -/
theorem perfect_hom_mayerVietoris_stage_rows_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    : ∃ (S : ComposableArrows (Set.Ici i ⥤ AddCommGrpCat.{max u w}) 4)
        (B : ComposableArrows AddCommGrpCat.{max u w} 4)
        (κ : S ⟶ B ⋙ Functor.const (Set.Ici i))
        (e : ∀ j : Set.Ici i, (S.obj' 2).obj j ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q))
        (b : B.obj' 2 ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        ∃ (hS : S.IsComplex) (hB : B.IsComplex),
        (∀ (r : ℕ) (hr : r + 2 ≤ 4) (j : Set.Ici i),
          ∃ (Z : Scheme.{u}) (M : schemeDerivedCategory Z)
            (T : Triangle (schemeDerivedCategory Z))
            (hT : T ∈ distTriang (schemeDerivedCategory Z)),
            Nonempty (((S.sc hS r hr).map
              ((evaluation (Set.Ici i) AddCommGrpCat.{max u w}).obj j)) ≅
              (shortComplexOfDistTriangle T hT).map
                ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙
                  AddCommGrpCat.uliftFunctor.{u}))) ∧
        (∀ (r : ℕ) (hr : r + 2 ≤ 4),
          ∃ (Z : Scheme.{u}) (M : schemeDerivedCategory Z)
            (T : Triangle (schemeDerivedCategory Z))
            (hT : T ∈ distTriang (schemeDerivedCategory Z)),
            Nonempty ((B.sc hB r hr) ≅
              (shortComplexOfDistTriangle T hT).map
                ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙
                  AddCommGrpCat.uliftFunctor.{u}))) ∧
        (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : (S.obj' 2).obj j),
          e k ((S.obj' 2).map (homOfLE hjk) f) =
            perfectStageMap R s j.property hjk (e j f)) ∧
        (∀ (j : Set.Ici i) (f : (S.obj' 2).obj j),
          b ((κ.app ⟨2, by decide⟩).app j f) =
            perfectLimitMap R c s j.property (e j f)) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 0) ⟨B.obj' 0, κ.app ⟨0, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 1) ⟨B.obj' 1, κ.app ⟨1, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 3) ⟨B.obj' 3, κ.app ⟨3, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 4) ⟨B.obj' 4, κ.app ⟨4, by decide⟩⟩) := by
  obtain ⟨D, d, hD, hd, e, b, he, hb, hlocal⟩ :=
    perfect_hom_mayerVietoris_triangle_cocone R c i X s₀ U V hU hV Y t ht s hs P Q hP hQ
  let S : ComposableArrows (Set.Ici i ⥤ AddCommGrpCat.{max u w}) 4 :=
    (D ⋙ perfectHomTriangleRowFunctor Y P).flip
  let B := perfectHomTriangleRow Y P d.pt
  let κ := perfectHomTriangleRowCoconeMap Y P D d
  obtain ⟨hB, hpresB⟩ := perfectHomTriangleRow_presentations Y P d.pt hd
  have hS : S.IsComplex := by
    constructor
    intro r hr
    apply NatTrans.ext
    funext j
    obtain ⟨hj, _⟩ := perfectHomTriangleRow_presentations Y P (D.obj j) (hD j)
    exact hj.zero r hr
  refine ⟨S, B, κ, e, b, hS, hB, ?_, ?_, he, hb,
    hlocal ⟨0, by decide⟩ (by decide), hlocal ⟨1, by decide⟩ (by decide),
    hlocal ⟨3, by decide⟩ (by decide), hlocal ⟨4, by decide⟩ (by decide)⟩
  · intro r hr j
    obtain ⟨hj, hpres⟩ := perfectHomTriangleRow_presentations Y P (D.obj j) (hD j)
    obtain ⟨T, hT, eT⟩ := hpres r hr
    exact ⟨Y, P, T, hT, eT⟩
  · intro r hr
    obtain ⟨T, hT, eT⟩ := hpresB r hr
    exact ⟨Y, P, T, hT, eT⟩

end AlgebraicGeometry
