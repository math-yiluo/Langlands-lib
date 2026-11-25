/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.HomColimitTruncation
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity

/-! # Sequential Hom continuity for a constructible integral sheaf -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

noncomputable local instance integralConstructibleHasZeroMorphisms
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

local instance integralConstructibleHasColimit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Shifted Hom from a constructible integral sheaf commutes with uniformly bounded-below
sequential colimits. The lifted indexing category is equivalent to the ordinary natural numbers.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Lemma 6.8.12 and the proof of Lemma 6.3.14.
(auxiliary; not a blueprint node)

Proof. Apply the good-truncation comparison theorem at the common cohomological
lower bound. Exact filtered colimits preserve the truncation quasi-isomorphisms,
so it suffices to use canonical cocones of termwise bounded-below diagrams.
Resolve a locally finitely presented integral module by two locally finite free
modules. Their Hom continuity and the rotated short exact single-sheaf triangle
prove continuity for the resolved module in every integer shift. Integral torsion
is retained in this resolution. For a locally closed piece, use the coefficient-
generic costalk-model theorem: it identifies the Hom diagram and cocone with a
strictly bounded-below model on the stratum, compatibly with every leg. Invertible
stage and vertex comparisons then identify the canonical colimit.desc maps.
Finally, finite stratification and noetherian open/closed induction express a
constructible sheaf as a finite distinguished extension of these pieces. Induct
on that tower using distinguished extension closure of homColimitProperty. The
good-truncation comparison returns the result for the supplied cocone c. Empty
schemes and zero ranks are covered by the same categorical argument. -/
theorem integralConstructible_sheaf_hom_colimit (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (D : AsSmall.{u + 1} ℕ ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ)
    (c : Cocone D) (hc : Nonempty (IsColimit c))
    (hD : ∃ a : ℤ, ∀ n, (DerivedCategory.Q.obj (D.obj n)).IsGE a) :
    homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c)
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨hc⟩ := hc
  apply homColimitProperty_of_strictly_bounded _ _ D c hc hD
  intro N hN
  obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X (integralCoeff ℓ E) M hM
  let D' := N ⋙ DerivedCategory.Q
  let c' := DerivedCategory.Q.mapCocone (colimit.cocone N)
  have hP : condensedLocallyClosedPiece (integralCoeff ℓ E) X ≤ homColimitProperty D' c' := by
    intro K hK
    obtain ⟨Z, U, i, j, hi, hj, hqc, P, hP, ⟨eK⟩⟩ := hK
    let : IsClosedImmersion i := hi
    let : IsOpenImmersion j := hj
    let : QuasiCompact j := hqc
    let : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    let : TopologicalSpace.NoetherianSpace U :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    apply (homColimitProperty D' c').prop_of_iso eK.symm
    intro n
    obtain ⟨L, hL, e, v, hleg⟩ :=
      condensed_local_piece_costalk_model X (integralCoeff ℓ E) i j P N hN n
    let F := shiftFunctor _ n ⋙ preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (integralCoeff ℓ E) i).obj
          ((openImmersionLowerShriek (integralCoeff ℓ E) j).obj P))))
    let G := condensedShiftedHom (integralCoeff ℓ E) U
      ((DerivedCategory.singleFunctor _ 0).obj P) n
    have hd : IsIso (colimit.desc _ (G.mapCocone (colimit.cocone L))) :=
      integral_lfp_hom_continuity U ℓ E P hP L hL n
    change IsIso (colimit.desc _ (F.mapCocone c'))
    have heq : colimit.desc _ (F.mapCocone c') ≫ v.hom =
        colimMap e.hom ≫ colimit.desc _ (G.mapCocone (colimit.cocone L)) := by
      apply colimit.hom_ext
      intro s
      dsimp only [G]
      simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
      exact hleg s
    have : IsIso (colimit.desc _ (F.mapCocone c') ≫ v.hom) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_right _ v.hom
  have h : ∀ r : ℕ, (condensedLocallyClosedPiece (integralCoeff ℓ E) X).extensionProductIter r ≤
      homColimitProperty D' c' := by
    intro r
    induction r with
    | zero => exact hP
    | succ r ih =>
      rw [ObjectProperty.extensionProductIter_succ]
      rintro K ⟨A, B, f, g, k, hdist, hA, hB⟩
      exact homColimitProperty_extensions D' c' _ hdist (hP _ hA) (ih _ hB)
  exact h r _ hr

end AlgebraicGeometry.ProEtale.CondensedRing
