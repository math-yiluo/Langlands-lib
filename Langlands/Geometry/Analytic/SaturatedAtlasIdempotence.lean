import Langlands.Geometry.Analytic.SaturatedStrongCategory
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure

/-! # The local-domain saturation of a saturated atlas is the same atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X]

/-- Two atlases on one space are equal once their index types, algebras,
charts and bounded restrictions agree; the remaining fields are propositions. -/
theorem ext_of_heq {a b : IndexedAffinoidAtlas.{u, v, w} K X} (hI : a.Index = b.Index)
    (hA : HEq a.algebra b.algebra) (hC : HEq a.chart b.chart)
    (hR : HEq a.restriction b.restriction) : a = b := by
  obtain ⟨Ia, Aa, Ca, _, _, _, _, Ra, _, _, _, _⟩ := a
  obtain ⟨Ib, Ab, Cb, _, _, _, _, Rb, _, _, _, _⟩ := b
  dsimp only at hI hA hC hR
  subst hI
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq hC
  obtain rfl := eq_of_heq hR
  rfl

omit [CompleteSpace K] in
private theorem val_eq_of_heq {α : Type v} {F G : Set α} (h : F = G) {S : F} {T : G}
    (hST : HEq S T) : (S : α) = T := by
  subst h
  rw [eq_of_heq hST]

variable (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A member of the twice-saturated family, read as an index of the saturated atlas. -/
private def saturatedIndexOf (S : a.saturatedAtlas.saturatedAtlas.Index) :
    a.saturatedAtlas.Index :=
  ⟨S.val, a.localDomainFamily_saturatedAtlas ▸ S.property⟩

private theorem originalSaturatedIndex_saturatedIndexOf
    (S : a.saturatedAtlas.saturatedAtlas.Index) :
    a.saturatedAtlas.originalSaturatedIndex (saturatedIndexOf a S) = S :=
  Subtype.ext (a.range_saturatedChart (saturatedIndexOf a S))

/-- Every member of the twice-saturated family is an original chart of the
saturated atlas, so its chosen representative is that whole chart. -/
private theorem saturatedRepresentative_eq (S : a.saturatedAtlas.saturatedAtlas.Index) :
    a.saturatedAtlas.saturatedRepresentative S =
      a.saturatedAtlas.originalLocalDomain (saturatedIndexOf a S) := by
  have h := a.saturatedAtlas.saturatedRepresentative_original (saturatedIndexOf a S)
  rw [originalSaturatedIndex_saturatedIndexOf] at h
  exact h

private theorem saturatedIndexOf_eq_of_heq {S : a.saturatedAtlas.saturatedAtlas.Index}
    {S' : a.saturatedAtlas.Index} (h : HEq S S') : S' = saturatedIndexOf a S :=
  Subtype.ext (val_eq_of_heq a.localDomainFamily_saturatedAtlas h).symm

/-- Saturating an atlas that is already the local-domain saturation returns
literally the same atlas: the same index type, algebras, charts and bounded
restrictions. -/
theorem saturatedAtlas_saturatedAtlas :
    a.saturatedAtlas.saturatedAtlas = a.saturatedAtlas := by
  let b := a.saturatedAtlas
  have hI : b.saturatedAtlas.Index = b.Index :=
    congrArg (fun F : Set (Set X) => (F : Type v)) a.localDomainFamily_saturatedAtlas
  have hrange (S : b.saturatedAtlas.Index) :
      range (b.saturatedAtlas.chart S) = S.val := b.range_saturatedChart S
  have hrange' (S : b.saturatedAtlas.Index) :
      range (b.chart (saturatedIndexOf a S)) = S.val :=
    a.range_saturatedChart (saturatedIndexOf a S)
  refine ext_of_heq hI ?_ ?_ ?_
  · refine Function.hfunext hI fun S S' hS => ?_
    obtain rfl := saturatedIndexOf_eq_of_heq a hS
    apply heq_of_eq
    change (b.saturatedRepresentative S).algebra = _
    rw [saturatedRepresentative_eq a S]
    rfl
  · refine Function.hfunext hI fun S S' hS => ?_
    obtain rfl := saturatedIndexOf_eq_of_heq a hS
    have key : ∀ (U : LocalDomain b), U = b.originalLocalDomain (saturatedIndexOf a S) →
        HEq (⇑U.ambientMap) (b.chart (saturatedIndexOf a S)) := by
      intro U hU
      subst hU
      exact heq_of_eq (funext (b.originalLocalDomain_ambientMap (saturatedIndexOf a S)))
    exact key _ (saturatedRepresentative_eq a S)
  · refine Function.hfunext hI fun S S' hS => Function.hfunext hI fun T T' hT => ?_
    obtain rfl := saturatedIndexOf_eq_of_heq a hS
    obtain rfl := saturatedIndexOf_eq_of_heq a hT
    have hprop : (range (b.saturatedAtlas.chart S) ⊆ range (b.saturatedAtlas.chart T)) =
        (range (b.chart (saturatedIndexOf a S)) ⊆ range (b.chart (saturatedIndexOf a T))) := by
      rw [hrange S, hrange T, hrange' S, hrange' T]
    refine Function.hfunext hprop fun h h' _ => ?_
    have key : ∀ (U V : LocalDomain b), U = b.originalLocalDomain (saturatedIndexOf a S) →
        V = b.originalLocalDomain (saturatedIndexOf a T) → ∀ p : U ⟶ V,
          HEq p.restriction
            (b.restriction (saturatedIndexOf a S) (saturatedIndexOf a T) h') := by
      intro U V hU hV p
      subst hU
      subst hV
      exact heq_of_eq (b.originalLocalDomain_restriction _ _ h' p)
    exact key _ _ (saturatedRepresentative_eq a S) (saturatedRepresentative_eq a T)
      (b.saturatedInclusion S T h)

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

/-- The local-domain saturation of a presentation is a fixed point of
saturation. -/
theorem saturatedPresentation_saturatedPresentation
    (A : AffinoidAtlasPresentation.{u, v, w} K) :
    A.saturatedPresentation.saturatedPresentation = A.saturatedPresentation := by
  change (⟨A.space, A.atlas.saturatedAtlas.saturatedAtlas⟩ :
      AffinoidAtlasPresentation.{u, v, v} K) = ⟨A.space, A.atlas.saturatedAtlas⟩
  rw [IndexedAffinoidAtlas.saturatedAtlas_saturatedAtlas]

end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

/-- The constructed saturation of a constructed saturation is the same object
of the saturated category. -/
theorem ofSaturation_saturatedPresentation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    ofSaturation A.saturatedPresentation = ofSaturation A := by
  have h := A.saturatedPresentation_saturatedPresentation
  unfold ofSaturation
  congr 1

end SaturatedAtlasPresentation

end Langlands.Analytic
