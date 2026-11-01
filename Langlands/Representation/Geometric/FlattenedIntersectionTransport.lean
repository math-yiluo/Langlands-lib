import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! Actual intersection conjugation in flattened product-Levi coordinates. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport CategoryTheory

universe uF uV

variable (F : Type uF) [Field F] {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F B C w = refinedLevi F B S)
  (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R)

/-- The actual intersection conjugation, with both product Levis flattened. -/
def flattenedIntersectionConjugation :
    (B.flatten S).Levi F ≃* (C.flatten R).Levi F :=
  (flattenedLeviEquiv F B S).trans
    ((MulEquiv.subgroupCongr hS.symm).trans
      ((intersectionLeviConjugation F B C w).trans
        ((MulEquiv.subgroupCongr hR).trans (flattenedLeviEquiv F C R).symm)))

/-- Flattening both sides retains precisely the prescribed ambient conjugation. -/
theorem flattenedIntersectionConjugation_embedding (m : (B.flatten S).Levi F) :
    (C.flatten R).leviEmbedding F
        (flattenedIntersectionConjugation F B C w S R hS hR m) =
      permutation n F w * (B.flatten S).leviEmbedding F m *
        (permutation n F w)⁻¹ := by
  change (C.flatten R).leviEmbedding F
      ((flattenedLeviEquiv F C R).symm
        ((MulEquiv.subgroupCongr hR)
          (intersectionLeviConjugation F B C w
            ((MulEquiv.subgroupCongr hS.symm) (flattenedLeviEquiv F B S m))))) = _
  rw [flattenedLeviEquiv_symm_embedding]
  change C.leviEmbedding F
      (intersectionLeviConjugation F B C w
        ((MulEquiv.subgroupCongr hS.symm) (flattenedLeviEquiv F B S m))).val = _
  rw [intersectionLeviConjugation_embedding]
  change permutation n F w *
      B.leviEmbedding F (flattenedLeviEquiv F B S m).val *
        (permutation n F w)⁻¹ = _
  rw [flattenedLeviEquiv_embedding]

include hS hR in
/-- The two flattened intersection Levis are conjugate by the actual
representative; no minimality or whole-target hypothesis is needed. -/
theorem conjugatesLevi_flattened_intersections :
    ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w := by
  apply le_antisymm
  · rintro g ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨flattenedIntersectionConjugation F B C w S R hS hR m,
      flattenedIntersectionConjugation_embedding F B C w S R hS hR m⟩
  · rintro g ⟨m, rfl⟩
    obtain ⟨d, rfl⟩ :=
      (flattenedIntersectionConjugation F B C w S R hS hR).surjective m
    exact ⟨(B.flatten S).leviEmbedding F d, ⟨d, rfl⟩,
      (flattenedIntersectionConjugation_embedding F B C w S R hS hR d).symm⟩

/-- In flattened coordinates the constructed intersection map is the existing
whole-Levi conjugation map, for any proof of the concrete conjugacy. -/
theorem flattenedIntersectionConjugation_eq_leviConjugation
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w) :
    flattenedIntersectionConjugation F B C w S R hS hR =
      leviConjugation (B.flatten S) (C.flatten R) w hw := by
  apply MulEquiv.ext
  intro m
  apply (C.flatten R).leviEmbedding_injective F
  rw [flattenedIntersectionConjugation_embedding, leviConjugation_embedding]

section Smooth

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Equality relabeling and actual inverse intersection conjugation, between
the two supplied refined subgroups. -/
def refinedIntersectionTransportFunctor :
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F C R) :=
  subgroupEqualityFunctor _ _ hS.symm ⋙ intersectionTransportFunctor F B C w ⋙
    subgroupEqualityFunctor _ _ hR

/-- The actual middle transport, flattened on the target, is whole-Levi
inverse conjugation of the flattened source representation. -/
def flattenedIntersectionTransportEquiv
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S)) :
    (SmoothRep.pullback (flattenedLeviEquivContinuous F C R)
      ((refinedIntersectionTransportFunctor F B C w S R hS hR).obj A)).representation.Equiv
        (transport (B.flatten S) (C.flatten R) w hw
          (A.representation.comp (flattenedLeviEquiv F B S).toMonoidHom)) := by
  have key : ∀ m : (C.flatten R).Levi F,
      (MulEquiv.subgroupCongr hS.symm).symm
          ((intersectionLeviConjugation F B C w).symm
            ((MulEquiv.subgroupCongr hR).symm (flattenedLeviEquiv F C R m))) =
        flattenedLeviEquiv F B S
          ((leviConjugation (B.flatten S) (C.flatten R) w hw).symm m) := by
    intro m
    apply Subtype.ext
    apply B.leviEmbedding_injective F
    rw [flattenedLeviEquiv_embedding]
    change B.leviEmbedding F
        ((intersectionLeviConjugation F B C w).symm
          ((MulEquiv.subgroupCongr hR).symm (flattenedLeviEquiv F C R m))).val = _
    rw [intersectionLeviConjugation_symm_embedding, leviConjugation_symm_embedding]
    change (permutation n F w)⁻¹ *
        C.leviEmbedding F (flattenedLeviEquiv F C R m).val * permutation n F w = _
    rw [flattenedLeviEquiv_embedding]
  have relabel {G : Type uF} [Group G] [TopologicalSpace G]
      (H K : Subgroup G) (h : H = K) (X : SmoothRep.{0, uF, uV} ℂ H) :
      ((subgroupEqualityFunctor H K h).obj X).representation.Equiv
        (X.representation.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom) := by
    subst K
    exact Representation.Equiv.refl _
  let A' := (subgroupEqualityFunctor _ _ hS.symm).obj A
  let Q := (intersectionTransportFunctor F B C w).obj A'
  have e1 := relabel _ _ hS.symm A
  have e2 := relabel _ _ hR Q
  have e3 := equivComp e1
    (((intersectionLeviConjugation F B C w).symm.toMonoidHom).comp
      (MulEquiv.subgroupCongr hR).symm.toMonoidHom)
  have e4 := equivComp (e2.trans e3) (flattenedLeviEquiv F C R).toMonoidHom
  refine e4.trans ?_
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_
  intro m
  ext v
  change A.representation
      ((MulEquiv.subgroupCongr hS.symm).symm
        ((intersectionLeviConjugation F B C w).symm
          ((MulEquiv.subgroupCongr hR).symm (flattenedLeviEquiv F C R m)))) v =
    A.representation (flattenedLeviEquiv F B S
      ((leviConjugation (B.flatten S) (C.flatten R) w hw).symm m)) v
  rw [key]

end Smooth
end Langlands.Geometric
