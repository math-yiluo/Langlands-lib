import Langlands.Global.InfinitePlaceIwasawaStatement
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Actual completion base change for parabolic Iwasawa decomposition -/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.CompactIwasawa

variable {P : Type u} {P' : Type v} {G : Type w} {G' : Type z}
  [Group P] [Group P'] [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G']

/-- A maximal compact subgroup with the specified homomorphism's image as
the left factor of a covering product. -/
def HasDecomposition (f : P →* G) : Prop :=
  ∃ K : Subgroup G, IsCompact (K : Set G) ∧
    (∀ L : Subgroup G, IsCompact (L : Set G) → K ≤ L → L = K) ∧
    Set.range f * (K : Set G) = Set.univ

/-- A commuting pair of point-group comparisons transports all three
Iwasawa conclusions, including maximality among every compact subgroup. -/
theorem HasDecomposition.transport
    {f : P →* G} {f' : P' →* G'}
    (h : HasDecomposition f) (eP : P ≃* P') (eG : G ≃ₜ* G')
    (comm : ∀ x, f' (eP x) = eG (f x)) :
    HasDecomposition f' := by
  obtain ⟨K, hK, hmax, hcover⟩ := h
  refine ⟨K.map eG.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.image eG.continuous
  · intro L hL hle
    have hpre : IsCompact (L.comap eG.toMonoidHom : Set G) :=
      eG.toHomeomorph.isCompact_preimage.mpr hL
    have hEq := hmax (L.comap eG.toMonoidHom) hpre
      (Subgroup.map_le_iff_le_comap.mp hle)
    have hmap := congrArg (Subgroup.map eG.toMonoidHom) hEq
    simpa only [Subgroup.map_comap_eq_self_of_surjective
      (f := eG.toMonoidHom) eG.surjective] using hmap
  · apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy : eG.symm y ∈ Set.range f * (K : Set G) := by
      rw [hcover]
      trivial
    obtain ⟨a, ⟨x, rfl⟩, b, hb, hab⟩ := Set.mem_mul.mp hy
    refine Set.mem_mul.mpr
      ⟨f' (eP x), ⟨eP x, rfl⟩, eG b, ⟨b, hb, rfl⟩, ?_⟩
    rw [comm, ← map_mul, hab, eG.apply_symm_apply]

/-- Existence of the maximal compact and covering product is invariant
under commuting multiplicative homeomorphisms. -/
theorem hasDecomposition_iff
    (f : P →* G) (f' : P' →* G')
    (eP : P ≃* P') (eG : G ≃ₜ* G')
    (comm : ∀ x, f' (eP x) = eG (f x)) :
    HasDecomposition f ↔ HasDecomposition f' := by
  refine ⟨fun h => h.transport eP eG comm, fun h => ?_⟩
  apply h.transport eP.symm eG.symm
  intro x
  apply eG.injective
  rw [eG.apply_symm_apply, ← comm, eP.apply_symm_apply]

end Langlands.CompactIwasawa

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
  [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
  {P G : GroupScheme (Spec (CommRingCat.of C))}

/-- The inverse actual base-change point comparison commutes with every
group-scheme homomorphism. No affineness is needed for this identity. -/
theorem affinePointsBaseChangeMulEquiv_symm_target
    (p : P ⟶ G)
    (q : ((GroupScheme.baseChange (Spec.algebraMap C D)).obj P).affinePoints
      (CommAlgCat.of D A)) :
    (affinePointsBaseChangeMulEquiv C D A G).symm
        (((GroupScheme.baseChange (Spec.algebraMap C D)).obj P).affinePointsTarget
          ((GroupScheme.baseChange (Spec.algebraMap C D)).map p)
          (CommAlgCat.of D A) q) =
      P.affinePointsTarget p (CommAlgCat.of C A)
        ((affinePointsBaseChangeMulEquiv C D A P).symm q) := by
  apply Over.OverMorphism.ext
  simp only [affinePointsBaseChangeMulEquiv_symm_left, affinePointsTarget_apply]
  change (q.left ≫ ((Over.pullback (Spec.algebraMap C D)).map p.hom.hom).left) ≫
      CategoryTheory.Limits.pullback.fst G.X.hom (Spec.algebraMap C D) =
    (q.left ≫ CategoryTheory.Limits.pullback.fst P.X.hom (Spec.algebraMap C D)) ≫
      p.hom.hom.left
  simp [Category.assoc]

/-- The forward actual base-change point comparison commutes with every
group-scheme homomorphism. -/
theorem affinePointsBaseChangeMulEquiv_target
    (p : P ⟶ G) (x : P.affinePoints (CommAlgCat.of C A)) :
    affinePointsBaseChangeMulEquiv C D A G
        (P.affinePointsTarget p (CommAlgCat.of C A) x) =
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj P).affinePointsTarget
        ((GroupScheme.baseChange (Spec.algebraMap C D)).map p)
        (CommAlgCat.of D A) (affinePointsBaseChangeMulEquiv C D A P x) := by
  apply (affinePointsBaseChangeMulEquiv C D A G).symm.injective
  rw [MulEquiv.symm_apply_apply, affinePointsBaseChangeMulEquiv_symm_target,
    MulEquiv.symm_apply_apply]

end Langlands.GroupScheme

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual pullback group scheme to the infinite-place completion. -/
abbrev completionBaseChange (v : NumberField.InfinitePlace F) :
    GroupScheme (Spec (CommRingCat.of v.Completion)) :=
  (GroupScheme.baseChange (Spec.algebraMap F v.Completion)).obj G

local instance completionPointTopology
    (H : GroupScheme (Spec (CommRingCat.of F))) (v : NumberField.InfinitePlace F) :
    TopologicalSpace
      ((completionBaseChange F H v).affinePoints
        (CommAlgCat.of v.Completion v.Completion)) :=
  (completionBaseChange F H v).affinePointsTopologicalSpace
    (CommAlgCat.of v.Completion v.Completion)

variable [IsAffine G.X.left]

/-- Original completion-valued points and completion-rational points of
the actual pullback group, with their unchanged evaluation topologies. -/
def completionBaseChangeHomeomorph (v : NumberField.InfinitePlace F) :
    InfinitePlaceGroupPoints F G v ≃ₜ*
      (completionBaseChange F G v).affinePoints
        (CommAlgCat.of v.Completion v.Completion) :=
  affinePointsBaseChangeContinuousMulEquiv F v.Completion v.Completion G

/-- Compact Iwasawa existence for a homomorphism is equivalent before and
after actual completion base change. The product order is unchanged. -/
theorem hasDecomposition_completionBaseChange_iff
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (v : NumberField.InfinitePlace F) :
    CompactIwasawa.HasDecomposition
        (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) ↔
      CompactIwasawa.HasDecomposition
        ((completionBaseChange F P v).affinePointsTarget
          ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p)
          (CommAlgCat.of v.Completion v.Completion)) := by
  apply CompactIwasawa.hasDecomposition_iff _ _
    (affinePointsBaseChangeMulEquiv F v.Completion v.Completion P)
    (completionBaseChangeHomeomorph F G v)
  intro x
  exact (affinePointsBaseChangeMulEquiv_target F v.Completion v.Completion p x).symm

omit [IsAffine G.X.left] in
/-- The existing connected-reductive predicate holds on the actual
completion pullback, without a new algebraic hypothesis. -/
theorem isConnectedReductive_completionBaseChange
    (hG : IsConnectedReductive G) (v : NumberField.InfinitePlace F) :
    IsConnectedReductive (completionBaseChange F G v) :=
  connectedReductiveFieldExtensionStatement F v.Completion G hG

omit [IsAffine G.X.left] in
/-- Every actual rational parabolic remains parabolic on completion base
change, including the improper parabolic. -/
theorem isParabolicSubgroup_completionBaseChange
    (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) (v : NumberField.InfinitePlace F) :
    IsParabolicSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p) :=
  parabolicFieldExtensionStatement F v.Completion G hG P p hp

end Langlands.Global.InfinitePlaceGroupPoints
