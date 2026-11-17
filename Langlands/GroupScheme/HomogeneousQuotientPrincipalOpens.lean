import Langlands.AlgebraicGeometry.GlobalVanishingIdeal
import Langlands.GroupScheme.Reductive.InvariantIdealLift
import Mathlib.Topology.Separation.Basic

/-! # Affine principal neighborhoods on a supplied homogeneous quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

open Langlands.AlgebraicGeometry InvariantPowerLift

namespace HomogeneousQuotient

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ J}
  (Q : HomogeneousQuotient i)

/-- Global sections whose principal opens in the supplied quotient are affine. -/
def affinePrincipalSections : Set Γ(Q.scheme.left, ⊤) :=
  {t | IsAffineOpen (Q.scheme.left.basicOpen t)}

/-- Inverse images of quotient point sets have rationally translation-stable
vanishing ideals in the ambient section ring. -/
theorem rightTranslation_mem_globalVanishingIdeal (Z : Set Q.scheme.left)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (s : ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hs : s ∈ globalVanishingIdeal J.X.left (Q.projection.left ⁻¹' Z)) :
    rightTranslation i h s ∈
      globalVanishingIdeal J.X.left (Q.projection.left ⁻¹' Z) := by
  let r : J.X ⟶ J.X :=
    𝟙 J.X * (CartesianMonoidalCategory.toUnit J.X ≫ h ≫ i.hom.hom)
  change r.left.appTop s ∈ _
  apply appTop_mem_globalVanishingIdeal r.left _ _ _ hs
  intro x hx
  have he := congrArg (fun f : J.X ⟶ Q.scheme => f.left x)
    (Q.right_mul_projection J.X (𝟙 _) (CartesianMonoidalCategory.toUnit J.X ≫ h))
  change Q.projection.left (r.left x) = Q.projection.left x at he
  change Q.projection.left (r.left x) ∈ Z
  rwa [he]

/-- Vanishing of a pulled-back section is detected by the supplied surjective projection. -/
theorem mem_globalVanishingIdeal_of_appTop_mem (Z : Set Q.scheme.left)
    {t : Γ(Q.scheme.left, ⊤)}
    (ht : Q.projection.left.appTop t ∈
      globalVanishingIdeal J.X.left (Q.projection.left ⁻¹' Z)) :
    t ∈ globalVanishingIdeal Q.scheme.left Z := by
  rw [mem_globalVanishingIdeal] at ht ⊢
  intro q hq hqt
  obtain ⟨x, hx⟩ := Q.surjective_projection.surj q
  apply ht x (by change Q.projection.left x ∈ Z; rwa [hx])
  rw [← Q.projection.left.preimage_basicOpen_top]
  change Q.projection.left x ∈ Q.scheme.left.basicOpen t
  rwa [hx]

variable [IsAlgClosed k] [Smooth H.X.hom] [IsAffine J.X.left]

/-- Geometric reductivity separates disjoint closed sets on the same supplied
quotient by a global section equal to zero on one and one on the other. -/
theorem exists_section_separating_closed_sets (hH : IsGeometricallyReductive H)
    {Z W : Set Q.scheme.left} (hZ : IsClosed Z) (hW : IsClosed W)
    (hd : Disjoint Z W) (hWne : W.Nonempty) :
    ∃ t : Γ(Q.scheme.left, ⊤),
      t ∈ globalVanishingIdeal Q.scheme.left Z ∧
        t - 1 ∈ globalVanishingIdeal Q.scheme.left W := by
  let I := globalVanishingIdeal J.X.left (Q.projection.left ⁻¹' Z)
  let K := globalVanishingIdeal J.X.left (Q.projection.left ⁻¹' W)
  have hKne : (Q.projection.left ⁻¹' W).Nonempty := by
    obtain ⟨q, hq⟩ := hWne
    obtain ⟨x, hx⟩ := Q.surjective_projection.surj q
    exact ⟨x, by change Q.projection.left x ∈ W; rwa [hx]⟩
  obtain ⟨s, hsI, hsinv, hsK⟩ := exists_invariant_separating_ideals i hH I K
    (Q.rightTranslation_mem_globalVanishingIdeal Z)
    (Q.rightTranslation_mem_globalVanishingIdeal W)
    (globalVanishingIdeal_ne_top hKne)
    (globalVanishingIdeal_sup_eq_top (hZ.preimage Q.projection.left.continuous)
      (hW.preimage Q.projection.left.continuous) (hd.preimage _))
  obtain ⟨t, ht⟩ := Q.exists_appTop_eq_of_isRightInvariant hsinv
  refine ⟨t, Q.mem_globalVanishingIdeal_of_appTop_mem Z ?_,
    Q.mem_globalVanishingIdeal_of_appTop_mem W ?_⟩
  · rwa [ht]
  · simpa only [map_sub, map_one, ht] using hsK

/-- A separating section vanishing away from a chosen open neighborhood gives
a principal neighborhood contained in that open. -/
theorem exists_basicOpen_between_closed_sets (hH : IsGeometricallyReductive H)
    {Z W : Set Q.scheme.left} (hZ : IsClosed Z) (hW : IsClosed W)
    (hd : Disjoint Z W) (hWne : W.Nonempty) :
    ∃ t : Γ(Q.scheme.left, ⊤),
      W ⊆ Q.scheme.left.basicOpen t ∧
        (Q.scheme.left.basicOpen t : Set Q.scheme.left) ⊆ Zᶜ := by
  obtain ⟨t, htZ, htW⟩ := Q.exists_section_separating_closed_sets hH hZ hW hd hWne
  refine ⟨t, ?_, ?_⟩
  · intro q hq
    by_contra hqt
    let Iq := globalVanishingIdeal Q.scheme.left ({q} : Set Q.scheme.left)
    have htq : t ∈ Iq := by
      apply (mem_globalVanishingIdeal _ _).2
      intro x hx
      have hxq : x = q := Set.mem_singleton_iff.mp hx
      subst x
      exact hqt
    have htq' : t - 1 ∈ Iq := by
      apply (mem_globalVanishingIdeal _ _).2
      intro x hx
      have hxq : x = q := Set.mem_singleton_iff.mp hx
      subst x
      exact (mem_globalVanishingIdeal _ _).1 htW q hq
    have h1 : (1 : Γ(Q.scheme.left, ⊤)) ∈ Iq := by
      simpa only [sub_sub_cancel] using Iq.sub_mem htq htq'
    exact ((mem_globalVanishingIdeal _ _).1 h1 q (Set.mem_singleton q)) (by simp)
  · intro q hq hqZ
    exact (mem_globalVanishingIdeal _ _).1 htZ q hqZ hq

/-- Every closed point has an affine principal neighborhood contained in any
prescribed open neighborhood. -/
theorem exists_affine_basicOpen_mem_subset_of_isClosed
    (hH : IsGeometricallyReductive H) (q : Q.scheme.left)
    (hq : IsClosed ({q} : Set Q.scheme.left))
    {U : Q.scheme.left.Opens} (hqU : q ∈ U) :
    ∃ t : Γ(Q.scheme.left, ⊤), q ∈ Q.scheme.left.basicOpen t ∧
      IsAffineOpen (Q.scheme.left.basicOpen t) ∧ Q.scheme.left.basicOpen t ≤ U := by
  obtain ⟨V, hV, hqV, hVU⟩ := exists_isAffineOpen_mem_and_subset hqU
  obtain ⟨t, htq, htV⟩ := Q.exists_basicOpen_between_closed_sets hH
    V.isOpen.isClosed_compl hq
    (by
      apply Set.disjoint_left.mpr
      intro x hx hxq
      have he : x = q := Set.mem_singleton_iff.mp hxq
      subst x
      exact hx hqV)
    (Set.singleton_nonempty q)
  have hsub : Q.scheme.left.basicOpen t ≤ V := by
    intro x hx
    exact not_not.mp (htV hx)
  refine ⟨t, htq (Set.mem_singleton q), ?_, hsub.trans hVU⟩
  have he : Q.scheme.left.basicOpen
      (Q.scheme.left.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op t) =
        Q.scheme.left.basicOpen t := by
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hsub]
  rw [← he]
  exact hV.basicOpen _

/-- Explicit geometric reductivity gives an affine principal neighborhood at
every point of the same supplied quotient. -/
theorem exists_affine_basicOpen_mem (hH : IsGeometricallyReductive H)
    (q : Q.scheme.left) :
    ∃ t : Γ(Q.scheme.left, ⊤), q ∈ Q.scheme.left.basicOpen t ∧
      IsAffineOpen (Q.scheme.left.basicOpen t) := by
  let : CompactSpace Q.scheme.left :=
    ⟨Q.surjective_projection.surj.range_eq ▸
      isCompact_range Q.projection.left.continuous⟩
  obtain ⟨x, hx, hxclosed⟩ :=
    (isClosed_closure : IsClosed (closure ({q} : Set Q.scheme.left))).exists_closed_singleton
      ⟨q, subset_closure (Set.mem_singleton q)⟩
  obtain ⟨t, hxt, ht, _⟩ := Q.exists_affine_basicOpen_mem_subset_of_isClosed hH x hxclosed
    (U := ⊤) (show x ∈ (⊤ : Q.scheme.left.Opens) from trivial)
  exact ⟨t, (specializes_iff_mem_closure.mpr hx).mem_open
    (Q.scheme.left.basicOpen t).isOpen hxt, ht⟩

end HomogeneousQuotient

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
