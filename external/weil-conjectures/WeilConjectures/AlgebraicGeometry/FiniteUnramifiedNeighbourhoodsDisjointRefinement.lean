/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Disjoint refinement of finite unramified neighbourhoods

Source: Stacks Project, Tags 04DG, 04HI and 01W6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Further restriction preserves a closed immersion: paste the two standard restriction
pullback squares and use stability of closed immersions under base change. -/
private theorem closedImmersion_restrict_of_le
    {Y T : Scheme.{u}} (π : Y ⟶ T) (A B : T.Opens) (hBA : B ≤ A)
    (hA : IsClosedImmersion (π ∣_ A)) : IsClosedImmersion (π ∣_ B) := by
  let r := Y.homOfLE (π.preimage_mono hBA)
  let t := T.homOfLE hBA
  have H : IsPullback r (π ∣_ B) (π ∣_ A) t := by
    apply IsPullback.of_right _ (morphismRestrict_homOfLE π B A hBA).symm
      (isPullback_morphismRestrict π A).flip
    simpa [r, t] using (isPullback_morphismRestrict π B).flip
  exact MorphismProperty.of_isPullback H hA

/-- Source: Stacks Project, Tag 04DG followed by the shrinking argument of Tag 04HI.
(blueprint: lem-weil-pbc-finite-unramified-neighbourhoods-disjoint-refinement)

Proof: apply `finite_unramified_one_point_closed` to each piece, using its unique fibre
point and purely inseparable residue extension. Intersect the finitely many neighbourhoods
of `u`. Replace all pieces by their base changes to this intersection. Their inclusions
into the pullback are proper by `IsProper.of_comp`, since the projection is separated
and each piece is a closed immersion over the base, hence proper. Thus these open pieces
are also closed. Each pairwise intersection is closed in one piece; its image in the
base is closed since that piece is finite. These images avoid `u`: uniqueness of each
piece's fibre would otherwise equate two distinct marked points. Delete the finite union
of these images and base change again. The pieces are now disjoint and still closed
immersions. Open base change identifies them with opens of the new pullback and preserves
their marked points and their exhaustion of all lifts of the listed points. For an empty
family use the whole base open; exhaustion already asserts that there are no such lifts.
No étaleness or local finite type is needed for the ambient morphism. -/
theorem exists_disjoint_closed_immersion_refinement
    {X S U : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (g : U ⟶ S) (u : U)
    (n : ℕ) (x : Fin n → X) (m : Fin n → ℕ)
    (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens)
    (v : (a : Σ i : Fin n, Fin (m i)) → (V a).toScheme)
    (hpieces : ∀ a, IsFinite ((V a).ι ≫ pullback.snd f g) ∧
      (LocallyOfFiniteType ((V a).ι ≫ pullback.snd f g) ∧
        IsOpenImmersion (pullback.diagonal ((V a).ι ≫ pullback.snd f g))) ∧
      ((V a).ι ≫ pullback.snd f g) (v a) = u ∧
      (∀ w : (V a).toScheme, ((V a).ι ≫ pullback.snd f g) w = u → w = v a) ∧
      (letI : Algebra (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
          ((V a).toScheme.residueField (v a)) :=
        (((V a).ι ≫ pullback.snd f g).residueFieldMap (v a)).hom.toAlgebra
       IsPurelyInseparable (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
         ((V a).toScheme.residueField (v a))))
    (hinjective : Function.Injective (fun a ↦ (V a).ι (v a)))
    (hexhaust : ∀ (i : Fin n) (p : ↥(pullback f g)),
      (pullback.snd f g).base p = u → (pullback.fst f g).base p = x i →
        ∃ a, p = (V a).ι (v a)) :
    ∃ (B : U.Opens) (huB : u ∈ B),
      ∃ V' : (Σ i : Fin n, Fin (m i)) → (pullback f (B.ι ≫ g)).Opens,
        (∀ a, IsClosed (V' a : Set ↥(pullback f (B.ι ≫ g)))) ∧
        Pairwise (fun a b ↦ Disjoint (V' a) (V' b)) ∧
        (∀ a, IsClosedImmersion ((V' a).ι ≫ pullback.snd f (B.ι ≫ g)) ∧
          (⟨u, huB⟩ : B.toScheme) ∈
            Set.range (((V' a).ι ≫ pullback.snd f (B.ι ≫ g)).base)) ∧
        (∀ (i : Fin n) (p : ↥(pullback f (B.ι ≫ g))),
          (pullback.snd f (B.ι ≫ g)).base p = (⟨u, huB⟩ : B.toScheme) →
          (pullback.fst f (B.ι ≫ g)).base p = x i → ∃ a, p ∈ V' a) := by
  classical
  let I := Σ i : Fin n, Fin (m i)
  let q := pullback.snd f g
  let π := fun a : I ↦ (V a).ι ≫ q
  have hfinite (a : I) : IsFinite (π a) := (hpieces a).1
  have hVclosed (a : I) : IsClosed (V a : Set ↥(pullback f g)) := by
    have : IsFinite (π a) := hfinite a
    have : IsProper ((V a).ι) := IsProper.of_comp (V a).ι q
    simpa only [Scheme.Opens.range_ι] using (V a).ι.isClosedMap.isClosed_range
  have hlocal (a : I) : ∃ A : U.Opens, u ∈ A ∧ IsClosedImmersion (π a ∣_ A) :=
    finite_unramified_one_point_closed (π a) u (v a) (hpieces a).2.2.1
      (hpieces a).2.2.2.1 (hfinite a) (hpieces a).2.1 (hpieces a).2.2.2.2
  choose A huA hA using hlocal
  let Z : I → I → Set U := fun a b ↦ q '' ((V a : Set _) ∩ (V b : Set _))
  have hZclosed (a b : I) : IsClosed (Z a b) := by
    have : IsFinite (π a) := hfinite a
    have hclosed : IsClosed ((V a).ι ⁻¹' (V b : Set _)) :=
      (hVclosed b).preimage (V a).ι.continuous
    have heq : Z a b = π a '' ((V a).ι ⁻¹' (V b : Set _)) := by
      change q '' ((V a : Set _) ∩ (V b : Set _)) =
        (q ∘ (V a).ι) '' ((V a).ι ⁻¹' (V b : Set _))
      rw [Set.image_comp, Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι]
    rw [heq]
    exact (π a).isClosedMap _ hclosed
  have huZ (a b : I) (hab : a ≠ b) : u ∉ Z a b := by
    rintro ⟨p, ⟨hpa, hpb⟩, hpu⟩
    let wa : (V a).toScheme := ⟨p, hpa⟩
    let wb : (V b).toScheme := ⟨p, hpb⟩
    have hea : wa = v a := (hpieces a).2.2.2.1 wa hpu
    have heb : wb = v b := (hpieces b).2.2.2.1 wb hpu
    apply hab
    apply hinjective
    exact (congrArg (fun w ↦ (V a).ι w) hea).symm.trans
      (congrArg (fun w ↦ (V b).ι w) heb)
  let D : I → I → U.Opens := fun a b ↦
    if a = b then ⊤ else ⟨(Z a b)ᶜ, (hZclosed a b).isOpen_compl⟩
  let B : U.Opens := (⨅ a, A a) ⊓ ⨅ a, ⨅ b, D a b
  have huB : u ∈ B := by
    refine ⟨?_, ?_⟩
    · simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      intro a
      exact huA a
    · simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      intro a b
      by_cases hab : a = b
      · simp [D, hab]
      · simp only [D, ite_eq_right hab]
        exact huZ a b hab
  have hBA (a : I) : B ≤ A a := inf_le_left.trans (iInf_le A a)
  have hBD (a b : I) : B ≤ D a b :=
    inf_le_right.trans ((iInf_le _ a).trans (iInf_le _ b))
  let g' := B.ι ≫ g
  let q' := pullback.snd f g'
  let k : pullback f g' ⟶ pullback f g :=
    pullback.map f g' f g (𝟙 X) B.ι (𝟙 S) (by simp) (by simp [g'])
  have hkfst : k ≫ pullback.fst f g = pullback.fst f g' := by simp [k]
  have hkq : k ≫ q = q' ≫ B.ι := by simp [k, q, q']
  have H : IsPullback k q' q B.ι := by
    apply IsPullback.of_right _ hkq (IsPullback.of_hasPullback f g)
    simpa only [hkfst] using (IsPullback.of_hasPullback f g')
  let V' : I → (pullback f g').Opens := fun a ↦ k ⁻¹ᵁ V a
  have hclosed (a : I) : IsClosed (V' a : Set ↥(pullback f g')) :=
    (hVclosed a).preimage k.continuous
  have hdisj : Pairwise (fun a b ↦ Disjoint (V' a) (V' b)) := by
    intro a b hab
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro p hp
    have hpZ : q (k p) ∈ Z a b := ⟨k p, hp, rfl⟩
    have hpoint : q (k p) = B.ι (q' p) :=
      congrArg (fun t ↦ t.base p) hkq
    have hpD : B.ι (q' p) ∈ D a b := hBD a b (q' p).property
    rw [hpoint] at hpZ
    exact (show B.ι (q' p) ∉ Z a b from by simpa [D, hab] using hpD) hpZ
  have hbase (a : I) : IsClosedImmersion ((V' a).ι ≫ q') := by
    have hπB : IsClosedImmersion (π a ∣_ B) :=
      closedImmersion_restrict_of_le (π a) (A a) B (hBA a) (hA a)
    let r := k.resLE (V a) (V' a) le_rfl
    have Hr : IsPullback r (V' a).ι (V a).ι k := by
      apply IsOpenImmersion.isPullback
      · simp [r]
      · simp [V']
    have Hπ : IsPullback r ((V' a).ι ≫ q') (π a) B.ι := Hr.paste_vert H
    -- Compare this pullback with the standard restriction of the piece to B.
    let e := Hπ.isoPullback ≪≫ pullbackRestrictIsoRestrict (π a) B
    have he : e.hom ≫ (π a ∣_ B) = (V' a).ι ≫ q' := by simp [e]
    have : IsClosedImmersion (e.hom ≫ (π a ∣_ B)) := by
      let := hπB
      infer_instance
    rwa [he] at this
  refine ⟨B, huB, V', hclosed, hdisj, ?_, ?_⟩
  · intro a
    refine ⟨hbase a, ?_⟩
    obtain ⟨p, hpk, hpq⟩ := Scheme.exists_preimage_of_isPullback H
      ((V a).ι (v a)) (⟨u, huB⟩ : B.toScheme) (hpieces a).2.2.1
    have hpV : p ∈ V' a := by
      change k p ∈ V a
      rw [hpk]
      exact (v a).property
    refine ⟨⟨p, hpV⟩, ?_⟩
    exact hpq
  · intro i p hpu hpx
    have hkpu : q (k p) = u := by
      rw [show q (k p) = B.ι (q' p) from congrArg (fun t ↦ t.base p) hkq, hpu]
      rfl
    have hkpx : (pullback.fst f g) (k p) = x i := by
      rw [← Scheme.Hom.comp_apply, hkfst]
      exact hpx
    obtain ⟨a, ha⟩ := hexhaust i (k p) hkpu hkpx
    refine ⟨a, ?_⟩
    change k p ∈ V a
    rw [ha]
    exact (v a).property

end AlgebraicGeometry
