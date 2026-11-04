import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportStatement
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof

/-! # Transport of the actual standard-Levi cuspidality tests -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- An equivalence of finite label types identifies all their proper subsets. -/
def properFinsetEquiv {α : Type u} {β : Type w} [Fintype α] [Fintype β]
    (e : α ≃ β) :
    {K : Finset α // K ≠ Finset.univ} ≃ {K : Finset β // K ≠ Finset.univ} where
  toFun K := ⟨K.val.map e.toEmbedding, by
    intro h
    apply K.property
    apply Finset.map_injective e.toEmbedding
    simpa only [Finset.map_univ_equiv] using h⟩
  invFun K := ⟨K.val.map e.symm.toEmbedding, by
    intro h
    apply K.property
    apply Finset.map_injective e.symm.toEmbedding
    simpa only [Finset.map_univ_equiv] using h⟩
  left_inv K := by
    apply Subtype.ext
    ext a
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, e.symm_apply_apply]
  right_inv K := by
    apply Subtype.ext
    ext a
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, e.apply_symm_apply]

section Roots

variable {k : Type u} [Field k]
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (iL : T.toGrp ⟶ L) (ν : cocharacterLattice T)
  (I : Finset (SimpleRoot i ν)) (hsimple : simpleRelativeRoots iL ν = rootSet i ν I)

/-- The intrinsic roots of an actual Levi keep their literal ambient character. -/
def leviSimpleRootEquivOfEq : SimpleRoot iL ν ≃ I where
  toFun α :=
    let a : SimpleRoot i ν := ⟨α.val, rootSet_subset i ν I (hsimple ▸ α.property)⟩
    ⟨a, (val_mem_rootSet i ν I a).mp (hsimple ▸ α.property)⟩
  invFun α := ⟨α.val.val, hsimple.symm ▸
    (val_mem_rootSet i ν I α.val).mpr α.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mapping an intrinsic root subset into the parent Levi index preserves its
exact character subset. -/
theorem rootSet_leviIndex_map_leviSimpleRootEquivOfEq
    (K : Finset (SimpleRoot iL ν)) :
    rootSet i ν (leviIndex I (K.map (leviSimpleRootEquivOfEq i iL ν I hsimple).toEmbedding)) =
      rootSet iL ν K := by
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp ha with ⟨b, hb, rfl⟩
    rcases Finset.mem_map.mp hb with ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(leviSimpleRootEquivOfEq i iL ν I hsimple a).val, ?_, rfl⟩
    exact Finset.mem_map.mpr ⟨_, Finset.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩

end Roots

/-- The actual standard families, the exact root labels, and the canonical
point homeomorphism transport every proper normalized Jacquet test. -/
theorem rationalLeviCuspidalityTransport :
    RationalLeviCuspidalityTransportStatement.{u, v} := by
  intro hDynamic hStandard k _ _ G hG T i hi
  have := hG.isAffineHom
  intro ν hν I L hL
  have := hL.isAffineHom
  intro iL
  let : TopologicalSpace (rationalPoints G) := pointTopology
  let : TopologicalSpace (rationalPoints L) := pointTopology
  intro _ _ _ _ _ hU hUL hMI hInner hOwn
  let := hMI.locallyCompactSpace
  intro σ
  obtain ⟨hsimple, -, hfamilies⟩ := standardLeviStandardFamilies hDynamic hStandard
    k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I) L hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  let eRoot : SimpleRoot iL ν ≃ I := leviSimpleRootEquivOfEq i iL ν I hsimple
  let eIndex := properFinsetEquiv eRoot
  let e := leviRationalPointHomeomorph i ν I
  have hmatch (K : {K : Finset (SimpleRoot iL ν) // K ≠ Finset.univ}) :
      standardLevi iL ν (rootSet iL ν K.val) =
          (standardLevi i ν (rootSet i ν (leviIndex I (eIndex K).val))).comap
            (Standard.leviHom i ν (rootSet i ν I)) ∧
        standardUnipotent iL ν (rootSet iL ν K.val) =
          (standardUnipotent i ν (rootSet i ν (leviIndex I (eIndex K).val))).comap
            (Standard.leviHom i ν (rootSet i ν I)) := by
    have hK : rootSet iL ν K.val ⊆ rootSet i ν I := by
      exact (rootSet_subset iL ν K.val).trans hsimple.subset
    have hm := hfamilies (rootSet iL ν K.val) hK
    have hset : rootSet i ν (leviIndex I (eIndex K).val) = rootSet iL ν K.val :=
      rootSet_leviIndex_map_leviSimpleRootEquivOfEq i iL ν I hsimple K.val
    rw [hset]
    exact ⟨hm.2.1, hm.2.2⟩
  have hMM : ∀ K (x : rationalPoints L),
      x ∈ levi iL ν K.val ↔
        e x ∈ (levi i ν (leviIndex I (eIndex K).val)).subgroupOf (levi i ν I) := by
    intro K x
    change x ∈ (standardLevi iL ν (rootSet iL ν K.val)).carrier (Over.mk (𝟙 _)) ↔
      (e x : rationalPoints G) ∈
        (standardLevi i ν (rootSet i ν (leviIndex I (eIndex K).val))).carrier (Over.mk (𝟙 _))
    rw [leviRationalPointHomeomorph_apply_coe]
    rw [(hmatch K).1]
    rfl
  have hUU : ∀ K (x : rationalPoints L),
      x ∈ unipotent iL ν K.val ↔
        e x ∈ (unipotent i ν (leviIndex I (eIndex K).val)).subgroupOf (levi i ν I) := by
    intro K x
    change x ∈ (standardUnipotent iL ν (rootSet iL ν K.val)).carrier (Over.mk (𝟙 _)) ↔
      (e x : rationalPoints G) ∈
        (standardUnipotent i ν (rootSet i ν (leviIndex I (eIndex K).val))).carrier (Over.mk (𝟙 _))
    rw [leviRationalPointHomeomorph_apply_coe]
    rw [(hmatch K).2]
    rfl
  exact isCuspidalFor_pullback_iff
    (κ := {K : Finset I // K ≠ Finset.univ})
    (κ' := {K : Finset (SimpleRoot iL ν) // K ≠ Finset.univ})
    (P := fun K => (parabolic i ν (leviIndex I K.val)).subgroupOf (levi i ν I))
    (M := fun K => (levi i ν (leviIndex I K.val)).subgroupOf (levi i ν I))
    (U := fun K => (unipotent i ν (leviIndex I K.val)).subgroupOf (levi i ν I))
    (P' := fun K => parabolic iL ν K.val)
    (M' := fun K => levi iL ν K.val)
    (U' := fun K => unipotent iL ν K.val)
    (h := fun K => hInner K.val) (h' := fun K => hOwn K.val)
    (hU := fun K => (hU (leviIndex I K.val)).preimage continuous_subtype_val)
    (hU' := fun K => hUL K.val) e eIndex eIndex.surjective hMM hUU σ

end Langlands.Aubert.General.RationalPointFamily
