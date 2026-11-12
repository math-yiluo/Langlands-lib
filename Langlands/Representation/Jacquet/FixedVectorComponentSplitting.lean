import Langlands.Representation.Jacquet.FixedVectorDualityReduction
import Langlands.Representation.Category.CoproductCompression
import Langlands.CategoryTheory.RenardCategoryDecomposition

/-! # Fixed-vector splitting from actual component coproducts -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe uG uV uI

namespace Langlands.Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (K : OpenSubgroup G) {I : Type uI}

/-- The endomorphism of a supplied actual coproduct that is the identity on
fixed-vector-generated components and zero on every other component. -/
def fixedVectorComponentProjector
    (A : I → SmoothRep.{0,uG,uV} ℂ G) (s : Cofan A) (hs : IsColimit s) :
    s.pt ⟶ s.pt := by
  classical
  exact hs.desc (Cofan.mk s.pt
    (fun i => if fixedVectorGenerated K.toSubgroup (A i) then s.inj i else 0))

/-- An actual component coproduct splits into a fixed-vector-generated part
and a part without fixed vectors if every component has one of those properties.
The index and carrier universes are independent. -/
theorem fixedVectorSplitting_of_cofan
    (A : I → SmoothRep.{0,uG,uV} ℂ G) (s : Cofan A) (hs : IsColimit s)
    (hA : ∀ i, fixedVectorGenerated K.toSubgroup (A i) ∨
      fixedVectors (A i).representation K.toSubgroup = ⊥) :
    ∃ S T : Subrepresentation s.pt.representation,
      fixedVectorGenerated K.toSubgroup (SmoothRep.subrepresentation s.pt S) ∧
      fixedVectors (SmoothRep.subrepresentation s.pt T).representation K.toSubgroup = ⊥ ∧
      S ⊔ T = ⊤ := by
  classical
  let Q : I → Prop := fun i => fixedVectorGenerated K.toSubgroup (A i)
  let c : Cofan A := Cofan.mk s.pt (fun i => if Q i then s.inj i else 0)
  let p : s.pt ⟶ s.pt := fixedVectorComponentProjector K A s hs
  have hp (i : I) : s.inj i ≫ p = if Q i then s.inj i else 0 := by
    exact hs.fac c ⟨i⟩
  have hp_apply (i : I) (v : A i) :
      SmoothRep.hom p (SmoothRep.hom (s.inj i) v) =
        if Q i then SmoothRep.hom (s.inj i) v else 0 := by
    have h := congrArg (fun f => SmoothRep.hom f v) (hp i)
    by_cases hi : Q i
    · simpa [hi] using h
    · rw [ite_eq_right hi] at h
      change SmoothRep.hom p (SmoothRep.hom (s.inj i) v) = 0 at h
      simpa only [ite_eq_right hi] using h
  have hpp : p ≫ p = p := by
    apply hs.hom_ext
    rintro ⟨i⟩
    change s.inj i ≫ (p ≫ p) = s.inj i ≫ p
    rw [← Category.assoc, hp]
    by_cases hi : Q i <;> simp [hi, hp]
  have hpp_apply (v : s.pt) :
      SmoothRep.hom p (SmoothRep.hom p v) = SmoothRep.hom p v :=
    congrArg (fun f => SmoothRep.hom f v) hpp
  let S := (SmoothRep.hom p).range
  let T := (SmoothRep.hom p).ker
  let q : s.pt ⟶ SmoothRep.subrepresentation s.pt S := SmoothRep.ofHom {
    toLinearMap := (SmoothRep.hom p).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      exact Subtype.ext ((SmoothRep.hom p).isIntertwining _ _ g v) }
  have hS : fixedVectorGenerated K.toSubgroup (SmoothRep.subrepresentation s.pt S) := by
    intro R hR
    have hwhole (v : s.pt) : SmoothRep.hom q v ∈ R := by
      obtain ⟨x, rfl⟩ := SmoothRep.cofanDirectSumMap_surjective A s hs v
      induction x using DirectSum.induction_on with
      | zero =>
        change SmoothRep.hom q (SmoothRep.cofanDirectSumMap A s 0) ∈ R.toSubmodule
        simpa only [map_zero] using R.toSubmodule.zero_mem
      | add x y hx hy =>
        change SmoothRep.hom q (SmoothRep.cofanDirectSumMap A s (x + y)) ∈ R.toSubmodule
        simpa only [map_add] using R.toSubmodule.add_mem hx hy
      | of i v =>
        change SmoothRep.hom q (SmoothRep.cofanDirectSumMap A s
          (DirectSum.lof ℂ I (fun i => A i) i v)) ∈ R
        rw [SmoothRep.cofanDirectSumMap_lof]
        by_cases hi : Q i
        · exact fixedVectorGenerated_image_le K.toSubgroup hi
            ((SmoothRep.hom q).comp (SmoothRep.hom (s.inj i))) R
            (fun w hw => hR (map_mem_fixedVectors _ hw)) v
        · have hz : SmoothRep.hom q (SmoothRep.hom (s.inj i) v) = 0 := by
            apply Subtype.ext
            exact (hp_apply i v).trans (ite_eq_right hi)
          rw [hz]
          exact R.toSubmodule.zero_mem
    apply top_unique
    intro v _
    obtain ⟨w, hw⟩ := v.property
    have hv : SmoothRep.hom q w = v := Subtype.ext hw
    rw [← hv]
    exact hwhole w
  have hfixed (v : s.pt) (hv : v ∈ fixedVectors s.pt.representation K.toSubgroup) :
      SmoothRep.hom p v = v := by
    let e := SmoothRep.cofanDirectSumEquiv A s hs
    let x := (fixedVectorsEquiv e K.toSubgroup).symm ⟨v, hv⟩
    obtain ⟨y, hy⟩ := (fixedVectorsDirectSumMap_bijective
      (fun i => (A i).representation) K.toSubgroup).2 x
    have he : e (fixedVectorsDirectSumMap
        (fun i => (A i).representation) K.toSubgroup y).val = v := by
      rw [hy]
      exact e.apply_symm_apply v
    rw [← he]
    clear hy he x hv v
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz
    | of i w =>
      change SmoothRep.hom p (e (fixedVectorsDirectSumMap
          (fun i => (A i).representation) K.toSubgroup
          (DirectSum.lof ℂ I (fun i => fixedVectors (A i).representation K.toSubgroup) i w)).val) =
        e (fixedVectorsDirectSumMap
          (fun i => (A i).representation) K.toSubgroup
          (DirectSum.lof ℂ I (fun i => fixedVectors (A i).representation K.toSubgroup) i w)).val
      have hmap : (fixedVectorsDirectSumMap
          (fun i => (A i).representation) K.toSubgroup
          (DirectSum.lof ℂ I (fun i => fixedVectors (A i).representation K.toSubgroup) i w)).val =
          DirectSum.lof ℂ I (fun i => A i) i w.val := by
        exact DirectSum.lmap_lof
          (fun i => (fixedVectors (A i).representation K.toSubgroup).subtype) i w
      rw [hmap, SmoothRep.cofanDirectSumEquiv_lof, hp_apply]
      by_cases hi : Q i
      · exact ite_eq_left hi
      · have hw : w.val = 0 := (hA i |>.resolve_left hi).le w.property
        simp [hi, hw]
  have hT : fixedVectors (SmoothRep.subrepresentation s.pt T).representation K.toSubgroup = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    apply Subtype.ext
    have hf := hfixed v.val
      (map_mem_fixedVectors (SmoothRep.hom (SmoothRep.subtype s.pt T)) hv)
    exact hf.symm.trans v.property
  refine ⟨S, T, hS, hT, ?_⟩
  apply top_unique
  intro v _
  apply Submodule.mem_sup.mpr
  refine ⟨SmoothRep.hom p v, ⟨v, rfl⟩, v - SmoothRep.hom p v, ?_, ?_⟩
  · change SmoothRep.hom p (v - SmoothRep.hom p v) = 0
    rw [map_sub, hpp_apply, sub_self]
  · abel

/-- A supplied component decomposition and an explicit fixed-level dichotomy
give the objectwise splitting used by smooth duality. -/
theorem fixedVectorSplitting_of_components
    (P : I → ObjectProperty (SmoothRep.{0,uG,uV} ℂ G))
    (hdec : Renard.EveryObjectIsCoproductOfComponents P)
    (hP : ∀ i V, P i V → fixedVectorGenerated K.toSubgroup V ∨
      fixedVectors V.representation K.toSubgroup = ⊥) :
    fixedVectorSplitting.{uG,uV} K := by
  intro V
  obtain ⟨A, ι, hA, ⟨hs⟩⟩ := hdec V
  exact fixedVectorSplitting_of_cofan K A (Cofan.mk V ι) hs (fun i => hP i (A i) (hA i))

end Langlands.Jacquet
