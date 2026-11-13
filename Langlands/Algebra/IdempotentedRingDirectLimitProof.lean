import Langlands.Algebra.IdempotentedDirectLimitStatements

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uI uA uM uT

namespace IdempotentedDirectLimitProof

/-- Gluing additive maps along a directed covering by additive subgroups. -/
theorem additiveUnion {ι : Type uI} [Preorder ι]
    {M : Type uM} [AddCommGroup M] {T : Type uT} [AddCommGroup T]
    (S : ι → AddSubgroup M) (hS : Monotone S)
    (hdir : ∀ i j : ι, ∃ k, i ≤ k ∧ j ≤ k)
    (hcover : ∀ m : M, ∃ i, m ∈ S i)
    (g : ∀ i, S i →+ T)
    (hg : ∀ i j, i ≤ j → ∀ m (hi : m ∈ S i) (hj : m ∈ S j),
      g i ⟨m, hi⟩ = g j ⟨m, hj⟩) :
    ∃! h : M →+ T, ∀ i (m : S i), h m = g i m := by
  classical
  choose index hindex using hcover
  let value (m : M) : T := g (index m) ⟨m, hindex m⟩
  have value_eq (i : ι) (m : M) (hm : m ∈ S i) :
      value m = g i ⟨m, hm⟩ := by
    obtain ⟨k, hik, hjk⟩ := hdir (index m) i
    exact (hg (index m) k hik m (hindex m) (hS hik (hindex m))).trans
      (hg i k hjk m hm (hS hik (hindex m))).symm
  let h : M →+ T :=
    { toFun := value
      map_zero' := by
        rw [value_eq (index 0) 0 (S (index 0)).zero_mem]
        exact (g (index 0)).map_zero
      map_add' := by
        intro m n
        obtain ⟨k, hmk, hnk⟩ := hdir (index m) (index n)
        have hm := hS hmk (hindex m)
        have hn := hS hnk (hindex n)
        rw [value_eq k (m + n) ((S k).add_mem hm hn),
          value_eq k m hm, value_eq k n hn]
        exact (g k).map_add ⟨m, hm⟩ ⟨n, hn⟩ }
  refine ⟨h, fun i m => value_eq i m m.property, ?_⟩
  intro h' hh'
  apply AddMonoidHom.ext
  intro m
  exact (hh' (index m) ⟨m, hindex m⟩).trans (value_eq _ _ _).symm

/-- Filtering idempotents remain directed after restricting to the filtering set. -/
theorem directed {A : Type uA} [NonUnitalRing A] (J : Set (Idempotent A))
    (hJ : ∀ s : Finset (Idempotent A), ∃ f ∈ J, ∀ e ∈ s, e ≤ f) :
    ∀ e f : J, ∃ k : J, e ≤ k ∧ f ≤ k := by
  classical
  intro e f
  obtain ⟨k, hk, hbound⟩ := hJ {e.val, f.val}
  exact ⟨⟨k, hk⟩, hbound e.val (by simp), hbound f.val (by simp)⟩

/-- Cofinality moves every ring element into a corner indexed by the filtering set. -/
theorem corner_cover {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (J : Set (Idempotent A))
    (hJ : ∀ s : Finset (Idempotent A), ∃ f ∈ J, ∀ e ∈ s, e ≤ f)
    (a : A) : ∃ e : J, a ∈ e.val.corner := by
  obtain ⟨e, he⟩ := hA.exists_mem_corner a
  obtain ⟨f, hf, hef⟩ := hJ {e}
  exact ⟨⟨f, hf⟩, (hef e (Finset.mem_singleton_self e)) he⟩

end IdempotentedDirectLimitProof

open IdempotentedDirectLimitProof

/-- Renard I.1.2: the corner inclusions have both direct-limit universal properties. -/
theorem idempotentedRingDirectLimitStatement :
    IdempotentedRingDirectLimitStatement.{uA, uT} := by
  intro A _ hA J hJ
  have hcover := corner_cover hA J hJ
  have hdir := directed J hJ
  constructor
  · intro T _ g hg
    obtain ⟨h, hh, hu⟩ := additiveUnion
      (fun e : J => e.val.corner.toAddSubgroup)
      (fun _ _ hef => hef) hdir hcover
      (fun e => g e.val e.property)
      (fun e f hef => hg e.val e.property f.val f.property hef)
    exact ⟨h, fun e he => hh ⟨e, he⟩, fun h' hh' =>
      hu h' (fun e => hh' e.val e.property)⟩
  · intro T _ g hg
    obtain ⟨h, hh, hu⟩ := additiveUnion
      (fun e : J => e.val.corner.toAddSubgroup)
      (fun _ _ hef => hef) hdir hcover
      (fun e => (g e.val e.property).toAddMonoidHom)
      (fun e f hef => hg e.val e.property f.val f.property hef)
    have hmul (a b : A) : h (a * b) = h a * h b := by
      obtain ⟨e, he⟩ := hcover a
      obtain ⟨f, hf⟩ := hcover b
      obtain ⟨k, hek, hfk⟩ := hdir e f
      have ha : a ∈ k.val.corner := hek he
      have hb : b ∈ k.val.corner := hfk hf
      rw [hh k ⟨a * b, k.val.corner.mul_mem ha hb⟩,
        hh k ⟨a, ha⟩, hh k ⟨b, hb⟩]
      exact (g k.val k.property).map_mul ⟨a, ha⟩ ⟨b, hb⟩
    let H : A →ₙ+* T := { h with map_mul' := hmul }
    refine ⟨H, fun e he => hh ⟨e, he⟩, ?_⟩
    intro H' hH'
    apply NonUnitalRingHom.ext
    intro a
    exact DFunLike.congr_fun (hu H'.toAddMonoidHom
      (fun e => hH' e.val e.property)) a

end Langlands.Algebra
