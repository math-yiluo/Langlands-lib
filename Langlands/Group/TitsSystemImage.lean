import Langlands.Group.TitsSystemRestricted

/-! # Epimorphic images of saturated Tits systems

The quotient transport of KP Lemma 1.4.12(1), expressed using a surjective
homomorphism whose kernel is contained in the Borel and normalizer subgroups.
The target Weyl projection is required to agree on every image representative.
-/

namespace Langlands.Group

universe u v w

namespace TitsSystem

variable {G : Type u} [Group G] {G' : Type v} [Group G']
  {W : Type w} [Group W] {B N : Subgroup G} {π : N →* W}

/-- The Weyl projection descended to the image normalizer. It is defined whenever
the source projection kills the kernel of the map on normalizers. -/
noncomputable def imageProjection (f : G →* G') (π : N →* W)
    (hker : (f.subgroupMap N).ker ≤ π.ker) : N.map f →* W :=
  (f.subgroupMap N).liftOfSurjective (f.subgroupMap_surjective N) ⟨π, hker⟩

/-- The descended projection agrees with the source on every representative. -/
theorem imageProjection_apply (f : G →* G') (π : N →* W)
    (hker : (f.subgroupMap N).ker ≤ π.ker) (n : N) :
    imageProjection f π hker (f.subgroupMap N n) = π n := by
  simp [imageProjection, MonoidHom.liftOfSurjective]

variable
  (f : G →* G') (π' : N.map f →* W)
  (hcompat : ∀ n : N, π' (f.subgroupMap N n) = π n)

include hcompat in
/-- A compatible projection identifies the images of the source Bruhat cells
with the target Bruhat cells. No kernel hypothesis is needed for this equality. -/
theorem image_cell (w : W) :
    f '' cell B π w = cell (B.map f) π' w := by
  ext y
  constructor
  · rintro ⟨x, ⟨n, hn, b, hb, c, hc, rfl⟩, rfl⟩
    refine ⟨f.subgroupMap N n, (hcompat n).trans hn,
      f b, Subgroup.mem_map_of_mem f hb, f c, Subgroup.mem_map_of_mem f hc, ?_⟩
    simp
  · rintro ⟨n', hn', b', ⟨b, hb, rfl⟩, c', ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨n, rfl⟩ := f.subgroupMap_surjective N n'
    exact ⟨b * (n : G) * c, ⟨n, (hcompat n).symm.trans hn', b, hb, c, hc, rfl⟩,
      by simp⟩

variable {f π' hcompat}

/-- Membership in an image subgroup can be tested before applying a map whose
kernel lies in that subgroup. -/
theorem apply_mem_map_iff (hker : f.ker ≤ B) (g : G) :
    f g ∈ B.map f ↔ g ∈ B := by
  change g ∈ (B.map f).comap f ↔ g ∈ B
  rw [Subgroup.comap_map_eq_self hker]

include hcompat in
/-- Under the Borel-kernel hypothesis a compatible image projection also
identifies the preimage of every Bruhat cell. -/
theorem apply_mem_cell_iff (hker : f.ker ≤ B) (w : W) (g : G) :
    f g ∈ cell (B.map f) π' w ↔ g ∈ cell B π w := by
  rw [← image_cell f π' hcompat]
  constructor
  · rintro ⟨x, ⟨n, hn, b, hb, c, hc, hx⟩, hfg⟩
    have hk : g * x⁻¹ ∈ B := hker (by
      change f (g * x⁻¹) = 1
      simp [← hfg])
    refine ⟨n, hn, (g * x⁻¹) * b, B.mul_mem hk hb, c, hc, ?_⟩
    rw [mul_assoc, hx]
    simp [mul_assoc]
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- Conjugate-subgroup membership, in the form used to descend saturation. -/
theorem mem_conjugate_iff (B : Subgroup G) (n g : G) :
    g ∈ B.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * g * n ∈ B := by
  simpa using (Subgroup.mem_map_equiv (f := MulAut.conj n) (K := B) (x := g))

/-- Saturation descends along a surjective homomorphism when its kernel lies in
both distinguished subgroups. -/
theorem IsSaturated.map (hsat : IsSaturated B N) (f : G →* G')
    (hf : Function.Surjective f) (hkerB : f.ker ≤ B) (hkerN : f.ker ≤ N) :
    IsSaturated (B.map f) (N.map f) := by
  apply Subgroup.comap_injective hf
  ext g
  change (f g ∈ ⨅ n : N.map f,
      (B.map f).map (MulAut.conj (n : G')).toMonoidHom) ↔
    (f g ∈ B.map f ∧ f g ∈ N.map f)
  rw [apply_mem_map_iff hkerB, apply_mem_map_iff hkerN]
  have hleft : (f g ∈ ⨅ n : N.map f,
      (B.map f).map (MulAut.conj (n : G')).toMonoidHom) ↔
      g ∈ ⨅ n : N, B.map (MulAut.conj (n : G)).toMonoidHom := by
    simp only [Subgroup.mem_iInf, mem_conjugate_iff]
    constructor
    · intro hg n
      have hn := hg (f.subgroupMap N n)
      change (f (n : G))⁻¹ * f g * f (n : G) ∈ B.map f at hn
      rw [← map_inv, ← map_mul, ← map_mul] at hn
      exact (apply_mem_map_iff hkerB _).1 hn
    · intro hg n'
      obtain ⟨n, rfl⟩ := f.subgroupMap_surjective N n'
      change (f (n : G))⁻¹ * f g * f (n : G) ∈ B.map f
      simpa only [map_mul, map_inv] using
        (Subgroup.mem_map_of_mem f (hg n))
  rw [hleft, hsat]
  rfl

end TitsSystem

namespace IsTitsSystem

open TitsSystem

variable {G : Type u} [Group G] {G' : Type v} [Group G']
  {W : Type w} [Group W] {B N : Subgroup G} {π : N →* W} {S : Set W}

/-- KP Lemma 1.4.12(1), for an arbitrary epimorphism and a representative-compatible
projection to the same Weyl group. -/
theorem map (h : IsTitsSystem B N π S) (f : G →* G')
    (hf : Function.Surjective f) (hker : f.ker ≤ B ⊓ N)
    (π' : N.map f →* W) (hcompat : ∀ n : N, π' (f.subgroupMap N n) = π n) :
    IsTitsSystem (B.map f) (N.map f) π' S where
  surjective w := by
    obtain ⟨n, hn⟩ := h.surjective w
    exact ⟨f.subgroupMap N n, (hcompat n).trans hn⟩
  ker_eq := by
    ext n'
    obtain ⟨n, rfl⟩ := f.subgroupMap_surjective N n'
    change π' (f.subgroupMap N n) = 1 ↔ f (n : G) ∈ B.map f
    rw [hcompat, apply_mem_map_iff (fun x hx => (hker hx).1)]
    change n ∈ π.ker ↔ n ∈ B.subgroupOf N
    rw [h.ker_eq]
  sup_eq := by
    rw [← Subgroup.map_sup, h.sup_eq, Subgroup.map_top_of_surjective f hf]
  closure_eq := h.closure_eq
  ne_one := h.ne_one
  mul_self := h.mul_self
  mul_mem_cell s hs n' m' hn' b' hb' := by
    obtain ⟨n, rfl⟩ := f.subgroupMap_surjective N n'
    obtain ⟨m, rfl⟩ := f.subgroupMap_surjective N m'
    obtain ⟨b, hb, rfl⟩ := hb'
    have hn : π n = s := (hcompat n).symm.trans hn'
    have hc := h.mul_mem_cell s hs n m hn b hb
    change f (n : G) * f b * f (m : G) ∈ _
    rw [hcompat]
    rcases hc with hc | hc
    · exact Or.inl (by
        rw [← map_mul, ← map_mul]
        exact (apply_mem_cell_iff (fun x hx => (hker hx).1)
          (π' := π') (hcompat := hcompat) _ _).2 hc)
    · exact Or.inr (by
        rw [← map_mul, ← map_mul]
        exact (apply_mem_cell_iff (fun x hx => (hker hx).1)
          (π' := π') (hcompat := hcompat) _ _).2 hc)
  conj_not_le s hs n' hn' := by
    obtain ⟨n, rfl⟩ := f.subgroupMap_surjective N n'
    obtain ⟨b, hb, hnb⟩ := h.conj_not_le s hs n ((hcompat n).symm.trans hn')
    refine ⟨f b, Subgroup.mem_map_of_mem f hb, ?_⟩
    change f (n : G) * f b * (f (n : G))⁻¹ ∉ B.map f
    rw [← map_inv, ← map_mul, ← map_mul,
      apply_mem_map_iff (fun x hx => (hker hx).1)]
    exact hnb

/-- A Borel-kernel hypothesis makes the source Weyl projection descend. -/
theorem ker_subgroupMap_le (h : IsTitsSystem B N π S) (f : G →* G')
    (hker : f.ker ≤ B) : (f.subgroupMap N).ker ≤ π.ker := by
  intro n hn
  rw [h.ker_eq]
  apply hker
  exact congrArg Subtype.val (MonoidHom.mem_ker.1 hn)

/-- Epimorphic-image transport using the canonical descended Weyl projection. -/
theorem map_imageProjection (h : IsTitsSystem B N π S) (f : G →* G')
    (hf : Function.Surjective f) (hker : f.ker ≤ B ⊓ N) :
    IsTitsSystem (B.map f) (N.map f)
      (imageProjection f π (h.ker_subgroupMap_le f (le_trans hker inf_le_left))) S :=
  h.map f hf hker _ (imageProjection_apply f π _)

end IsTitsSystem

end Langlands.Group
