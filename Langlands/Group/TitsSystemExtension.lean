import Langlands.Group.TitsSystemRestricted

/-! # Extending a Tits system by a supplement

An internal representative-projection form of KP Lemma 1.4.12(2).
-/

namespace Langlands.Group.TitsSystem

universe u v

variable {G : Type u} [Group G]

/-- Inclusion of the restriction of `N` to an ambient subgroup `H` into `N`. -/
def restrictedInclusion (H N : Subgroup G) : N.subgroupOf H →* N where
  toFun n := ⟨((n : H) : G), n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A supplement contained in `K` factors every element of `K` with its other
factor in `K ∩ H`. -/
theorem exists_restricted_factor {H K T : Subgroup G}
    (hfactor : ∀ g : G, ∃ a : H, ∃ t : T, g = (a : G) * t)
    (hTK : T ≤ K) (k : K) :
    ∃ a : K.subgroupOf H, ∃ t : T, (k : G) = ((a : H) : G) * t := by
  obtain ⟨a, t, ha⟩ := hfactor k
  have hak : (a : G) ∈ K := by
    have heq : (a : G) = (k : G) * (t : G)⁻¹ := by simp [ha, mul_assoc]
    rw [heq]
    exact K.mul_mem k.property (K.inv_mem (hTK t.property))
  exact ⟨⟨a, hak⟩, t, ha⟩

variable {W : Type v} [Group W] {H B N T : Subgroup G}
  {π : N.subgroupOf H →* W} {π' : N →* W} {S : Set W}

/-- Extension of a Tits system on `H` to `G`, with explicit representative
compatibility and a supplement killed by the target Weyl projection. -/
theorem extension [H.Normal]
    (h : IsTitsSystem (B.subgroupOf H) (N.subgroupOf H) π S)
    (hfactor : ∀ g : G, ∃ a : H, ∃ t : T, g = (a : G) * t)
    (hTB : T ≤ B) (hTN : T ≤ N)
    (hNT : N ≤ Subgroup.normalizer (T : Set G))
    (hcompat : ∀ n : N.subgroupOf H, π' (restrictedInclusion H N n) = π n)
    (hkill : ∀ t : T, π' ⟨(t : G), hTN t.property⟩ = 1) :
    IsTitsSystem B N π' S := by
  have hfactorN := exists_restricted_factor hfactor hTN
  have hfactorB := exists_restricted_factor hfactor hTB
  have hproj : ∀ (n : N.subgroupOf H) (t : T),
      π' (restrictedInclusion H N n * ⟨(t : G), hTN t.property⟩) = π n := by
    intro n t
    rw [map_mul, hcompat, hkill, mul_one]
  refine {
    surjective := ?_
    ker_eq := ?_
    sup_eq := ?_
    closure_eq := h.closure_eq
    ne_one := h.ne_one
    mul_self := h.mul_self
    mul_mem_cell := ?_
    conj_not_le := ?_ }
  · intro w
    obtain ⟨n, hn⟩ := h.surjective w
    exact ⟨restrictedInclusion H N n, (hcompat n).trans hn⟩
  · ext n'
    obtain ⟨n, t, hn⟩ := hfactorN n'
    have hn' : n' = restrictedInclusion H N n * ⟨(t : G), hTN t.property⟩ :=
      Subtype.ext hn
    rw [hn']
    change π' (restrictedInclusion H N n * ⟨(t : G), hTN t.property⟩) = 1 ↔
      ((n : H) : G) * (t : G) ∈ B
    rw [hproj, B.mul_mem_cancel_right (hTB t.property)]
    change n ∈ π.ker ↔ n ∈ (B.subgroupOf H).subgroupOf (N.subgroupOf H)
    rw [h.ker_eq]
  · apply top_unique
    intro g _
    obtain ⟨a, t, rfl⟩ := hfactor g
    apply (B ⊔ N).mul_mem _ ((show B ≤ B ⊔ N from le_sup_left) (hTB t.property))
    have ha : a ∈ B.subgroupOf H ⊔ N.subgroupOf H := by rw [h.sup_eq]; trivial
    have himage : (B.subgroupOf H ⊔ N.subgroupOf H).map H.subtype ≤ B ⊔ N := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      exact sup_le (le_trans inf_le_left le_sup_left) (le_trans inf_le_left le_sup_right)
    exact himage (Subgroup.mem_map_of_mem H.subtype ha)
  · intro s hs n' m' hn' b' hb'
    obtain ⟨n, t, hn⟩ := hfactorN n'
    obtain ⟨m, v, hm⟩ := hfactorN m'
    obtain ⟨b, u, hb⟩ := hfactorB ⟨b', hb'⟩
    change b' = ((b : H) : G) * u at hb
    have hnsub : n' = restrictedInclusion H N n * ⟨(t : G), hTN t.property⟩ :=
      Subtype.ext hn
    have hmsub : m' = restrictedInclusion H N m * ⟨(v : G), hTN v.property⟩ :=
      Subtype.ext hm
    have hns : π n = s := by rw [hnsub, hproj] at hn'; exact hn'
    have hmp : π' m' = π m := by rw [hmsub, hproj]
    have htbH : (t : G) * ((b : H) : G) * (t : G)⁻¹ ∈ H :=
      (inferInstance : H.Normal).conj_mem _ (b : H).property _
    have htbB : (t : G) * ((b : H) : G) * (t : G)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (hTB t.property) b.property) (B.inv_mem (hTB t.property))
    let b₀ : H := ⟨(t : G) * ((b : H) : G) * (t : G)⁻¹, htbH⟩
    have hb₀ : b₀ ∈ B.subgroupOf H := htbB
    have htu : (t : G) * (u : G) ∈ T := T.mul_mem t.property u.property
    have htm : (((m : H) : G))⁻¹ * ((t : G) * (u : G)) * ((m : H) : G) ∈ T := by
      simpa only [inv_inv, Subgroup.subtype_apply] using (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (T : Set G)).inv_mem (hNT m.property)) _).1 htu
    let z : T := ⟨(((m : H) : G))⁻¹ * ((t : G) * (u : G)) * ((m : H) : G) * v,
      T.mul_mem htm v.property⟩
    have heq : (n' : G) * b' * (m' : G) =
        ((((n : H) * b₀ * (m : H)) : H) : G) * z := by
      change (n' : G) * b' * (m' : G) =
        ((n : H) : G) * ((t : G) * ((b : H) : G) * (t : G)⁻¹) * ((m : H) : G) *
          ((((m : H) : G))⁻¹ * ((t : G) * (u : G)) * ((m : H) : G) * (v : G))
      rw [hn, hm, hb]
      simp [mul_assoc]
    have hlift : ∀ (w : W) (a : H), a ∈ cell (B.subgroupOf H) π w →
        (a : G) * z ∈ cell B π' w := by
      rintro w a ⟨k, hk, c, hc, d, hd, rfl⟩
      exact ⟨restrictedInclusion H N k, (hcompat k).trans hk,
        c, hc, (d : G) * z, B.mul_mem hd (hTB z.property),
        by simp [restrictedInclusion, mul_assoc]⟩
    rw [heq, hmp]
    rcases h.mul_mem_cell s hs n m hns b₀ hb₀ with hc | hc
    · exact Or.inl (hlift _ _ hc)
    · exact Or.inr (hlift _ _ hc)
  · intro s hs n' hn'
    obtain ⟨n, t, hn⟩ := hfactorN n'
    have hnsub : n' = restrictedInclusion H N n * ⟨(t : G), hTN t.property⟩ :=
      Subtype.ext hn
    have hns : π n = s := by rw [hnsub, hproj] at hn'; exact hn'
    obtain ⟨b, hb, hnb⟩ := h.conj_not_le s hs n hns
    have htbB : (t : G)⁻¹ * (b : G) * (t : G) ∈ B :=
      B.mul_mem (B.mul_mem (B.inv_mem (hTB t.property)) hb) (hTB t.property)
    refine ⟨(t : G)⁻¹ * (b : G) * (t : G), htbB, ?_⟩
    intro hbad
    apply hnb
    change (n : H) * b * (n : H)⁻¹ ∈ B.subgroupOf H
    change ((n : H) : G) * (b : G) * (((n : H) : G))⁻¹ ∈ B
    simpa [hn, mul_assoc] using hbad

private theorem extension_mem_conjugate (B : Subgroup G) (n g : G) :
    g ∈ B.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * g * n ∈ B := by
  simpa using (Subgroup.mem_map_equiv (f := MulAut.conj n) (K := B) (x := g))

/-- Saturation extends from the restricted system once the target Tits axioms
hold and the supplement is normalized by the target normalizer. -/
theorem IsSaturated.extension
    (hsat : IsSaturated (B.subgroupOf H) (N.subgroupOf H))
    (h' : IsTitsSystem B N π' S)
    (hfactor : ∀ g : G, ∃ a : H, ∃ t : T, g = (a : G) * t)
    (hTB : T ≤ B) (hTN : T ≤ N)
    (hNT : N ≤ Subgroup.normalizer (T : Set G)) :
    IsSaturated B N := by
  apply le_antisymm
  · intro g hg
    have hgB : g ∈ B := by
      have hg1 := (Subgroup.mem_iInf.1 hg) (1 : N)
      simpa only [extension_mem_conjugate, Subgroup.coe_one, inv_one, one_mul, mul_one]
        using hg1
    obtain ⟨b, t, hgt⟩ := exists_restricted_factor hfactor hTB ⟨g, hgB⟩
    change g = ((b : H) : G) * t at hgt
    have hbconjs : (b : H) ∈ ⨅ n : N.subgroupOf H,
        (B.subgroupOf H).map (MulAut.conj (n : H)).toMonoidHom := by
      apply Subgroup.mem_iInf.2
      intro n
      rw [extension_mem_conjugate]
      have hgconj := (extension_mem_conjugate B
        (restrictedInclusion H N n) g).1
          ((Subgroup.mem_iInf.1 hg) (restrictedInclusion H N n))
      change (((n : H) : G))⁻¹ * g * ((n : H) : G) ∈ B at hgconj
      have htconj : (((n : H) : G))⁻¹ * (t : G) * ((n : H) : G) ∈ T := by
        simpa only [inv_inv, Subgroup.subtype_apply] using
          (Subgroup.mem_normalizer_iff.1
            ((Subgroup.normalizer (T : Set G)).inv_mem (hNT n.property)) _).1 t.property
      have hbconj := B.mul_mem hgconj (B.inv_mem (hTB htconj))
      change (((n : H) : G))⁻¹ * ((b : H) : G) * ((n : H) : G) ∈ B
      simpa [hgt, mul_assoc] using hbconj
    rw [hsat] at hbconjs
    refine ⟨hgB, ?_⟩
    rw [hgt]
    exact N.mul_mem hbconjs.2 (hTN t.property)
  · intro g hg
    apply Subgroup.mem_iInf.2
    intro n
    rw [extension_mem_conjugate]
    let k : N := ⟨g, hg.2⟩
    have hk : π' k = 1 := by
      change k ∈ π'.ker
      rw [h'.ker_eq]
      exact hg.1
    have hc : n⁻¹ * k * n ∈ π'.ker := by
      simp [MonoidHom.mem_ker, hk]
    rw [h'.ker_eq] at hc
    exact hc

end Langlands.Group.TitsSystem
