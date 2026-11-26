import Langlands.Representation.Clifford.Stabilizer
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Extension of an open-kernel irreducible class to its stabilizer
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

section Sup

variable {G : Type uG} [Group G] {N U : Subgroup G} [U.Normal]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For a normal subgroup `U`, a representation of `N` trivial on `N ⊓ U` extends to `N ⊔ U`,
trivially on `U`. -/
theorem exists_sup_extension (A : Representation ℂ N V)
    (hU : ∀ n : N, (n : G) ∈ U → A n = 1) :
    ∃ c : Representation ℂ (N ⊔ U : Subgroup G) V,
      (∀ n : N, c (Subgroup.inclusion le_sup_left n) = A n) ∧
      (∀ u : U, c (Subgroup.inclusion le_sup_right u) = 1) := by
  classical
  have hdec : ∀ k : (N ⊔ U : Subgroup G), ∃ y : N, ∃ z : U, (y : G) * z = k := by
    intro k
    obtain ⟨y, hy, z, hz, h⟩ := Subgroup.mem_sup_of_normal_right.mp k.2
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, h⟩
  let y : (N ⊔ U : Subgroup G) → N := fun k => Classical.choose (hdec k)
  have hy : ∀ k, ∃ z : U, ((y k : N) : G) * z = k := fun k => Classical.choose_spec (hdec k)
  have hwd : ∀ (k : (N ⊔ U : Subgroup G)) (y' : N) (z' : U), (y' : G) * z' = k →
      A (y k) = A y' := by
    intro k y' z' h'
    obtain ⟨z, hz⟩ := hy k
    have hmem : ((y' : N)⁻¹ * y k : N) ∈ ({n | (n : G) ∈ U} : Set N) := by
      change ((y' : G))⁻¹ * (y k : G) ∈ U
      have : ((y' : G))⁻¹ * (y k : G) = (z' : G) * (z : G)⁻¹ := by
        have e1 : (y k : G) = (k : G) * (z : G)⁻¹ := by rw [← hz]; group
        have e2 : (y' : G) = (k : G) * (z' : G)⁻¹ := by rw [← h']; group
        rw [e1, e2]
        group
      rw [this]
      exact U.mul_mem z'.2 (U.inv_mem z.2)
    have h1 := hU _ hmem
    have h2 : y k = y' * ((y' : N)⁻¹ * y k) := by group
    rw [h2, map_mul, h1, mul_one]
  let c : Representation ℂ (N ⊔ U : Subgroup G) V :=
    { toFun := fun k => A (y k)
      map_one' := by
        rw [hwd 1 1 1 (by simp), map_one]
      map_mul' := fun k₁ k₂ => by
        obtain ⟨z₁, hz₁⟩ := hy k₁
        obtain ⟨z₂, hz₂⟩ := hy k₂
        have hz : ((y k₂ : G))⁻¹ * z₁ * (y k₂ : G) * z₂ ∈ U :=
          U.mul_mem (‹U.Normal›.conj_mem' _ z₁.2 _) z₂.2
        rw [hwd (k₁ * k₂) (y k₁ * y k₂) ⟨_, hz⟩ (by
          simp only [Subgroup.coe_mul]
          rw [← hz₁, ← hz₂]
          group), map_mul] }
  refine ⟨c, fun n => ?_, fun u => ?_⟩
  · exact hwd _ n 1 (by simp)
  · change A (y _) = 1
    rw [hwd _ 1 u (by simp), map_one]

end Sup

section Topological

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]

/-- In a compact nonarchimedean group there is an open normal subgroup meeting `N` inside the
kernel of an open-kernel representation of `N`. -/
theorem exists_openNormal_le_ker (A : WildObj.{uG, uW} N) :
    ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧
      ∀ n : N, (n : G) ∈ U → A.1.representation n = 1 := by
  obtain ⟨O, hO, hOk⟩ := isOpen_induced_iff.mp A.2.2
  have h1 : (1 : G) ∈ O := by
    have : (1 : N) ∈ (A.1.representation.ker : Set N) := A.1.representation.ker.one_mem
    rw [← hOk] at this
    exact this
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O (hO.mem_nhds h1)
  obtain ⟨U, hU⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one V.isClopen V.one_mem
  refine ⟨U.toSubgroup, U.isNormal', U.isOpen, fun n hn => ?_⟩
  have hnO : (n : G) ∈ O := hV (hU hn)
  have : n ∈ (A.1.representation.ker : Set N) := by
    rw [← hOk]
    exact hnO
  exact this

omit [CompactSpace G] [NonarchimedeanGroup G] in
/-- A normal subgroup meeting `N` inside the kernel stabilizes the class. -/
theorem le_stabilizer_of_ker {A : WildObj.{uG, uW} N} {U : Subgroup G} [U.Normal]
    (hU : ∀ n : N, (n : G) ∈ U → A.1.representation n = 1) :
    U ≤ MulAction.stabilizer G (wildClass A) := by
  intro u hu
  change u • wildClass A = wildClass A
  rw [smul_wildClass]
  apply (wildClass_eq_iff _ _).mpr
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
  have hmem : ((n : G)⁻¹ * (u⁻¹ * n * u) : G) ∈ N :=
    N.mul_mem (N.inv_mem n.2) (‹N.Normal›.conj_mem' _ n.2 u)
  have hmemU : ((n : G)⁻¹ * (u⁻¹ * n * u) : G) ∈ U := by
    have h1 : (n : G)⁻¹ * u⁻¹ * n ∈ U := by
      simpa using ‹U.Normal›.conj_mem' _ (U.inv_mem hu) (n : G)
    have h2 := U.mul_mem h1 hu
    simpa [mul_assoc] using h2
  have hA := hU ⟨_, hmem⟩ hmemU
  have hsplit : (MulAut.conjNormal u⁻¹ n : N) = n * ⟨_, hmem⟩ := by
    apply Subtype.ext
    simp [MulAut.conjNormal_apply, mul_assoc]
  apply LinearMap.ext
  intro v
  change A.1.representation (MulAut.conjNormal u⁻¹ n) v = A.1.representation n v
  rw [hsplit, map_mul, hA, mul_one]

/-- In a compact nonarchimedean group the stabilizer of an open-kernel class is open. -/
theorem isOpen_stabilizer (A : WildObj.{uG, uW} N) :
    IsOpen (MulAction.stabilizer G (wildClass A) : Set G) := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_openNormal_le_ker A
  exact Subgroup.isOpen_mono (le_stabilizer_of_ker hU) hUo

/-- In a compact nonarchimedean group, when every commutator lies in `N` and
`CyclicOpenQuotients N` holds, an open-kernel irreducible representation of `N` extends to the
stabilizer of its class with open kernel. -/
theorem exists_extension_stabilizer (hab : CommutatorsIn N) (hcyc : CyclicOpenQuotients N)
    (A : WildObj.{uG, uW} N) :
    ∃ θ : Representation ℂ (MulAction.stabilizer G (wildClass A)) A.1,
      θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation ∧
      IsOpen (θ.ker : Set (MulAction.stabilizer G (wildClass A))) := by
  classical
  set H := MulAction.stabilizer G (wildClass A) with hHdef
  have hNH : N ≤ H := le_stabilizer _
  obtain ⟨U, hUn, hUo, hU⟩ := exists_openNormal_le_ker A
  have hUH : U ≤ H := le_stabilizer_of_ker hU
  have hHo : IsOpen (H : Set G) := isOpen_stabilizer A
  have : H.Normal := normal_of_le hab hNH
  have : H.FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen H hHo
    exact Subgroup.finiteIndex_of_finite_quotient
  let N' : Subgroup H := N.subgroupOf H
  let U' : Subgroup H := U.subgroupOf H
  have : U'.Normal := Subgroup.Normal.subgroupOf hUn H
  have : N'.Normal := Subgroup.Normal.subgroupOf ‹N.Normal› H
  let eN : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNH
  let A' : Representation ℂ N' A.1 := A.1.representation.comp eN.toMonoidHom
  have hU' : ∀ n : N', (n : H) ∈ U' → A' n = 1 := fun n hn => hU (eN n) hn
  obtain ⟨c, hcN, hcU⟩ := exists_sup_extension A' hU'
  let K : Subgroup H := N' ⊔ U'
  have hK : ∀ x : H, x ∈ K ↔ (x : G) ∈ N ⊔ U := by
    intro x
    change x ∈ N.subgroupOf H ⊔ U.subgroupOf H ↔ _
    rw [← Subgroup.subgroupOf_sup hNH hUH, Subgroup.mem_subgroupOf]
  have hNUo : IsOpen ((N ⊔ U : Subgroup G) : Set G) := Subgroup.isOpen_mono le_sup_right hUo
  have hNUH : N ⊔ U ≤ H := sup_le hNH hUH
  have : (N ⊔ U).Normal := normal_of_le hab le_sup_left
  obtain ⟨g, hg⟩ := hcyc (N ⊔ U) le_sup_left hNUo
  let e₀ := H.index
  have he₀ : e₀ ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let g₀ : H := ⟨g ^ e₀, pow_index_mem' hab hNH g⟩
  have hgH := zpow_mem_iff_dvd hNUH hg
  have hgNU := zpow_mem_iff_dvd (le_refl (N ⊔ U)) hg
  have hind : (N ⊔ U).relIndex H * H.index = (N ⊔ U).index := Subgroup.relIndex_mul_index hNUH
  let e := K.index
  have heK : e = (N ⊔ U).relIndex H := by
    change (N.subgroupOf H ⊔ U.subgroupOf H).index = _
    rw [← Subgroup.subgroupOf_sup hNH hUH]
    rfl
  have hg₀pow : ∀ t : ℤ, ((g₀ ^ t : H) : G) = g ^ ((e₀ : ℤ) * t) := by
    intro t
    rw [Subgroup.coe_zpow, zpow_mul, zpow_natCast]
  have hord : ∀ t : ℤ, g₀ ^ t ∈ K ↔ (e : ℤ) ∣ t := by
    intro t
    rw [hK, hg₀pow, hgNU, ← hind, heK, Nat.cast_mul, mul_comm ((N ⊔ U).relIndex H : ℤ)]
    exact mul_dvd_mul_iff_left (by exact_mod_cast he₀)
  have hgen : ∀ x : H, ∃ t : ℤ, x * (g₀ ^ t)⁻¹ ∈ K := by
    intro x
    obtain ⟨i, hi⟩ := hg x
    have hgi : g ^ i ∈ H := by
      have h1 := H.mul_mem (H.inv_mem (hNUH hi)) x.2
      simpa using h1
    obtain ⟨t, rfl⟩ := (hgH i).mp hgi
    refine ⟨t, (hK _).mpr ?_⟩
    simpa [hg₀pow] using hi
  have he : 0 < e := by
    rw [heK]
    have : (N ⊔ U).index ≠ 0 := by
      have := Subgroup.quotient_finite_of_isOpen _ hNUo
      exact (Subgroup.finiteIndex_of_finite_quotient).index_ne_zero
    rw [← hind] at this
    exact Nat.pos_of_ne_zero (left_ne_zero_of_mul this)
  have hKN : K.Normal := by
    have h1 : K = (N ⊔ U).subgroupOf H := (Subgroup.subgroupOf_sup hNH hUH).symm
    rw [h1]
    exact Subgroup.Normal.subgroupOf ‹_› H
  have hA' : A'.IsIrreducible := by
    have := A.2.1
    exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective A.1.representation
      eN.toMonoidHom eN.surjective
  have hcA : c.comp (Subgroup.inclusion (le_sup_left : N' ≤ K)) = A' := by
    ext n v
    exact congrArg (fun T => T v) (hcN n)
  have hc : c.IsIrreducible := Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp c _ (hcA ▸ hA')
  have hdec : ∀ k : K, ∃ y : N', ∃ z : U',
      k = Subgroup.inclusion (le_sup_left : N' ≤ K) y *
        Subgroup.inclusion (le_sup_right : U' ≤ K) z := by
    intro k
    obtain ⟨y, hy, z, hz, h⟩ := Subgroup.mem_sup_of_normal_right.mp k.2
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext h.symm⟩
  have hcval : ∀ (y : N') (z : U'), c (Subgroup.inclusion (le_sup_left : N' ≤ K) y *
      Subgroup.inclusion (le_sup_right : U' ≤ K) z) = A' y := by
    intro y z
    rw [map_mul, hcN, hcU, mul_one]
  have hinv : Nonempty (Representation.Equiv (c.comp (conjPow K g₀ 1)) c) := by
    have hfix : ((g₀ : G))⁻¹ • wildClass A = wildClass A := H.inv_mem g₀.2
    rw [smul_wildClass] at hfix
    obtain ⟨E⟩ := (wildClass_eq_iff _ _).mp hfix
    refine ⟨Representation.Equiv.mk E.toLinearEquiv fun k => ?_⟩
    obtain ⟨y, z, rfl⟩ := hdec k
    have hy' : (g₀ : H) * (y : H) * (g₀ : H)⁻¹ ∈ N' :=
      ‹N'.Normal›.conj_mem _ y.2 _
    have hz' : (g₀ : H) * (z : H) * (g₀ : H)⁻¹ ∈ U' :=
      ‹U'.Normal›.conj_mem _ z.2 _
    have hconj : conjPow K g₀ 1 (Subgroup.inclusion (le_sup_left : N' ≤ K) y *
        Subgroup.inclusion (le_sup_right : U' ≤ K) z) =
        Subgroup.inclusion (le_sup_left : N' ≤ K) ⟨_, hy'⟩ *
          Subgroup.inclusion (le_sup_right : U' ≤ K) ⟨_, hz'⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    have hE := E.isIntertwining' (eN y)
    change E.toLinearMap ∘ₗ c (conjPow K g₀ 1 _) = c _ ∘ₗ E.toLinearMap
    rw [hconj, hcval, hcval]
    have h1 : A' ⟨_, hy'⟩ = A.1.representation (MulAut.conjNormal (g₀ : G)⁻¹⁻¹ (eN y)) := by
      change A.1.representation (eN ⟨_, hy'⟩) = _
      congr 1
      apply Subtype.ext
      simp only [eN, MulAut.conjNormal_apply, inv_inv]
      rfl
    rw [h1]
    exact hE
  have hge : g₀ ^ e ∈ K := by
    rw [← zpow_natCast]
    exact (hord e).mpr dvd_rfl
  obtain ⟨θ, hθ⟩ := exists_extension c hc he (fun t ht => (hord t).mp ht) hge hgen hinv
  have hθK : ∀ k : K, θ k = c k := fun k => congrArg (fun f => f k) hθ
  refine ⟨θ, ?_, ?_⟩
  · ext n v
    have hn : Subgroup.inclusion hNH n =
        (Subgroup.inclusion (le_sup_left : N' ≤ K) (eN.symm n) : H) := by
      apply Subtype.ext
      rfl
    change θ (Subgroup.inclusion hNH n) v = A.1.representation n v
    rw [hn, hθK, hcN]
    change A.1.representation (eN (eN.symm n)) v = _
    rw [MulEquiv.apply_symm_apply]
  · have hU'θ : U' ≤ θ.ker := by
      intro u hu
      have h1 := hθK (Subgroup.inclusion (le_sup_right : U' ≤ K) ⟨u, hu⟩)
      rw [hcU] at h1
      exact h1
    exact Subgroup.isOpen_mono hU'θ (hUo.preimage continuous_subtype_val)

end Topological

end Langlands.Clifford
