import Langlands.Representation.SubrepresentationLattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Restriction of an irreducible representation to a normal subgroup of finite index

For an irreducible representation `ρ` of a group `G` over a field and a normal subgroup
`N` of finite index, the restriction of `ρ` to `N` is semisimple and is the sum of
finitely many irreducible subrepresentations. The argument is Clifford's: the
restriction is finitely generated, so it has a maximal proper subrepresentation `M`;
the intersection of the finitely many translates of `M` is a `G`-invariant proper
subspace, hence zero, and the restriction embeds in the product of the corresponding
simple quotients.

If the centre of `G` acts by scalars, the same conclusions pass from `H ⊔ center G` to
`H`, since both subgroups have the same invariant subspaces.
-/

noncomputable section

namespace Langlands.FiniteIndexRestriction

open scoped MonoidAlgebra

universe uk uG uV

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]

section Generic

variable (ρ : Representation k G V)

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero (hirr : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra! h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [h v]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- The orbit of a nonzero vector of an irreducible representation spans it. -/
theorem span_orbit_eq_top (hirr : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Submodule.span k (Set.range fun g => ρ g v) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span k (Set.range fun g => ρ g v)
      apply_mem_toSubmodule := fun g x hx => by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨h, rfl⟩ := hy
          exact Submodule.subset_span ⟨g * h, by
            show ρ (g * h) v = ρ g (ρ h v)
            rw [map_mul, Module.End.mul_apply]⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
        | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy }
  rcases hirr.eq_bot_or_eq_top S with h | h
  · exfalso
    have hmem : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by
      show ρ 1 v = v
      rw [map_one]
      rfl⟩
    rw [h] at hmem
    exact hv hmem
  · exact congrArg Subrepresentation.toSubmodule h

/-- An atom of the lattice of subrepresentations is an irreducible representation. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    (S : Subrepresentation ρ) (hS : IsAtom S) : S.toRepresentation.IsIrreducible := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  let j : S.toRepresentation.asModule →ₗ[k[G]] e S :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ i).codRestrict (e S)
      (fun v => v.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  exact (j.isSimpleModule_iff_of_bijective hj).mpr
    (isSimpleModule_iff_isAtom.mpr ((e.isAtom_iff S).mpr hS))

end Generic

section Normal

variable (ρ : Representation k G V) (N : Subgroup G) [N.Normal]

/-- Every element is an element of `N` times the chosen representative of its coset. -/
theorem exists_mem_mul_out (g : G) :
    ∃ n ∈ N, g = n * (QuotientGroup.mk g : G ⧸ N).out := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
  refine ⟨(QuotientGroup.mk g : G ⧸ N).out * (h : G)⁻¹ *
    ((QuotientGroup.mk g : G ⧸ N).out)⁻¹, ?_, ?_⟩
  · exact ‹N.Normal›.conj_mem _ (inv_mem h.property) _
  · rw [hh]
    group

/-- The subrepresentation `{x | ρ g x ∈ S}` of the restriction to a normal subgroup `N`,
that is, the translate `g⁻¹ S`. Normality of `N` makes it invariant. -/
def translate (g : G) (S : Subrepresentation (ρ.comp N.subtype)) :
    Subrepresentation (ρ.comp N.subtype) where
  toSubmodule := S.toSubmodule.comap (ρ g)
  apply_mem_toSubmodule n x hx := by
    have hn : g * (n : G) * g⁻¹ ∈ N := ‹N.Normal›.conj_mem _ n.property g
    have hS := S.apply_mem_toSubmodule ⟨_, hn⟩ hx
    change ρ g (ρ n x) ∈ S.toSubmodule
    change ρ (g * n * g⁻¹) (ρ g x) ∈ S.toSubmodule at hS
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul,
      Module.End.mul_apply] at hS

theorem mem_translate {g : G} {S : Subrepresentation (ρ.comp N.subtype)} {x : V} :
    x ∈ translate ρ N g S ↔ ρ g x ∈ S :=
  Iff.rfl

/-- Translation by `g` is an order automorphism of the subrepresentation lattice. -/
def translateOrderIso (g : G) :
    Subrepresentation (ρ.comp N.subtype) ≃o Subrepresentation (ρ.comp N.subtype) where
  toFun := translate ρ N g
  invFun := translate ρ N g⁻¹
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    change ρ g (ρ g⁻¹ x) ∈ S.toSubmodule ↔ x ∈ S.toSubmodule
    rw [Representation.self_inv_apply]
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    change ρ g⁻¹ (ρ g x) ∈ S.toSubmodule ↔ x ∈ S.toSubmodule
    rw [Representation.inv_self_apply]
  map_rel_iff' {S S'} := by
    constructor
    · intro h x hx
      have hx' : ρ g⁻¹ x ∈ translate ρ N g S := by
        rw [mem_translate, Representation.self_inv_apply]
        exact hx
      have : ρ g⁻¹ x ∈ translate ρ N g S' := h hx'
      rwa [mem_translate, Representation.self_inv_apply] at this
    · intro h x hx
      exact h hx

variable [N.FiniteIndex]

/-- The restriction to a normal subgroup of finite index is finitely generated: the
translates of a nonzero vector by coset representatives generate it. -/
theorem finite_asModule (hirr : ρ.IsIrreducible) :
    Module.Finite k[N] (Representation.asModule (ρ.comp N.subtype)) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero ρ hirr
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  let t : Finset (Representation.asModule (ρ.comp N.subtype)) :=
    Finset.univ.image fun r : G ⧸ N => (show (Representation.asModule (ρ.comp N.subtype)) from ρ r.out v)
  refine ⟨⟨t, ?_⟩⟩
  let S : Subrepresentation (ρ.comp N.subtype) := Subrepresentation.ofSubmodule'
    (Submodule.span k[N] (t : Set (Representation.asModule (ρ.comp N.subtype))))
  have hmem : ∀ g : G, ρ g v ∈ S := by
    intro g
    obtain ⟨n, hn, hg⟩ := exists_mem_mul_out N g
    have hout : ρ (QuotientGroup.mk g : G ⧸ N).out v ∈ S :=
      Subrepresentation.mem_ofSubmodule'_iff.mpr
        (Submodule.subset_span (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem _ (Finset.mem_univ _))))
    have := S.apply_mem_toSubmodule ⟨n, hn⟩ hout
    rw [hg, map_mul, Module.End.mul_apply]
    exact this
  have hle : Submodule.span k (Set.range fun g => ρ g v) ≤ S.toSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hmem g)
  rw [span_orbit_eq_top ρ hirr hv] at hle
  rw [Submodule.eq_top_iff']
  intro x
  exact hle (Submodule.mem_top (x := (show V from x)))

/-- The restriction to a normal subgroup of finite index has a maximal proper
subrepresentation. -/
theorem exists_isCoatom (hirr : ρ.IsIrreducible) :
    ∃ M : Subrepresentation (ρ.comp N.subtype), IsCoatom M := by
  have := finite_asModule ρ N hirr
  have hco : IsCoatomic (Subrepresentation (ρ.comp N.subtype)) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)).isCoatomic_iff.mpr
      inferInstance
  obtain ⟨v, hv⟩ := exists_ne_zero ρ hirr
  rcases hco.eq_top_or_exists_le_coatom ⊥ with h | ⟨M, hM, _⟩
  · exfalso
    apply hv
    have hmem : v ∈ (⊥ : Subrepresentation (ρ.comp N.subtype)) := by
      rw [h]
      exact Submodule.mem_top
    exact hmem
  · exact ⟨M, hM⟩

omit [N.FiniteIndex] in
/-- A vector all of whose coset-representative translates lie in a maximal proper
subrepresentation `M` is zero: the vectors whose whole `G`-orbit lies in `M` form a
`G`-invariant proper subspace. -/
theorem eq_zero_of_forall_out_mem (hirr : ρ.IsIrreducible)
    (M : Subrepresentation (ρ.comp N.subtype)) (hM : IsCoatom M) {x : V}
    (hx : ∀ r : G ⧸ N, ρ r.out x ∈ M) : x = 0 := by
  let I : Subrepresentation ρ :=
    { toSubmodule := ⨅ g : G, M.toSubmodule.comap (ρ g)
      apply_mem_toSubmodule := fun h y hy => by
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
        intro g
        rw [← Module.End.mul_apply, ← map_mul]
        exact hy (g * h) }
  have hxI : x ∈ I.toSubmodule := by
    simp only [I, Submodule.mem_iInf, Submodule.mem_comap]
    intro g
    obtain ⟨n, hn, hg⟩ := exists_mem_mul_out N g
    rw [hg, map_mul, Module.End.mul_apply]
    exact M.apply_mem_toSubmodule ⟨n, hn⟩ (hx _)
  rcases hirr.eq_bot_or_eq_top I with h | h
  · rw [h] at hxI
    exact hxI
  · exfalso
    apply hM.1
    apply top_unique
    intro y _
    have hy : y ∈ I.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    simp only [I, Submodule.mem_iInf, Submodule.mem_comap] at hy
    have := hy 1
    rwa [map_one, Module.End.one_apply] at this

/-- Clifford: the restriction of an irreducible representation to a normal subgroup of
finite index is a semisimple module over the group algebra of the subgroup. -/
theorem isSemisimpleModule_asModule (hirr : ρ.IsIrreducible) :
    IsSemisimpleModule k[N] (Representation.asModule (ρ.comp N.subtype)) := by
  classical
  obtain ⟨M, hM⟩ := exists_isCoatom ρ N hirr
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  let Mr : G ⧸ N → Submodule k[N] (Representation.asModule (ρ.comp N.subtype)) :=
    fun r => e (translate ρ N r.out M)
  have hMr : ∀ r, IsCoatom (Mr r) := fun r =>
    (e.isCoatom_iff _).mpr (((translateOrderIso ρ N r.out).isCoatom_iff M).mpr hM)
  have : ∀ r, IsSimpleModule k[N] ((Representation.asModule (ρ.comp N.subtype)) ⧸ Mr r) := fun r =>
    isSimpleModule_iff_isCoatom.mpr (hMr r)
  let f := LinearMap.pi fun r => (Mr r).mkQ
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_pi, eq_bot_iff]
    intro x hx
    simp only [Submodule.ker_mkQ, Submodule.mem_iInf] at hx
    exact (Submodule.mem_bot _).mpr
      (eq_zero_of_forall_out_mem ρ N hirr M hM (x := show V from x) fun r => hx r)
  exact IsSemisimpleModule.of_injective f hf

/-- Clifford: the restriction to a normal subgroup of finite index is semisimple. -/
theorem isSemisimpleRepresentation_comp (hirr : ρ.IsIrreducible) :
    Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (isSemisimpleModule_asModule ρ N hirr)

/-- The restriction to a normal subgroup of finite index is the sum of finitely many
atoms of its subrepresentation lattice. -/
theorem exists_finite_atoms (hirr : ρ.IsIrreducible) :
    ∃ (m : ℕ) (W : Fin m → Subrepresentation (ρ.comp N.subtype)),
      (∀ i, IsAtom (W i)) ∧ (⨆ i, (W i).toSubmodule) = ⊤ := by
  classical
  have hfin := finite_asModule ρ N hirr
  have := isSemisimpleModule_asModule ρ N hirr
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  have hc : IsCompactElement (⊤ : Submodule k[N] (Representation.asModule (ρ.comp N.subtype))) :=
    (Submodule.fg_iff_compact ⊤).mp hfin.fg_top
  let ι := {a : Submodule k[N] (Representation.asModule (ρ.comp N.subtype)) // IsSimpleModule k[N] a}
  obtain ⟨t, ht⟩ := hc.exists_finset_of_le_iSup (fun a : ι => a.val) (by
    rw [← IsSemisimpleModule.sSup_simples_eq_top]
    exact sSup_le fun a ha => le_iSup_of_le (⟨a, ha⟩ : ι) le_rfl)
  let a : Fin t.card → ι := fun i => (t.equivFin.symm i).val
  refine ⟨t.card, fun i => e.symm (a i).val, fun i => ?_, ?_⟩
  · exact (e.symm.isAtom_iff _).mpr (isSimpleModule_iff_isAtom.mp (a i).property)
  · have hsup : (⨆ i, (a i).val) = ⊤ := by
      apply top_unique
      refine ht.trans (iSup₂_le fun b hb => ?_)
      exact le_iSup_of_le (t.equivFin ⟨b, hb⟩) (by simp [a])
    rw [← Langlands.Subrepresentation.toSubmodule_iSup, ← e.symm.map_iSup, hsup,
      e.symm.map_top]
    rfl

end Normal

section Center

variable (ρ : Representation k G V) (H : Subgroup G)

/-- When the centre acts by scalars, the invariant subspaces for `H ⊔ center G` and for
`H` coincide. -/
def supCenterOrderIso (hscalar : ∀ z : Subgroup.center G, ∃ c : k, ∀ v : V, ρ z v = c • v) :
    Subrepresentation (ρ.comp (H ⊔ Subgroup.center G).subtype) ≃o
      Subrepresentation (ρ.comp H.subtype) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        S.apply_mem_toSubmodule ⟨g.val, Subgroup.mem_sup_left g.property⟩ hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨h, hh, z, hz, heq⟩ := Subgroup.mem_sup_of_normal_right.mp g.property
        obtain ⟨c, hc⟩ := hscalar ⟨z, hz⟩
        change ρ g.val v ∈ S.toSubmodule
        rw [← heq, map_mul, Module.End.mul_apply, hc]
        exact S.apply_mem_toSubmodule ⟨h, hh⟩ (S.toSubmodule.smul_mem c hv) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Clifford's theorem for a normal subgroup `H` whose join with the centre has finite
index, when the centre acts by scalars: the restriction to `H` is semisimple and is
spanned by finitely many irreducible subrepresentations. -/
theorem finite_irreducible_restriction [H.Normal]
    [(H ⊔ Subgroup.center G).FiniteIndex] (hirr : ρ.IsIrreducible)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : k, ∀ v : V, ρ z v = c • v) :
    Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) ∧
      ∃ (m : ℕ) (W : Fin m → Subrepresentation (ρ.comp H.subtype)),
        (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧ (⨆ i, (W i).toSubmodule) = ⊤ := by
  let e := supCenterOrderIso ρ H hscalar
  refine ⟨e.complementedLattice_iff.mp
    (isSemisimpleRepresentation_comp ρ (H ⊔ Subgroup.center G) hirr), ?_⟩
  obtain ⟨m, W, hW, hsup⟩ := exists_finite_atoms ρ (H ⊔ Subgroup.center G) hirr
  exact ⟨m, fun i => e (W i), fun i =>
    isIrreducible_toRepresentation_of_isAtom _ ((e.isAtom_iff _).mpr (hW i)), hsup⟩

end Center

end Langlands.FiniteIndexRestriction
