import Langlands.ClassFieldTheory.Local.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The universal property of the open finite quotient completion -/

noncomputable section

namespace Langlands.LocalClassField.ContinuousProfinite

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

@[simp]
theorem map_eta (f : G →ₜ* H) (g : G) : map f (eta G g) = eta H (f g) := rfl

omit [IsTopologicalGroup H] in
/-- Continuous maps on the completion are determined by their values on the source. -/
theorem hom_ext [T2Space H] {a b : Completion G →ₜ* H}
    (h : ∀ g : G, a (eta G g) = b (eta G g)) : a = b := by
  apply DFunLike.ext'
  exact (eta_dense G).equalizer a.continuous b.continuous (funext h)

section ProfiniteTarget

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

omit [T2Space H] in
/-- Open finite quotient coordinates separate elements of a profinite group. -/
theorem eta_injective : Function.Injective (eta H) := by
  apply (injective_iff_map_eq_one (eta H)).mpr
  intro x hx
  by_contra hne
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isClosed_singleton (x := x)).isOpen_compl (by simpa using Ne.symm hne)
  let : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let Q : OpenFiniteQuotient H := ⟨FiniteIndexNormalSubgroup.ofSubgroup N.toSubgroup, N.isOpen⟩
  have hQ : Q.projection x = 1 := congrArg (projection H Q) hx
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hQ
  exact hN hxN rfl

omit [T2Space H] [TotallyDisconnectedSpace H] in
/-- Compactness makes the dense canonical map from a profinite group onto. -/
theorem eta_surjective : Function.Surjective (eta H) := by
  have hc : IsClosed (Set.range (eta H)) := (isCompact_range (eta H).continuous).isClosed
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans (eta_dense H).closure_range)

/-- The actual open finite quotient completion fixes profinite groups. -/
def etaEquiv : H ≃ₜ* Completion H := by
  let e := MulEquiv.ofBijective (eta H).toMonoidHom ⟨eta_injective, eta_surjective⟩
  have he : Continuous e := (eta H).continuous
  exact { e with
    continuous_toFun := he
    continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

omit [T2Space H] in
@[simp]
theorem etaEquiv_apply (h : H) : etaEquiv h = eta H h := rfl

/-- Every continuous homomorphism to a profinite group extends to the completion. -/
def lift (f : G →ₜ* H) : Completion G →ₜ* H :=
  (ContinuousMonoidHom.toContinuousMonoidHom (etaEquiv (H := H)).symm).comp (map f)

omit [T2Space H] in
@[simp]
theorem lift_eta (f : G →ₜ* H) (g : G) : lift f (eta G g) = f g := by
  change etaEquiv.symm (map f (eta G g)) = f g
  rw [map_eta]
  exact etaEquiv.symm_apply_apply (f g)

/-- Density of the original map implies surjectivity of its extension. -/
theorem lift_surjective (f : G →ₜ* H) (hf : DenseRange f) :
    Function.Surjective (lift f) := by
  have hsub : Set.range f ⊆ Set.range (lift f) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨eta G g, lift_eta f g⟩
  have hd : Dense (Set.range (lift f)) := hf.mono hsub
  have hc : IsClosed (Set.range (lift f)) := (isCompact_range (lift f).continuous).isClosed
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans hd.closure_eq)

omit [T2Space H] in
/-- Descent of all actual source finite quotients makes the extension injective. -/
theorem lift_injective_of_finite_quotient_descent (f : G →ₜ* H)
    (h : ∀ N : OpenFiniteQuotient G,
      ∃ q : H →ₜ* N.Quotient, q.comp f = N.projection) :
    Function.Injective (lift f) := by
  intro x y hxy
  apply Subtype.ext
  funext N
  obtain ⟨q, hq⟩ := h N
  have heq : q.comp (lift f) = projection G N := by
    apply hom_ext
    intro g
    change q (lift f (eta G g)) = N.projection g
    rw [lift_eta]
    exact DFunLike.congr_fun hq g
  have hx : q (lift f x) = projection G N x := DFunLike.congr_fun heq x
  have hy : q (lift f y) = projection G N y := DFunLike.congr_fun heq y
  exact hx.symm.trans ((congrArg q hxy).trans hy)

/-- A dense map inducing every source finite quotient gives the unique completion
comparison. The finite quotient descent condition is an explicit hypothesis. -/
theorem existsUnique_equiv_of_finite_quotient_descent (f : G →ₜ* H)
    (hf : DenseRange f)
    (h : ∀ N : OpenFiniteQuotient G,
      ∃ q : H →ₜ* N.Quotient, q.comp f = N.projection) :
    ∃! e : Completion G ≃ₜ* H, ∀ g : G, e (eta G g) = f g := by
  let e := MulEquiv.ofBijective (lift f).toMonoidHom
    ⟨lift_injective_of_finite_quotient_descent f h, lift_surjective f hf⟩
  have he : Continuous e := (lift f).continuous
  let E : Completion G ≃ₜ* H := { e with
    continuous_toFun := he
    continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }
  refine ⟨E, lift_eta f, ?_⟩
  intro E' hE'
  apply ContinuousMulEquiv.ext
  exact congrFun ((eta_dense G).equalizer E'.continuous E.continuous
    (funext fun g => (hE' g).trans (lift_eta f g).symm))

end ProfiniteTarget

end Langlands.LocalClassField.ContinuousProfinite
