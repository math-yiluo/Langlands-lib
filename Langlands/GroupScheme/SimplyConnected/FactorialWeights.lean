import Langlands.GroupScheme.SimplyConnected.FactorialCellData
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.Reductive.AffineSplitSurjectionFieldIsogeny

/-! # Fundamental weights of a split simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell CoordinateRootDatum

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G)

/-- For a simply connected group the coroots span the full cocharacter lattice. -/
theorem span_coroot_eq_top (hG : IsSimplyConnected G) :
    Submodule.span ℤ (Set.range D.P.coroot) = ⊤ := by
  have : Smooth G.X.hom := D.isReductive.smooth
  have hG' := isSimplyConnectedFieldExtension k k G hG
  have hmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise D.I G D.i
    D.isFibrewiseMaximal k
  have hred := AffineSplitSurjection.isReduced_fieldRealization k D.P
  have h := splitSimplyConnectedCorootSpan k _ hG' (splitTorus.commGroupScheme _ D.I)
    (isSplitTorus_splitTorus D.I) _ hmax D.J (fieldRealization k D.P) (D.hP.field k) hred
  have hc : ∀ α, (fieldRealization k D.P).coroot α =
      (splitTorus.cocharacterLatticeEquiv k D.I).symm (D.P.coroot α) := fun α => by
    rw [fieldRealization_coroot, splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
  let f := (splitTorus.cocharacterLatticeEquiv k D.I).toAddMonoidHom.toIntLinearMap
  rw [eq_top_iff]
  intro v _
  have hv : (splitTorus.cocharacterLatticeEquiv k D.I).symm v ∈
      (fieldRealization k D.P).corootSpan ℤ := by
    rw [h]
    trivial
  have hv' := Submodule.mem_map_of_mem (f := f) hv
  rw [RootPairing.corootSpan, Submodule.map_span, ← Set.range_comp] at hv'
  convert hv' using 2
  · ext α
    simp [f, hc]
  · simp [f]

open Classical in
/-- **Fundamental weights.** For a simply connected group there are characters `ω i` with
`⟨ω i, j∨⟩ = δᵢⱼ` for all simple roots `i, j`. -/
theorem exists_fundamentalWeights (hG : IsSimplyConnected G) :
    ∃ ω : D.J → (D.I → ℤ), ∀ i ∈ D.b.support, ∀ j ∈ D.b.support,
      coPairing (ω i) (D.P.coroot j) = if j = i then 1 else 0 := by
  classical
  let s := D.b.support
  let v : s → (D.I → ℤ) := fun j => D.P.coroot j
  have hli : LinearIndependent ℤ v := D.b.linearIndepOn_coroot
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    have : Set.range v = D.P.coroot '' s := by
      ext x
      simp [v]
    rw [this, RootPairing.Base.span_int_coroot_support, D.span_coroot_eq_top hG]
  let B := Module.Basis.mk hli hsp
  refine ⟨fun i => if h : i ∈ s then fun l => B.coord ⟨i, h⟩ (Pi.single l 1) else 0, ?_⟩
  intro i hi j hj
  have hi' : i ∈ s := hi
  simp only [dif_pos hi', coPairing]
  have hexp : D.P.coroot j = ∑ l, D.P.coroot j l • (Pi.single l 1 : D.I → ℤ) := by
    ext m
    simp [Finset.sum_apply, Pi.single_apply]
  have key : ∑ l, B.coord ⟨i, hi⟩ (Pi.single l 1) * D.P.coroot j l =
      B.coord ⟨i, hi⟩ (D.P.coroot j) := by
    conv_rhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, smul_eq_mul, mul_comm]
  rw [key]
  have hBj : D.P.coroot j = B ⟨j, hj⟩ := by simp [B, v]
  rw [hBj, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [Subtype.ext_iff]

end CellData

end Langlands.GroupScheme.SplitFactorial
