import Langlands.GroupScheme.SimplyConnected.CenterCharacterQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! # Cartan relations on the actual full centre -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) d.pinning.torus)
local notation "C" => characterLattice (Functor.obj (BC) d.toralCenter.group)
local notation "P" => d.pinning.rootDatum

/-- The fundamental-weight basis of the split geometric torus of a
simply connected group. -/
abbrev absoluteFundamentalCharacterBasis (hsc : IsSimplyConnected G) : Module.Basis d.Vertex ℤ X :=
  Langlands.RootDatum.fundamentalWeightBasis P d.pinning.base
    (d.pinning_corootSpan_eq_top hsc)

private theorem span_simpleRoots :
    Submodule.span ℤ (Set.range (fun a : d.Vertex => (P).root a.val)) = (P).rootSpan ℤ := by
  change Submodule.span ℤ (Set.range ((P).root ∘ ((↑) : d.Vertex → d.pinning.rootIndex))) = _
  rw [Set.range_comp, Subtype.range_coe_subtype, Finset.setOfPred_mem,
    d.pinning.base.span_int_root_support]

private def simpleRootSpanBasis : Module.Basis d.Vertex ℤ ((P).rootSpan ℤ) :=
  (Module.Basis.span d.pinning.base.linearIndepOn_root).map
    (LinearEquiv.ofEq _ _ d.span_simpleRoots)

private theorem simpleRootSpanBasis_coe (a : d.Vertex) :
    ((d.simpleRootSpanBasis a : (P).rootSpan ℤ) : X) = (P).root a.val := by
  rw [simpleRootSpanBasis, Module.Basis.map_apply]
  exact Module.Basis.coe_span_apply d.pinning.base.linearIndepOn_root a

private theorem absoluteFundamentalCharacterBasis_repr_root (hsc : IsSimplyConnected G)
    (a b : d.Vertex) :
    (d.absoluteFundamentalCharacterBasis hsc).repr ((P).root a.val) b = d.cartan a b := by
  rw [absoluteFundamentalCharacterBasis, Langlands.RootDatum.fundamentalWeightBasis_repr,
    (P).root_coroot_eq_pairing]
  rfl

private theorem simpleRoot_eq_sum (hsc : IsSimplyConnected G) (a : d.Vertex) :
    (P).root a.val = ∑ b, d.cartan a b • d.absoluteFundamentalCharacterBasis hsc b := by
  simp_rw [← d.absoluteFundamentalCharacterBasis_repr_root hsc a]
  exact ((d.absoluteFundamentalCharacterBasis hsc).sum_repr ((P).root a.val)).symm

/-- The number of geometric centre characters is the absolute value of the
determinant of the numbered Cartan matrix. -/
theorem natCard_centerCharacter_eq_cartanDet (hsc : IsSimplyConnected G)
    {n : ℕ} (e : d.Vertex ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ a b, d.cartan a b = M (e a) (e b)) : Nat.card C = M.det.natAbs := by
  classical
  let W := (d.absoluteFundamentalCharacterBasis hsc).reindex e
  let R := d.simpleRootSpanBasis.reindex e
  let : Module.Free ℤ X := Module.Free.of_basis W
  let : Module.Finite ℤ X := Module.Finite.of_basis W
  have ha : W.toMatrix ((↑) ∘ R) = M.transpose := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Function.comp_apply]
    change W.repr ((R j : (P).rootSpan ℤ) : X) i = M j i
    dsimp only [W, R]
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
      d.simpleRootSpanBasis_coe, d.absoluteFundamentalCharacterBasis_repr_root, hM,
      e.apply_symm_apply, e.apply_symm_apply]
  calc
    Nat.card C = Nat.card (X ⧸ (P).rootSpan ℤ) :=
      (Nat.card_congr d.centerCharacterQuotientEquiv.toEquiv).symm
    _ = (W.det ((↑) ∘ R)).natAbs :=
      (Submodule.natAbs_det_basis_change W ((P).rootSpan ℤ) R).symm
    _ = M.det.natAbs := by rw [Module.Basis.det_apply, ha, Matrix.det_transpose]

/-- The fundamental centre characters generate every geometric character
by integral linear combinations. -/
theorem exists_centerCharacter_sum_fundamental (hsc : IsSimplyConnected G) (χ : C) :
    ∃ c : d.Vertex → ℤ, χ = ∑ a, c a • d.centerFundamentalCharacter hsc a := by
  obtain ⟨weight, rfl⟩ := d.centerCharacterRestriction_surjective χ
  let b := d.absoluteFundamentalCharacterBasis hsc
  refine ⟨b.repr weight, ?_⟩
  calc
    _ = d.centerCharacterRestriction (∑ a, b.repr weight a • b a) := by rw [b.sum_repr]
    _ = _ := by simp only [map_sum, map_smul]; rfl

/-- Each row of the Cartan matrix gives the corresponding simple-root
relation on the fundamental centre characters. -/
theorem centerCharacter_cartan_relation (hsc : IsSimplyConnected G) (a : d.Vertex) :
    ∑ b, d.cartan a b • d.centerFundamentalCharacter hsc b = 0 := by
  have h' := congrArg d.centerCharacterRestriction (d.simpleRoot_eq_sum hsc a).symm
  simp only [map_sum, map_smul] at h'
  exact h'.trans (d.toralCenter_root_comp_eq_zero a.val)

private theorem rootSpan_le_ker_constr (hsc : IsSimplyConnected G) {M : Type v} [AddCommGroup M]
    (w : d.Vertex → M) (hw : ∀ a, ∑ b, d.cartan a b • w b = 0) :
    (P).rootSpan ℤ ≤ ((d.absoluteFundamentalCharacterBasis hsc).constr ℤ w).ker := by
  let W := d.absoluteFundamentalCharacterBasis hsc
  rw [← d.span_simpleRoots]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change (W.constr ℤ w) ((P).root a.val) = 0
  rw [d.simpleRoot_eq_sum hsc a, map_sum]
  simpa only [map_smul, Module.Basis.constr_basis, W] using hw a

/-- Any assignment to the fundamental characters that satisfies the Cartan
relations defines an integral linear map from the actual centre characters. -/
def centerCharacterLift (hsc : IsSimplyConnected G) {M : Type v} [AddCommGroup M]
    (w : d.Vertex → M) (hw : ∀ a, ∑ b, d.cartan a b • w b = 0) : C →ₗ[ℤ] M :=
  (((P).rootSpan ℤ).liftQ ((d.absoluteFundamentalCharacterBasis hsc).constr ℤ w)
      (d.rootSpan_le_ker_constr hsc w hw)).comp d.centerCharacterQuotientEquiv.symm.toLinearMap

@[simp]
theorem centerCharacterLift_fundamental (hsc : IsSimplyConnected G) {M : Type v} [AddCommGroup M]
    (w : d.Vertex → M) (hw : ∀ a, ∑ b, d.cartan a b • w b = 0) (a : d.Vertex) :
    d.centerCharacterLift hsc w hw (d.centerFundamentalCharacter hsc a) = w a := by
  let W := d.absoluteFundamentalCharacterBasis hsc
  have he : d.centerCharacterQuotientEquiv (Submodule.Quotient.mk (W a)) =
      d.centerFundamentalCharacter hsc a := rfl
  rw [← he]
  unfold centerCharacterLift
  change ((P).rootSpan ℤ).liftQ (W.constr ℤ w) (d.rootSpan_le_ker_constr hsc w hw)
    (d.centerCharacterQuotientEquiv.symm
      (d.centerCharacterQuotientEquiv (Submodule.Quotient.mk (W a)))) = _
  rw [LinearEquiv.symm_apply_apply]
  change (W.constr ℤ w) (W a) = _
  exact W.constr_basis ℤ w a

end Langlands.GroupScheme.TitsIndexData
