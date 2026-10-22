import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.OrderOfElement

/-! Vanishing of nonconjugating geometric pieces for associated Levis. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric
open scoped Pointwise

universe uF uV

/-- In the subgroup orbit of a finite group of automorphisms, containment is equality. -/
theorem finiteAutomorphismOrbit_eq_of_le
    {G H : Type*} [Group G] [Finite G] [Group H]
    (φ : G →* MulAut H) (K : Subgroup H) (g h : G)
    (hle : K.map (φ g).toMonoidHom ≤ K.map (φ h).toMonoidHom) :
    K.map (φ g).toMonoidHom = K.map (φ h).toMonoidHom := by
  let : MulAction G (Subgroup H) := MulAction.compHom (Subgroup H) φ
  let : CovariantClass G (Subgroup H) HSMul.hSMul LE.le :=
    ⟨fun _ _ _ hab => Subgroup.map_mono hab⟩
  change g • K ≤ h • K at hle
  have hback : (h⁻¹ * g) • K ≤ K := by
    simpa only [smul_smul, inv_mul_cancel, one_smul] using smul_mono_right h⁻¹ hle
  have hfix := smul_eq_of_smul_le hback
  have heq := congrArg (fun A : Subgroup H => h • A) hfix
  change g • K = h • K
  simpa only [smul_smul, mul_inv_cancel_left] using heq

/-- Association and containment suffice for equality under a permutation conjugation. -/
theorem conjugatesLevi_of_le_of_associated
    {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
    (hBC : LevisAssociated (F := F) B C) (w : Equiv.Perm (Fin n))
    (hle : (B.leviSubgroup F).map
      (MulAut.conj (permutation n F w)).toMonoidHom ≤ C.leviSubgroup F) :
    ConjugatesLevi (F := F) B C w := by
  obtain ⟨⟨v, hv⟩⟩ := hBC
  change (B.leviSubgroup F).map
    (MulAut.conj (permutation n F v)).toMonoidHom = C.leviSubgroup F at hv
  change (B.leviSubgroup F).map
    (MulAut.conj (permutation n F w)).toMonoidHom = C.leviSubgroup F
  rw [← hv] at hle ⊢
  exact finiteAutomorphismOrbit_eq_of_le
    (MulAut.conj.comp (permutation n F)) (B.leviSubgroup F) w v hle

/-- At associated Levis, a nonconjugating permutation cannot have a full source refinement. -/
theorem source_refinement_proper_of_associated_nonconjugating
    {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
    (hBC : LevisAssociated (F := F) B C) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (hS : IsIntersectionRefinement (F := F) B C w S)
    (hw : ¬ ConjugatesLevi (F := F) B C w) :
    refinedParabolic F B S ≠ ⊤ := by
  intro hfull
  apply hw
  apply conjugatesLevi_of_le_of_associated B C hBC w
  have hs : sourceLevi F B C w = ⊤ :=
    hS.2.1.trans (refinedLevi_eq_top_of_refinedParabolic_eq_top B S hfull)
  intro g hg
  obtain ⟨x, ⟨m, rfl⟩, rfl⟩ := hg
  exact (show m ∈ sourceLevi F B C w from hs ▸ Subgroup.mem_top m)

/-- The published vanishing component, for every rank including zero. -/
theorem associatedGeometricPieceVanishing
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ hBC w S R hS hR hw
  exact geometricPieceFunctor_subsingleton_of_proper_source F T B C w.val S R
    hS.2.1 hR.2.1 ρ hρ
    (source_refinement_proper_of_associated_nonconjugating B C hBC w.val S hS hw)

end Langlands.CuspidalSupport
