import Langlands.BaseChange.InducedBlockFixedLevel
import Langlands.LocalField.PadicBridge
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Smooth.Admissibility.Extension
import Langlands.Representation.Tensor.ExternalSubquotient

/-! # Uniform fixed-vector detection on refining blocks -/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear Geometric
open WeylBranchPieces (IsSubquotient)

universe v z w

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (T : E.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

set_option backward.isDefEq.respectTransparency.types false

private theorem fixedVectors_ne_bot_of_subquotient
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type z} [AddCommGroup X] [Module ℂ X]
    {Y : Type w} [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {π : Representation ℂ G Y}
    (hρ : IsSmooth ρ) (hπ : IsSmooth π) (h : IsSubquotient ρ π)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hπK : fixedVectors π K.toSubgroup ≠ ⊥) : fixedVectors ρ K.toSubgroup ≠ ⊥ := by
  obtain ⟨U, q, hq⟩ := h
  obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπK
  obtain ⟨x, hx⟩ := Compact.CharZero.fixedVectorMap_surjective U.toRepresentation π
    (isSmooth_subrepresentation hρ U) hπ K hK q hq ⟨y, hy⟩
  have he : q x.val = y := congrArg Subtype.val hx
  refine (Submodule.ne_bot_iff _).mpr ⟨x.val.val, fun k => ?_, fun hz => ?_⟩
  · exact congrArg Subtype.val (x.property k)
  · apply hy₀
    rw [← he, show x.val = 0 from Subtype.ext hz, map_zero]

private theorem external_factor_fixedVectors
    {ι : Type} [Fintype ι] {G : ι → Type v} [∀ i, Group (G i)]
    {X : ι → Type z} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (G i) (X i)) (K : ∀ i, Subgroup (G i))
    (h : fixedVectors (FiniteTensor.external ρ) (Subgroup.pi Set.univ K) ≠ ⊥)
    (i : ι) : fixedVectors (ρ i) (K i) ≠ ⊥ := by
  classical
  intro hi
  apply h
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := FiniteTensor.fixedVectors_external_le ρ K hx
  have hmap : PiTensorProduct.map (fun j => (fixedVectors (ρ j) (K j)).subtype) = 0 := by
    apply PiTensorProduct.ext
    ext a
    rw [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
      LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
    exact (PiTensorProduct.tprod ℂ).map_coord_zero i
      ((Submodule.eq_bot_iff _).mp hi _ (a i).property)
  rw [hmap, LinearMap.zero_apply]

/-- At a compact open level on a product Levi, a visible subquotient of an
external tensor of normalized inductions forces each inducing factor to have
fixed vectors at a level that depends only on the refinement and ambient level. -/
def RelativeInducedBlockFixedLevelStatement : Prop :=
  letI := T.topology
  ∀ (K : OpenSubgroup (B.Levi E.Carrier)), IsCompact (K : Set (B.Levi E.Carrier)) →
    ∃ J : ∀ i j, OpenSubgroup (GeneralLinear ((S i).size j) E.Carrier),
      (∀ i j, IsCompact (J i j : Set (GeneralLinear ((S i).size j) E.Carrier))) ∧
      ∀ (A : ∀ i j, SmoothRep.{0,v,z} ℂ (GeneralLinear ((S i).size j) E.Carrier))
        (X : Type w) [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (B.Levi E.Carrier) X),
        IsSmooth π →
        IsSubquotient (FiniteTensor.external fun i =>
          ((T.normalizedProductInductionFunctor (S i)).obj (A i)).representation) π →
        fixedVectors π K.toSubgroup ≠ ⊥ →
        ∀ i j, fixedVectors (A i j).representation (J i j).toSubgroup ≠ ⊥

theorem relativeInducedBlockFixedLevel :
    RelativeInducedBlockFixedLevelStatement.{v,z,w} T B S := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  intro K hK
  let L (i : Fin B.length) : OpenSubgroup (GeneralLinear (B.size i) E.Carrier) :=
    K.comap (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) E.Carrier) i)
      (continuous_mulSingle i)
  have hL : Subgroup.pi Set.univ (fun i => (L i).toSubgroup) ≤ K.toSubgroup := by
    apply Subgroup.pi_le_iff.mpr
    rintro i _ ⟨g, hg, rfl⟩
    exact hg
  have hlevels (i : Fin B.length) :=
    inducedBlockFixedLevel.{v,z} E.Carrier (S i) (L i)
  choose J hJ hdetect using hlevels
  refine ⟨J, hJ, ?_⟩
  intro A X _ _ π hπ hsub hπK
  let M := FiniteTensor.externalSmoothObject
    (fun i => (T.normalizedProductInductionFunctor (S i)).obj (A i))
  have hM : fixedVectors M.representation K.toSubgroup ≠ ⊥ :=
    fixedVectors_ne_bot_of_subquotient M.isSmooth hπ hsub K hK hπK
  have hM' : fixedVectors M.representation (Subgroup.pi Set.univ
      (fun i => (L i).toSubgroup)) ≠ ⊥ := fun h =>
    hM (le_bot_iff.mp ((fixedVectors_antitone M.representation hL).trans_eq h))
  intro i j
  exact hdetect i (fun k => A i k) (fun k => (A i k).representation)
    (external_factor_fixedVectors _ _ hM' i) j

end Langlands.BaseChange.TwistedLeviPaleyWiener
