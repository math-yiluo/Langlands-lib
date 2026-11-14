import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement cuspidalDatum_eq_of_equiv glCuspidalTensorAssociation
section FactorEquivalence
variable {K : Type*} [Field K] {G : Type*} [Group G]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  {W : κ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]

variable [∀ i, Nontrivial (V i)]

end FactorEquivalence
section Blocks
open Langlands.GeneralLinear
open Langlands.Geometric
variable {F : Type*} [Field F] {n : ℕ}

variable (B C : BlockShape n) {w : Equiv.Perm (Fin n)}

variable {B C}

end Blocks
section Datum
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uV uF

/-- Two cuspidal data are equal when their actual representatives are
equivalent after pulling back along a homomorphism that permutes matrix
entries by a coordinate bijection. -/
theorem cuspidalDatum_eq_of_equiv {F : LocalFieldPackage.{uF}}
    {T : F.TopologicalData} {ρ₁ ρ₂ : Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T}
    (A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ₁.rank))
    (A₂ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ₂.rank))
    (h₁ : ρ₁.IsRepresentedBy A₁) (h₂ : ρ₂.IsRepresentedBy A₂)
    (β : Fin ρ₁.rank ≃ Fin ρ₂.rank)
    (φ : GeneralLinear ρ₂.rank F.Carrier →* GeneralLinear ρ₁.rank F.Carrier)
    (hφ : ∀ g x y, φ g x y = g (β x) (β y))
    (E : letI := T.topology
      Representation.Equiv (A₁.obj.representation.comp φ) A₂.obj.representation) :
    ρ₁ = ρ₂ := by
  let _ := T.topology
  obtain ⟨r, hr, c₁⟩ := ρ₁
  obtain ⟨r₂, hr₂, c₂⟩ := ρ₂
  obtain rfl : r = r₂ := Fin.equiv_iff_eq.mp ⟨β⟩
  have hc : c₁ = c₂ := by
    rw [← show A₁.isoClass = c₁ from h₁, ← show A₂.isoClass = c₂ from h₂]
    exact (SupercuspidalRep.isoClass_eq_iff A₁ A₂).mpr
      (nonempty_iso_of_equiv_comp_permuted A₁ A₂ β φ hφ E)
  rw [hc]

/-- Proof of `GLCuspidalTensorAssociationStatement`. -/
theorem glCuspidalTensorAssociation : GLCuspidalTensorAssociationStatement.{uV, uF} := by
  intro F T n _
  let _ := T.topology
  intro k l ρ ρ' h h' A A' hA hA' hassoc
  obtain ⟨w, hw, ⟨E⟩⟩ := hassoc
  have : ∀ i, Nontrivial (A i).obj := fun i =>
    nontrivial_of_isIrreducible (A i).obj.representation (hρ := (A i).property.1)
  have key : ∀ i,
      ρ i = ρ' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i) := by
    intro i
    have hE : Nonempty (Representation.Equiv
        ((A i).obj.representation.comp (factorHom hw i))
        (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)).obj.representation) := by
      refine nonempty_equiv_of_factor_actions (V := fun i => (A i).obj)
        (W := fun j => (A' j).obj)
        (hρ := isIrreducible_comp_of_surjective (A i).obj.representation
          (hρ := (A i).property.1) (factorHom hw i) (factorHom_surjective hw i))
        (hσ := (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)).property.1)
        ?_ ?_
        (equivComp E (MonoidHom.mulSingle _
          (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)))
      -- Elaborating the lemmas before unifying with the goals avoids slow unification.
      · intro g v
        have hl := external_leviConjugation_symm_mulSingle (fun i => (A i).obj.representation)
          hw i g v
        exact hl
      · intro g v
        have hl := external_mulSingle_tprod (fun j => (A' j).obj.representation)
          (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i) g v
        exact hl
    obtain ⟨E'⟩ := hE
    exact cuspidalDatum_eq_of_equiv (A i)
      (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)) (hA i)
      (hA' _) (blockPositionEquiv hw i) (factorHom hw i)
      (fun g x y => factorHom_apply_entry hw i g x y) E'
  let τ : Fin k ≃ Fin l := Equiv.ofBijective _ (blockImage_bijective hw)
  rw [← Fin.univ_val_map, ← Fin.univ_val_map, show ρ = ρ' ∘ τ from funext key,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

end Datum
end Langlands.AllFieldBZ.CuspidalSupport
