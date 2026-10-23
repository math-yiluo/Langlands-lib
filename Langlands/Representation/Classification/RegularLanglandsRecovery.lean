import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Mathlib.Order.Hom.Set

/-!
# Algebraic recovery from an actual block tensor equivalence

Construct isomorphisms of the irreducible factors of equivalent block tensor
representations. No comparison of Langlands quotients is asserted here.
-/

noncomputable section

namespace Langlands

open CategoryTheory

/-- An order isomorphism preserving all block sizes identifies the shapes. -/
theorem GeneralLinear.BlockShape.eq_of_orderIso {n : ℕ}
    (B C : GeneralLinear.BlockShape n)
    (a : Fin B.length ≃o Fin C.length)
    (h : ∀ i, B.size i = C.size (a i)) : B = C := by
  rcases B with ⟨r, b, hb, hsum⟩
  rcases C with ⟨s, c, hc, hsum'⟩
  have hrs : r = s := by simpa using Fintype.card_congr a.toEquiv
  subst s
  have ha : a = OrderIso.refl (Fin r) := Subsingleton.elim _ _
  have hbc : b = c := by
    funext i
    simpa only [ha, OrderIso.refl_apply] using h i
  subst c
  rfl

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Choose an actual smooth isomorphism in each irreducible factor from an
actual equivalence of the two external block tensor representations. -/
def blockIsoOfTensorEquiv {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (σ τ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (_hσ : ∀ i, Representation.IsIrreducible (σ i).representation)
    (_hτ : ∀ i, Representation.IsIrreducible (τ i).representation)
    (_E : (B.blockTensor (fun i => (σ i).representation)).Equiv
      (B.blockTensor (fun i => (τ i).representation))),
    ∀ i, σ i ≅ τ i := by
  letI := T.topology
  intro σ τ hσ hτ E
  let : ∀ i, Nontrivial (σ i) := fun i =>
    CuspidalSupport.nontrivial_of_isIrreducible (σ i).representation (hρ := hσ i)
  intro i
  have he : Nonempty ((σ i).representation.Equiv (τ i).representation) := by
    refine CuspidalSupport.nonempty_equiv_of_factor_actions
      (V := fun j => σ j) (W := fun j => τ j)
      (hρ := hσ i) (hσ := hτ i) ?_ ?_
      (CuspidalSupport.equivComp E
        (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) F.Carrier) i))
    · intro g v
      exact CuspidalSupport.external_mulSingle_tprod
        (fun j => (σ j).representation) i g v
    · intro g v
      exact CuspidalSupport.external_mulSingle_tprod
        (fun j => (τ j).representation) i g v
  exact SmoothRep.mkIso (Classical.choice he)

end PadicField.TopologicalData
end Langlands
