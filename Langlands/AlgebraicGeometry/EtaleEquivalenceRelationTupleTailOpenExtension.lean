import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationStratification
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpen
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtensionRecovery
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtensionAffine

/-! # Recovering a finite tuple tail by an open extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- The next invariant threshold in a finite tuple tail. -/
def tupleTailNextOpen (N p : ℕ) : (E.tupleTailPresentation N p).U.Opens :=
  E.tupleChartThresholdOpen
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (p + 1)

theorem tupleTailNextOpen_isInvariant (N p : ℕ) :
    (E.tupleTailPresentation N p).IsInvariantOpen (E.tupleTailNextOpen N p) :=
  (E.tupleChartThresholdOpen_preimage_eq _ (p + 1)).symm

/-- Restriction of the whole tail to the next threshold. -/
def tupleTailNextRelation (N p : ℕ) : EtaleEquivalenceRelation.{u} :=
  (E.tupleTailPresentation N p).chart (E.tupleTailNextOpen N p).ι

theorem tupleTailNextRelation_isCartesianHom (N p : ℕ) :
    IsCartesianHom (E.tupleTailNextRelation N p) (E.tupleTailPresentation N p)
      (E.tupleTailNextOpen N p).ι
      (Chart.map (E.tupleTailPresentation N p) (E.tupleTailNextOpen N p).ι) :=
  (E.tupleTailPresentation N p).isCartesianHom_chart_of_isInvariantOpen _
    (E.tupleTailNextOpen_isInvariant N p)

theorem tupleTailNextComplement_covers (N p : ℕ) :
    ∀ x : (E.tupleTailPresentation N p).U,
      x ∉ Set.range (E.tupleTailNextOpen N p).ι →
        x ∈ Set.range (E.tupleTailNextComplementι N p) := by
  intro x hx
  rw [Scheme.Opens.range_ι] at hx
  rw [E.tupleTailNextComplementι_range N p]
  exact hx

/-- Replace the units of the next-threshold restriction by the whole tail
object scheme. -/
def tupleTailOpenExtension (N p : ℕ) : EtaleEquivalenceRelation.{u} :=
  OpenExtension.relation (E.tupleTailNextRelation N p) (E.tupleTailNextOpen N p).ι

/-- The open-extension pushout recovers the original finite-tail arrows. -/
def tupleTailOpenExtensionArrowsIso (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailOpenExtension N p).R ≅ (E.tupleTailPresentation N p).R :=
  OpenExtension.Recovery.arrowsIso (E.tupleTailNextRelation_isCartesianHom N p)
    (E.tupleTailNextComplementι N p) (E.tupleTailNextComplement_covers N p)
    (E.tupleTailNextComplement_unit_isPullback N p hp)

@[reassoc (attr := simp)]
theorem tupleTailOpenExtensionArrowsIso_hom_t (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailOpenExtensionArrowsIso N p hp).hom ≫ (E.tupleTailPresentation N p).t =
      (E.tupleTailOpenExtension N p).t :=
  OpenExtension.Recovery.toOriginal_t (E.tupleTailNextRelation_isCartesianHom N p)

@[reassoc (attr := simp)]
theorem tupleTailOpenExtensionArrowsIso_hom_s (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailOpenExtensionArrowsIso N p hp).hom ≫ (E.tupleTailPresentation N p).s =
      (E.tupleTailOpenExtension N p).s :=
  OpenExtension.Recovery.toOriginal_s (E.tupleTailNextRelation_isCartesianHom N p)

@[reassoc (attr := simp)]
theorem tupleTailOpenExtensionArrowsIso_inv_t (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailOpenExtensionArrowsIso N p hp).inv ≫ (E.tupleTailOpenExtension N p).t =
      (E.tupleTailPresentation N p).t :=
  OpenExtension.Recovery.arrowsIso_inv_t (E.tupleTailNextRelation_isCartesianHom N p)
    (E.tupleTailNextComplementι N p) (E.tupleTailNextComplement_covers N p)
    (E.tupleTailNextComplement_unit_isPullback N p hp)

@[reassoc (attr := simp)]
theorem tupleTailOpenExtensionArrowsIso_inv_s (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailOpenExtensionArrowsIso N p hp).inv ≫ (E.tupleTailOpenExtension N p).s =
      (E.tupleTailPresentation N p).s :=
  OpenExtension.Recovery.arrowsIso_inv_s (E.tupleTailNextRelation_isCartesianHom N p)
    (E.tupleTailNextComplementι N p) (E.tupleTailNextComplement_covers N p)
    (E.tupleTailNextComplement_unit_isPullback N p hp)

theorem tupleTailOpenExtension_isCartesianHom (N p : ℕ) (hp : p < N + 1) :
    IsCartesianHom (E.tupleTailOpenExtension N p) (E.tupleTailPresentation N p)
      (𝟙 _) (E.tupleTailOpenExtensionArrowsIso N p hp).hom :=
  OpenExtension.Recovery.isCartesianHom (E.tupleTailNextRelation_isCartesianHom N p)
    (E.tupleTailNextComplementι N p) (E.tupleTailNextComplement_covers N p)
    (E.tupleTailNextComplement_unit_isPullback N p hp)

/-- The reverse recovery map is cartesian as well. -/
theorem tupleTailOpenExtension_inv_isCartesianHom (N p : ℕ) (hp : p < N + 1) :
    IsCartesianHom (E.tupleTailPresentation N p) (E.tupleTailOpenExtension N p)
      (𝟙 _) (E.tupleTailOpenExtensionArrowsIso N p hp).inv := by
  refine ⟨by simp, IsPullback.mk' (by simp) ?_ ?_⟩
  · intro T a b hab _
    exact (cancel_mono (E.tupleTailOpenExtensionArrowsIso N p hp).inv).mp hab
  · intro T a b hab
    refine ⟨a ≫ (E.tupleTailOpenExtensionArrowsIso N p hp).hom, ?_, ?_⟩
    · simp
    · simpa using hab

variable (N p : ℕ) (hp : p < N + 1)
  {F : EtaleEquivalenceRelation.{u}} {V : Scheme.{u}}
  (a : (E.tupleTailNextRelation N p).U ⟶ F.U)
  (b : (E.tupleTailNextRelation N p).R ⟶ F.R)
  (h : IsCartesianHom (E.tupleTailNextRelation N p) F a b)
  (κ : F.U ⟶ V) [IsOpenImmersion κ]
  (v : (E.tupleTailPresentation N p).U ⟶ V)
  (hv : IsPullback a (E.tupleTailNextOpen N p).ι κ v)

/-- The actual comparison from a finite tail to a compatible extended level. -/
def tupleTailToOpenExtension :
    (E.tupleTailPresentation N p).R ⟶ (OpenExtension.relation F κ).R :=
  (E.tupleTailOpenExtensionArrowsIso N p hp).inv ≫
    OpenExtension.Comparison.map (E := E.tupleTailNextRelation N p) (F := F)
      (f := a) (g := b) (E.tupleTailNextOpen N p).ι κ v h.1 h.2.w hv.w.symm

include h hv in
theorem tupleTailToOpenExtension_isCartesianHom :
    IsCartesianHom (E.tupleTailPresentation N p) (OpenExtension.relation F κ) v
      (E.tupleTailToOpenExtension N p hp a b h κ v hv) := by
  have H := (E.tupleTailOpenExtension_inv_isCartesianHom N p hp).comp
    (OpenExtension.Comparison.isCartesianHom
      (E := E.tupleTailNextRelation N p) (F := F) (f := a) (g := b)
      (ι := (E.tupleTailNextOpen N p).ι) (κ := κ) (v := v) hv.w.symm h hv)
  simpa only [tupleTailToOpenExtension, Category.id_comp] using H

@[reassoc (attr := simp)]
theorem tupleTailToOpenExtension_t :
    E.tupleTailToOpenExtension N p hp a b h κ v hv ≫ (OpenExtension.relation F κ).t =
      (E.tupleTailPresentation N p).t ≫ v :=
  (E.tupleTailToOpenExtension_isCartesianHom N p hp a b h κ v hv).1

@[reassoc (attr := simp)]
theorem tupleTailToOpenExtension_s :
    E.tupleTailToOpenExtension N p hp a b h κ v hv ≫ (OpenExtension.relation F κ).s =
      (E.tupleTailPresentation N p).s ≫ v :=
  (E.tupleTailToOpenExtension_isCartesianHom N p hp a b h κ v hv).2.w

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
