/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedDetectorOpenLiftCore

/-! # Lifting the detector from the smaller open

Source: Stacks Project, Tag 0A9A.
(blueprint: lem-pc-supported-detector-open-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The lift of the smaller-cover detector detects supported objects whose open unit
is invertible; it need not detect arbitrary supported objects on X.
Source: Stacks Project, Tag 0A9A, induction and final adjunction paragraphs.
(blueprint: lem-pc-supported-detector-open-lift).

Proof:
1. Remove one affine chart V from s and take U to be the union of the others. Restrict
   those charts to U to obtain a strictly smaller affine cover. Finite unions of affine
   opens are compact; quasi-separatedness makes U and U minus T quasi-compact.
2. Transport the derived localizations across the canonical module equivalence for U
   and its opens. Apply ih to the smaller cover and the inverse image of T to obtain P.
3. Lift the zero map P to zero using exists_perfect_supported_map_lift. Its global
   source Q is perfect, supported on T, and P is a retract of Q restricted to U.
   Perfect complexes have quasi-coherent cohomology, so Q lies in D_QCoh(X).
4. Take a right adjoint R of exact derived restriction L (unbounded open direct image).
   For supported K with invertible unit, adjunction identifies Hom(Q[n], K) with
   Hom(L(Q[n]), L(K)). Exact restriction commutes with shifts. The retract P of L(Q)
   therefore gives vanishing of Hom(P[n], L(K)). Restriction preserves quasi-coherence
   and support. The detector P gives L(K) zero, and the invertible unit K to R(L(K))
   makes K zero: the inverse hom equivalence makes the unit zero, and cancellation
   against this invertible unit gives the identity of K equal to zero.
   Redundant charts and empty U are allowed; the smaller-cover bound still holds. -/
theorem exists_supported_detector_open_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (s : Finset X.affineOpens) (hcover : (⨆ U ∈ s, (U : X.Opens)) = ⊤)
    (hcard : 2 ≤ s.card)
    (ih : ∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ U : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
      (t : Finset Y.affineOpens), t.card < s.card →
      (⨆ U ∈ t, (U : Y.Opens)) = ⊤ →
      ∀ (S : Set Y), IsClosed S → IsCompact Sᶜ →
        ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
          (∀ (n : ℤ) (x : Y), x ∉ S →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
          ∀ K : schemeDerivedQCohCategory Y,
            (∀ (n : ℤ) (x : Y), x ∉ S →
              Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
            (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ (U : X.Opens) (V : X.affineOpens), IsCompact (U : Set X) ∧
      U ⊔ (V : X.Opens) = ⊤ ∧
      ∃ (R : DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
          schemeDerivedCategory X)
        (adj : (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
        (Q : schemeDerivedQCohCategory X),
        Scheme.IsPerfect X Q.obj ∧
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj Q.obj).val.presheaf x))) ∧
        ∀ K : schemeDerivedQCohCategory X,
          (∀ (n : ℤ) (x : X), x ∉ T →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
          IsIso (adj.unit.app K.obj) →
          (∀ n : ℤ, Subsingleton (Q.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  obtain ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, hdetect⟩ :=
    exists_supported_detector_open_lift_core X s hcover hcard ih T hT hTc
  refine ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, ?_⟩
  intro K hKT hUnit hHom
  let : IsIso (adj.unit.app K.obj) := hUnit
  have hres := hdetect K hKT (fun n ↦ ?_)
  · apply (IsZero.iff_id_eq_zero K.obj).mpr
    apply (cancel_mono (adj.unit.app K.obj)).mp
    have heq : adj.unit.app K.obj = 0 := by
      apply (adj.homEquiv K.obj _).symm.injective
      exact hres.eq_of_src _ _
    simp [heq]
  · refine ⟨fun f g ↦ ?_⟩
    apply (adj.homEquiv _ _).injective
    apply (cancel_mono (inv (adj.unit.app K.obj))).mp
    exact (hHom n).elim _ _

end AlgebraicGeometry
