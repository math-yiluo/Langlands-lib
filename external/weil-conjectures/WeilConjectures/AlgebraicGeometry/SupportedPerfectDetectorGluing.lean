/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SupportedDetectorOpenLift
import WeilConjectures.AlgebraicGeometry.SupportedKoszulUnitSummand

/-! # Gluing supported perfect zero detectors

Source: Stacks Project, Tag 0A9A, induction step.
(blueprint: lem-pc-supported-perfect-detector-gluing).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The supported Koszul gluing step for a finite affine cover with at least two members.
The hypothesis supplies zero detectors only for schemes with strictly smaller covers.
Source: Stacks Project, Tag 0A9A, the open-cover induction paragraphs.
(blueprint: lem-pc-supported-perfect-detector-gluing).

Proof:
1. Choose a member V of s and put U equal to the union of the remaining members.
   The latter give an affine cover of U with at most card(s)-1 members: restrict the
   remaining charts, each already contained in U. Thus the induction hypothesis applies
   to U and T intersect U. U is quasi-compact and quasi-separated; its complement of T
   is quasi-compact by quasi-separatedness of X. Restriction and the module equivalence
   for an open subscheme supply derived localizations in the same Hom universe. Apply
   the hypothesis to these localizations, obtaining a perfect supported detector P on U.
2. Apply exists_perfect_supported_map_lift to P, the zero quasi-coherent object on X,
   and the zero map. It gives a perfect Q supported on T with P a retract of Q restricted
   to U. No global detection property is assumed in this step.
3. Put Z = X minus U and W = V minus (Z intersect T). This open is the union of U
   intersect V and V minus T, hence quasi-compact. Choose a finite tuple cutting out
   Z intersect T on the affine V and form its Koszul complex K. It is perfect and
   supported on Z intersect T. supported_open_pushforward identifies K' = Ri_*K
   with extension by zero and makes it perfect and supported on T. Form Q plus K'.
4. If all shifted maps from this sum to a supported object E vanish, they vanish from
   each summand. Exact extension-by-zero adjunction gives orthogonality to K on V.
   koszul_open_orthogonality makes E restricted to V the pushforward from W.
5. On W the support is T intersect U intersect V, closed in W and contained in U
   intersect V. supported_open_pushforward and derived direct-image composition
   identify this pushforward with that from U intersect V. Open restriction base change
   then shows the canonical unit E to Rj_*(E restricted to U) is invertible on U and V.
   Its cone has zero cohomology stalks on this cover, hence is zero globally.
6. Derived adjunction and the retract P of Q restricted to U give vanishing of every
   shifted Hom from P to E restricted to U. The detector P makes this restriction zero,
   and step 5 makes E zero. The finite sum Q plus K' is perfect, quasi-coherent and
   supported on T, so it is the claimed detector. Empty U and redundant affine charts
   are allowed; the strictly smaller cover condition remains valid. -/
theorem supported_perfect_detector_gluing
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
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  obtain ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, hdetect⟩ :=
    exists_supported_detector_open_lift X s hcover hcard ih T hT hTc
  obtain ⟨E, hE, hET, ⟨r⟩, hunit⟩ :=
    exists_supported_koszul_unit_summand X T hT hTc U V hU hUV R adj Q hQ hQT
  refine ⟨E, hE, hET, ?_⟩
  intro K hKT hHom
  refine hdetect K hKT (hunit K hKT hHom) ?_
  intro n
  let rn := r.map (shiftFunctor (schemeDerivedCategory X) n)
  refine ⟨fun f g ↦ ?_⟩
  have hfg : rn.r ≫ f = rn.r ≫ g := (hHom n).elim _ _
  have h := congrArg (fun k ↦ rn.i ≫ k) hfg
  simpa only [← Category.assoc, rn.retract, Category.id_comp] using h

end AlgebraicGeometry
