/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# Picard pullback as extension of Jacobian points

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
`lem-sc-piczero-torsion-base-change`, steps 1 and 2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The degree-zero Picard comparison is extension of points of one abelian variety.

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
`lem-sc-piczero-torsion-base-change`, steps 1 and 2.
(blueprint: lem-sc-piczero-jacobian-point-comparison)

Proof: over the algebraically closed base, connectedness gives geometric connectedness;
smoothness gives geometric irreducibility and geometric reducedness, hence integrality.
The dimension criterion for an integral smooth scheme gives relative dimension one.
Jacobian representability supplies one commutative group scheme J representing Pic^0,
proper, smooth and geometrically integral, hence an abelian variety. Transport G and G'
to the degree-zero Picard subgroups using their underlying-set equalities. The existing
rational-point comparisons identify these subgroups with Pic^0 at Spec k and Spec k',
and record that the comparisons send a class to its image under the sheafification unit.
For the canonical pullback square, the comparison isomorphism with that pullback is the
identity, so the second comparison sends a class directly to its sheafification. The
tensor-compatible representation turns both comparisons into multiplicative equivalences.
Apply naturality of the representation and of the sheafification unit along Spec k' to
Spec k. Picard functoriality and the first-projection identity for the base-change map
identify the resulting class with the specified pullback hj. This gives the displayed
square without comparing two separately chosen Jacobians. Identity extensions and genus
zero are covered by the same argument.
-/
theorem pic_zero_jacobian_point_comparison
    {k k' : Type u} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f]
    (G : Subgroup X.Pic) (hG : (G : Set X.Pic) = f.picZero)
    (G' : Subgroup (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
    (hG' : (G' : Set (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic) =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).picZero)
    (j : G →* G')
    (hj : ∀ L : G, (j L).val = Scheme.Pic.mapHom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L.val)
    : ∃ (J : Over (Spec (.of k))) (hJ : CommGrpObj J),
      letI := hJ
      ∃ (_ : IsAbelianVariety J) (e : G ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J))
        (e' : G' ≃* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶ J)),
      ∀ x : G, e' (j x) =
        toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ≫ e x := by
  classical
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace X := IsConnectedCurve.connectedSpace (f := f)
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (X ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (X ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let T : Over (Spec (.of k)) := Over.mk b
  let T₀ := 𝟙_ (Over (Spec (.of k)))
  let Y := pullback f b
  let g := pullback.snd f b
  let : Y.Over (Spec (.of k')) := ⟨g⟩
  have : SmoothOfRelativeDimension 1 g := inferInstance
  have : IsProper g := inferInstance
  have : SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k')) :=
    ‹SmoothOfRelativeDimension 1 g›
  have : IsProper (Y ↘ Spec (.of k')) := ‹IsProper g›
  have hG₀ : G = picardZero k X := SetLike.coe_injective
    (hG.trans (Scheme.coe_ker_picDegreeHom (k := k) (C := X)).symm)
  have hG₁ : G' = picardZero k' Y := SetLike.coe_injective
    (hG'.trans (Scheme.coe_ker_picDegreeHom (k := k') (C := Y)).symm)
  let c := MulEquiv.subgroupCongr hG₀
  let c' := MulEquiv.subgroupCongr hG₁
  obtain ⟨J, hJ, r, hP, hS, hI, hr, -⟩ := exists_jacobian (k := k) (X := X)
  change (picardFunctorDegree f 0).obj.RepresentableBy J at r
  change IsPicardZeroMul f r at hr
  let := hJ
  let := hI
  have hA : IsAbelianVariety J :=
    { toIsProper := hP
      toSmooth := SmoothOfRelativeDimension.smooth (Scheme.arithmeticGenus k X) J.hom
      toConnectedSpace := GeometricallyConnected.connectedSpace_of_subsingleton J.hom }
  obtain ⟨Φ₀, hΦ₀⟩ := exists_picardZero_equiv_picardFunctorDegree_zero (k := k) (X := X)
  let sq := IsPullback.of_hasPullback f b
  obtain ⟨Φ₁, hΦ₁, -⟩ := exists_picardZero_equiv_picardFunctorDegree (k₀ := k) (K := k') X Y
    (pullback.fst f b) sq
  have hinv : sq.isoPullback.inv = 𝟙 Y := by
    apply pullback.hom_ext
    · exact sq.isoPullback_inv_fst.trans (Category.id_comp _).symm
    · exact sq.isoPullback_inv_snd.trans (Category.id_comp _).symm
  let Φ : G ≃ (picardFunctorDegree f 0).obj.obj (.op T₀) := c.toEquiv.trans Φ₀
  let Φ' : G' ≃ (picardFunctorDegree f 0).obj.obj (.op T) := c'.toEquiv.trans Φ₁
  have hΦ (L : G) : ∃ h, Φ L =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f 0).toFunctor).app (.op T₀)
          ⟨Scheme.Pic.map (pullback.fst f T₀.hom) L.val, h⟩ := hΦ₀ (c L)
  have hΦ' (L : G') : ∃ h, Φ' L =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨L.val, h⟩ := by
    obtain ⟨h, hh⟩ := hΦ₁ (c' L)
    have hm : Scheme.Pic.map sq.isoPullback.inv (c' L).val = L.val := by
      rw [hinv]
      exact Scheme.Pic.map_id _
    simp only [hm] at h hh
    exact ⟨h, hh⟩
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isPicardZeroMul f r hr (T := T₀)
    (fun L : G ↦ Scheme.Pic.map (pullback.fst f T₀.hom) L.val)
    (fun a b ↦ Scheme.Pic.map_mul _ a.val b.val) Φ hΦ
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isPicardZeroMul f r hr (T := T)
    (fun L : G' ↦ L.val) (fun _ _ ↦ rfl) Φ' hΦ'
  refine ⟨J, hJ, hA, e, e', ?_⟩
  intro x
  rw [he', he]
  apply r.homEquiv.injective
  rw [Equiv.apply_symm_apply, r.homEquiv_comp, Equiv.apply_symm_apply]
  obtain ⟨hx, hΦx⟩ := hΦ x
  obtain ⟨hjx, hΦjx⟩ := hΦ' (j x)
  rw [hΦx, hΦjx]
  have hn := NatTrans.naturality_apply
    (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
      (picardSubfunctorDegree f 0).toFunctor) (toUnit T).op
        ⟨Scheme.Pic.map (pullback.fst f T₀.hom) x.val, hx⟩
  refine Eq.trans ?_ hn
  symm
  congr 1
  apply Subtype.ext
  change Scheme.Pic.map (baseChangeMap f (toUnit T))
    (Scheme.Pic.map (pullback.fst f T₀.hom) x.val) = (j x).val
  rw [← Scheme.Pic.map_comp, hj]
  congr 1
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end AlgebraicGeometry
