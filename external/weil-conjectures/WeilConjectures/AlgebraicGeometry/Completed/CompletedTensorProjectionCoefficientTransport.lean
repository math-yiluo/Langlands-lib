/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus
import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientTensorTransport
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-! # Transport of projection arrows through coefficient isomorphisms

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem projection_mate_formula
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (H : B ⥤ A) (adj : L ⊣ H)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (K : B) (Q : A) :
    derivedProjectionFormulaMate L H adj TR TS alpha K Q =
      adj.homEquiv _ _ (alpha.hom.app (H.obj K, Q) ≫
        TS.map (Prod.mkHom (adj.counit.app K) (𝟙 (L.obj Q)))) := by
  simp [derivedProjectionFormulaMate, Adjunction.rightAdjointProjectionMap]

/-- Adjunction compatibility and tensor compatibility transport the projection mate.
Source: Stacks Tag 0B56, transposition of the tensor/counit composite. -/
private theorem coefficientProjectionMate_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (L : A ⥤ B) (H : B ⥤ A) (adj : L ⊣ H)
    (L' : A ⥤ C) (H' : C ⥤ A) (adj' : L' ⊣ H') (U : C ⥤ B)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B) (TS' : C × C ⥤ C)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS)
    (alpha' : TR ⋙ L' ≅ (L'.prod L') ⋙ TS')
    (b : L' ⋙ U ≅ L) (q : H' ≅ U ⋙ H)
    (rho : (U.prod U) ⋙ TS ≅ TS' ⋙ U)
    (hAdj : ∀ (M : A) (N : C) (t : L'.obj M ⟶ N),
      adj.homEquiv _ _ (b.inv.app M ≫ U.map t) =
        adj'.homEquiv _ _ t ≫ q.hom.app N)
    (hTensor : ∀ F G : A,
      b.hom.app (TR.obj (F, G)) ≫ alpha.hom.app (F, G) =
        U.map (alpha'.hom.app (F, G)) ≫ rho.inv.app (L'.obj F, L'.obj G) ≫
          TS.map (Prod.mkHom (b.hom.app F) (b.hom.app G)))
    (K : C) (Q : A) :
    TR.map (Prod.mkHom (q.hom.app K) (𝟙 Q)) ≫
        derivedProjectionFormulaMate L H adj TR TS alpha (U.obj K) Q ≫
        H.map (TS.map (Prod.mkHom (𝟙 (U.obj K)) (b.inv.app Q)) ≫
          rho.hom.app (K, L'.obj Q)) =
      derivedProjectionFormulaMate L' H' adj' TR TS' alpha' K Q ≫
        q.hom.app (TS'.obj (K, L'.obj Q)) := by
  have hc : L.map (q.hom.app K) ≫ adj.counit.app (U.obj K) =
      b.inv.app (H'.obj K) ≫ U.map (adj'.counit.app K) := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left]
    erw [hAdj (H'.obj K) K (adj'.counit.app K)]
    simp only [Functor.id_obj, Functor.comp_obj, ← Adjunction.homEquiv_symm_id,
      Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]
  have ha : alpha.hom.app (H'.obj K, Q) =
      b.inv.app (TR.obj (H'.obj K, Q)) ≫
        U.map (alpha'.hom.app (H'.obj K, Q)) ≫
        rho.inv.app (L'.obj (H'.obj K), L'.obj Q) ≫
        TS.map (Prod.mkHom (b.hom.app (H'.obj K)) (b.hom.app Q)) := by
    have h := congrArg (fun v ↦ b.inv.app (TR.obj (H'.obj K, Q)) ≫ v)
      (hTensor (H'.obj K) Q)
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h
  have hn := alpha.hom.naturality (Prod.mkHom (q.hom.app K) (𝟙 Q))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  have hr := rho.hom.naturality (Prod.mkHom (adj'.counit.app K) (𝟙 (L'.obj Q)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hr
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_id] at hn hr
  rw [projection_mate_formula, projection_mate_formula]
  erw [← hAdj (TR.obj (H'.obj K, Q)) (TS'.obj (K, L'.obj Q))
    (alpha'.hom.app (H'.obj K, Q) ≫
      TS'.map (Prod.mkHom (adj'.counit.app K) (𝟙 (L'.obj Q))))]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, prod_comp, Prod.mkHom,
    Category.id_comp, Category.comp_id]
  rw [hc, ha]
  simp only [Category.assoc, ← Functor.map_comp_assoc, prod_comp, Prod.mkHom,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.comp_obj]
  rw [hr]
  simp only [Iso.inv_hom_id_app_assoc, ← U.map_comp]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The matching direct-image comparison, with identity restriction on the base removed.
Source: Stacks Tags 0D6E and 07A6. -/
private def pushforward :
    proEtaleRingDerivedDirectImage f R S c ≅ pbcDerivedRestrict c.hom ⋙
      proEtaleRingDerivedDirectImage f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft _ (identityRestriction R).symm ≪≫
    proEtaleRingRestrictionDerivedDirectImage f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp)

/-- Removing identity restriction preserves the adjunction compatibility equation.
Source: Stacks Tag 07A6. -/
private theorem adjunction (M : DerivedCategory (proEtaleRingModules Y R))
    (N : DerivedCategory (proEtaleRingModules X S))
    (t : (proEtaleRingDerivedPullback f R S c).obj M ⟶ N) :
    (proEtaleRingDerivedAdjunction f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)).homEquiv _ _
      ((pullback f R S c).inv.app M ≫ (pbcDerivedRestrict c.hom).map t) =
    (proEtaleRingDerivedAdjunction f R S c).homEquiv _ _ t ≫
      (pushforward f R S c).hom.app N := by
  have h := (proEtaleRingSheafChangeAdjunction f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp)).2.2 M N t
  dsimp only [pullback, pushforward, Iso.trans_inv, Iso.trans_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    isoWhiskerRight_inv, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp] at ⊢
  simp only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.assoc]
  erw [Adjunction.homEquiv_naturality_left, h]
  have hn := (identityRestriction R).inv.naturality
    ((proEtaleRingDerivedAdjunction f R S c).homEquiv _ _ t)
  dsimp only [Functor.id_map] at hn
  erw [← Category.assoc, ← hn, Category.assoc]

end AlgebraicGeometry.Scheme.CoefficientTensorTransport

namespace AlgebraicGeometry.Scheme

/-- The native derived tensor with its flat K-flat representative comparison.
Source: Stacks Tags 06YT and 0FPT. -/
@[irreducible] private def coefficientTensorModel (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) : ProEtaleTensorModel W R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology W) R)
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology W) R P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      (ProEt.topology W) R _ _ _ _ _ _ f.1.hom f.2.hom)

/-- Changing from literal inverse-image coefficients to the canonically identified
completed coefficients transports the specified tensor projection arrow.
This concerns only tensor, geometric pullback and direct image. There are no scalar
extension functors or scalar mates in this statement. The isomorphism r transports
an arbitrary coefficient object; neither it nor K need be perfect.

Source: Stacks Project, sites-cohomology.tex, equation-projection-formula-map
(Tag 0B56), and the adjunction comparison of Tag 07A6; blueprint order 1275.
(blueprint: lem-pbc-completed-tensor-projection-coefficient-transport).

Proof: restriction along the coefficient isomorphism c_f is an exact equivalence
of module categories, with inverse restriction along c_f inverse. Its unit and
counit are the identity on sections. Transport the flat K-flat representative
class and the signed total tensor through this equivalence. The resulting
bifunctor and representative comparison give aX. The canonical restriction/direct
image comparison identifies pushforward of the restricted K with the completed
pushforward of K. Tensor this identification with r to obtain s. Restriction
commutes with pullback by the action square; combine this with the transported
tensor and direct-image comparisons to obtain t. On each pair of flat K-flat
representatives the pullback/tensor comparisons agree on every pure tensor and
hence on all sections after sheafification. Their localizations therefore agree.
The coefficient-change adjunction theorem identifies the transported counit with
the original counit. Transpose the defining tensor-comparison/counit composite:
naturality of the Hom equivalence gives exactly the asserted equation. The same
formulas apply to the zero coefficient object, zero ring and empty site. -/
theorem completedTensorProjectionCoefficientTransport
    {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (aY : ProEtaleTensorModel Y (PerfectProjection.ring d Y))
    (z : ProEtaleTensorModel X
      (DerivedScalarMate.inverseRing f (PerfectProjection.ring d Y)))
    (K : PerfectProjection.derived d X)
    (Q P : PerfectProjection.derived d Y) (r : Q ≅ P) :
    ∃ (aX : ProEtaleTensorModel X (PerfectProjection.ring d X))
      (s : aY.tensor.obj
          ((DerivedScalarMate.push f (PerfectProjection.ring d Y)).obj
            ((pbcDerivedRestrict (PerfectProjection.coefficients d f).hom).obj K), Q) ≅
        aY.tensor.obj ((PerfectProjection.directImage d f).obj K, P))
      (t : (DerivedScalarMate.push f (PerfectProjection.ring d Y)).obj
          (z.tensor.obj ((pbcDerivedRestrict (PerfectProjection.coefficients d f).hom).obj K,
            (DerivedScalarMate.pull f (PerfectProjection.ring d Y)).obj Q)) ≅
        (PerfectProjection.directImage d f).obj
          (aX.tensor.obj (K, (PerfectProjection.pullback d f).obj P))),
      proEtaleProjectionFormulaMate f (PerfectProjection.ring d Y)
          (DerivedScalarMate.inverseRing f (PerfectProjection.ring d Y))
          (Iso.refl _) aY z
          ((pbcDerivedRestrict (PerfectProjection.coefficients d f).hom).obj K) Q ≫ t.hom =
        s.hom ≫ PerfectProjection.projection d f aY aX K P := by
  let R := PerfectProjection.ring d Y
  let S := PerfectProjection.ring d X
  let c := PerfectProjection.coefficients d f
  let U := pbcDerivedRestrict c.hom
  let L := DerivedScalarMate.pull f R
  let H := DerivedScalarMate.push f R
  let L' := PerfectProjection.pullback d f
  let H' := PerfectProjection.directImage d f
  let b := CoefficientTensorTransport.pullback f R S c
  let q := CoefficientTensorTransport.pushforward f R S c
  let aX := coefficientTensorModel X S
  obtain ⟨rho, hTensor⟩ := CoefficientTensorTransport.tensorComparison_compatibility f R S c aY z aX
  let s0 := aY.tensor.mapIso ((q.app K).symm.prod (Iso.refl Q))
  let t0 := H.mapIso
    (z.tensor.mapIso ((Iso.refl (U.obj K)).prod (b.app Q).symm) ≪≫
      rho.app (K, L'.obj Q)) ≪≫ (q.app (aX.tensor.obj (K, L'.obj Q))).symm
  have hg := coefficientProjectionMate_transport L H (DerivedScalarMate.adjunction f R)
    L' H' (proEtaleRingDerivedAdjunction f R S c) U aY.tensor z.tensor aX.tensor
    (proEtaleCanonicalTensorComparison f R (DerivedScalarMate.inverseRing f R)
      (Iso.refl _) aY z)
    (proEtaleCanonicalTensorComparison f R S c aY aX) b q rho
    (CoefficientTensorTransport.adjunction f R S c) hTensor K Q
  have h0 : proEtaleProjectionFormulaMate f R (DerivedScalarMate.inverseRing f R)
        (Iso.refl _) aY z (U.obj K) Q ≫ t0.hom =
      s0.hom ≫ PerfectProjection.projection d f aY aX K Q := by
    apply (cancel_epi s0.inv).1
    apply (cancel_mono (q.hom.app (aX.tensor.obj (K, L'.obj Q)))).1
    have ht : t0.hom ≫ q.hom.app (aX.tensor.obj (K, L'.obj Q)) =
        H.map (z.tensor.map (Prod.mkHom (𝟙 (U.obj K)) (b.inv.app Q)) ≫
          rho.hom.app (K, L'.obj Q)) := by
      change (H.map _ ≫ q.inv.app _) ≫ q.hom.app _ = _
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      rfl
    simp only [Category.assoc, ht, s0.inv_hom_id_assoc]
    exact hg
  let s := s0 ≪≫ aY.tensor.mapIso ((Iso.refl (H'.obj K)).prod r)
  let t := t0 ≪≫ H'.mapIso
    (aX.tensor.mapIso ((Iso.refl K).prod (L'.mapIso r)))
  have hn := (((proEtaleRingDerivedAdjunction f R S c).rightAdjointProjectionMap
    (T_C := Functor.curry.obj aX.tensor) (T_D := Functor.curry.obj aY.tensor)
    (Functor.curry.map (proEtaleCanonicalTensorComparison f R S c aY aX).hom ≫
      (Functor.curryObjProdComp L' L' aX.tensor).hom)).app K).naturality r.hom
  change aY.tensor.map (Prod.mkHom (𝟙 (H'.obj K)) r.hom) ≫
      PerfectProjection.projection d f aY aX K P =
    PerfectProjection.projection d f aY aX K Q ≫
      H'.map (aX.tensor.map (Prod.mkHom (𝟙 K) (L'.map r.hom))) at hn
  refine ⟨aX, s, t, ?_⟩
  change _ ≫ (t0.hom ≫
      H'.map (aX.tensor.map (Prod.mkHom (𝟙 K) (L'.map r.hom)))) =
    (s0.hom ≫ aY.tensor.map (Prod.mkHom (𝟙 (H'.obj K)) r.hom)) ≫ _
  rw [← Category.assoc, h0, Category.assoc, ← hn, ← Category.assoc]

end AlgebraicGeometry.Scheme
