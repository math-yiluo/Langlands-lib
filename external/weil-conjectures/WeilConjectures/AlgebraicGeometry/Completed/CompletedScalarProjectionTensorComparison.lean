/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.CompletedProjection.CompletedScalarMateCoefficientTransport
import WeilConjectures.AlgebraicGeometry.Completed.CompletedTensorProjectionCoefficientTransport
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-!
# Comparing scalar reduction with the tensor projection morphism

Source: blueprint, proper base change, order 1276, finite-level projection formula;
Stacks Project, Tags 0B56 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def comparisonTensorModel (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) : ProEtaleTensorModel T R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) R P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun v ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      (ProEt.topology T) R _ _ _ _ _ _ v.1.hom v.2.hom)

/-- After forgetting the target coefficient action and transporting the completed ring
along its canonical constant-system comparison, the scalar-adjunction mate is the
ordinary tensor projection morphism. This statement concerns the specified arrows;
it asserts no invertibility of either projection morphism. The coefficient maps
φY and φX are arbitrary compatible maps, and P is their restricted target ring;
no finiteness, flatness or perfectness is assumed for these target rings.
The ordinary direct-image presentations F and G are identified with the canonical
ringed functors by hF and hG; deriving these exact presentations avoids unfolding
the chosen localization constructions when applying the comparison.

Source: blueprint order 1276, finite-level projection formula, and order 1275,
identification of quotient tensors; Stacks Project, Tags 0B56 and 06YY.
(blueprint: lem-pbc-completed-scalar-projection-tensor-comparison).

Proof: identify the constant and continuous-function quotient ring systems using
pbcConstantSystemComparison. Its limit comparison identifies completed rings, and
its projection equations identify the transported target-module actions. Resolve an input
by flat K-flat complexes. Extension followed by restriction is tensor with the
restricted quotient ring: on sections the comparison sends s tensor m to m tensor s.
The same construction at X and Y descends to the two tensor models and the source
and target isomorphisms below. Restriction commutes with direct image through the
section-normalized comparison. Its derived comparison is fixed by the universal
right-derived units, so this comparison agrees with the given e.
Transpose the displayed scalar projection using pbcDerivedScalarAdjunction: its
transpose is direct image of m mapping to 1 tensor m, followed by this restriction
comparison. Under the tensor identifications this is the transpose of the tensor
projection, namely the tensor pullback comparison followed by counit tensor identity.
The tensor-unit normalization and the adjunction triangle identity identify them
on K-flat representatives. Localization and the derived-unit normalization extend
the equality to arbitrary unbounded inputs. No perfectness argument is used to
infer invertibility here; that is a separate application of the perfect projection
formula. The zero quotient and the empty site use the same tensor/unit equations. -/
theorem completedScalarProjectionTensorComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) [IsIso (completedCoefficientMap f d)]
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φY : pbcAdicCompletion Y d ⟶ SY) (φX : pbcAdicCompletion X d ⟶ SX)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (hc : completedCoefficientMap f d ≫ φX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫ c.hom)
    (F : pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d))
    [F.Additive]
    (hF : F = proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d)))
    (G : pbcModules X SX ⥤ pbcModules Y SY) [G.Additive]
    (hG : G = proEtaleRingModuleDirectImage f SY SX c)
    (i : pbcRestrict φX ⋙ F ≅
      G ⋙ pbcRestrict φY)
    (hi : ∀ (M : pbcModules X SX) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (i.hom.app M).val.app U x)
        (fun x : ((proEtaleRingModuleDirectImage f SY SX c).obj M).val.obj U ↦ x))
    (e : pbcDerivedRestrict φX ⋙ F.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ pbcDerivedRestrict φY)
    (he : ∀ C : CochainComplex (pbcModules X SX) ℤ,
      F.rightDerivedFunctorUnitQ
          (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).obj C) ≫
        F.rightDerivedFunctor.map
          ((pbcRestrict φX).mapDerivedCategoryFactors.inv.app C) ≫
        e.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex i.hom (.up ℤ)).app C) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        (pbcDerivedRestrict φY).map (G.rightDerivedFunctorUnitQ C))
    (P : PerfectProjection.derived d Y)
    (r : (DerivedCategory.singleFunctor (PerfectProjection.modules d Y) 0).obj
        ((pbcRestrict ((pbcCompletedComparison Y d).hom ≫ φY)).obj
          (SheafOfModules.unit (reductionModuleRing Y SY))) ≅ P)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    ∃ (aY : ProEtaleTensorModel Y (PerfectProjection.ring d Y))
      (aX : ProEtaleTensorModel X (PerfectProjection.ring d X))
      (s : (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).obj
          ((pbcDerivedRestrict φY).obj
            ((pbcDerivedExtend φY).obj
              (F.rightDerivedFunctor.obj K))) ≅
        aY.tensor.obj
          ((PerfectProjection.directImage d f).obj
            ((pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K), P))
      (t : (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).obj
          ((pbcDerivedRestrict φY).obj
            (G.rightDerivedFunctor.obj
              ((pbcDerivedExtend φX).obj K))) ≅
        (PerfectProjection.directImage d f).obj
          (aX.tensor.obj
            ((pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K,
              (PerfectProjection.pullback d f).obj P))),
      (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).map
          ((pbcDerivedRestrict φY).map
            (((pbcDerivedScalarAdjunction φY).homEquiv _ _).symm
              (F.rightDerivedFunctor.map
                  ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
                e.hom.app ((pbcDerivedExtend φX).obj K)))) ≫ t.hom =
        s.hom ≫ PerfectProjection.projection d f aY aX
          ((pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K) P := by
  let χ := (pbcCompletedComparison Y d).hom ≫ φY
  let K₀ := (pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K
  let Kᵢ := CompletedProjection.inverseObject f d K₀
  let aY := comparisonTensorModel Y (PerfectProjection.ring d Y)
  let z := comparisonTensorModel X
    (DerivedScalarMate.inverseRing f (PerfectProjection.ring d Y))
  obtain ⟨u, v, huv⟩ := completedScalarMateCoefficientTransport
    f d SY SX φY φX c hc F hF G hG i hi e he K
  let s₀ := (DerivedScalarMate.sourceIso f χ aY).app Kᵢ
  let t₀ := (DerivedScalarMate.targetIso f χ z).app Kᵢ
  let Q := DerivedCategory.Q.obj (DerivedScalarMate.coefficientComplex χ)
  have r₀ : Q ≅ P := r
  obtain ⟨aX, s₁, t₁, hπ⟩ := completedTensorProjectionCoefficientTransport
    f d aY z K₀ Q P r₀
  let π := proEtaleProjectionFormulaMate f (PerfectProjection.ring d Y)
    (DerivedScalarMate.inverseRing f (PerfectProjection.ring d Y))
    (Iso.refl _) aY z Kᵢ Q
  let β := (DerivedScalarMate.restriction χ).mapDerivedCategory.map
    ((DerivedScalarMate.beta f χ).app Kᵢ)
  have hn : s₀.inv ≫ β ≫ t₀.hom = π :=
    (DerivedScalarMate.derivedScalarMateThickLocus f χ aY z).1 Kᵢ
  have hn' : β ≫ t₀.hom = s₀.hom ≫ π := by
    rw [← hn]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨aY, aX, u ≪≫ s₀ ≪≫ s₁, v ≪≫ t₀ ≪≫ t₁, ?_⟩
  simp only [Iso.trans_hom, Category.assoc]
  calc
    _ = u.hom ≫ β ≫ t₀.hom ≫ t₁.hom := by
      simpa only [Category.assoc] using
        congrArg (fun w ↦ w ≫ t₀.hom ≫ t₁.hom) huv
    _ = u.hom ≫ s₀.hom ≫ π ≫ t₁.hom := by
      rw [reassoc_of% hn']
    _ = _ := by
      rw [hπ]

end AlgebraicGeometry.Scheme
