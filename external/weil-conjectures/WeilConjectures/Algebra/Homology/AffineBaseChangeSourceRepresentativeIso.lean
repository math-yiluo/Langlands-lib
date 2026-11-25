/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality

/-! # Independence of the source-only stalk comparison from its representative

Source: Stacks Project, Tags 06Y6, 08IB and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-base-change-source-representative-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem exists_stalkCohomologyComparison (Y : Scheme.{u}) (p : Y) (i : ℤ) :
    ∃ δ : SingleComplexBaseChange.comparisonStalkCohomology Y p i ≅
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i ⋙
            RingedSpace.moduleStalkFunctor Y.toRingedSpace p,
      ∀ P, δ.hom.app (DerivedCategory.Q.obj P) =
        (SingleComplexBaseChange.comparisonStalkHomologyIso Y p P i).hom ≫
          (affineRepresentativeStalkIso Y p P i).inv := by
  let F := SingleComplexBaseChange.comparisonStalkCohomology Y p i
  let G := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i ⋙
      RingedSpace.moduleStalkFunctor Y.toRingedSpace p
  let ε : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    NatIso.ofComponents (fun P ↦
      SingleComplexBaseChange.comparisonStalkHomologyIso Y p P i ≪≫
        (affineRepresentativeStalkIso Y p P i).symm) (by
      intro P N a
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.comp_map]
      apply (cancel_mono (affineRepresentativeStalkIso Y p N i).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [G, Functor.comp_map]
      rw [affineRepresentativeStalkIso_naturality Y p a i]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact SingleComplexBaseChange.comparisonStalkHomologyIso_naturality Y p a i)
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  refine ⟨Localization.liftNatIso DerivedCategory.Q W
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G ε, ?_⟩
  intro P
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rfl

-- The original 200000 budget times out at the final equivalence construction in 13s.
/-- The source-only comparison is unchanged under K-flat representative change.
Source: Stacks Project, Tags 06Y6, 08IB and perfect.tex, equation-bc before Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-source-representative-iso).

Proof: the exact stalk functor sends eQ followed by eP inverse to an isomorphism
between the derived stalk complexes. The universal derived extension functors
of the baseDerivedTensorCohomologyModel are uniquely isomorphic through their
counits. Apply their cohomology functors to this isomorphism. The cohomologyIso_smul
equations show that it respects both commuting scalar actions, hence the tensor
algebra action. Extend to the fourth stalk ring and forget scalars to obtain t.
Naturality of the universal counit makes the comparison_eq squares commute;
transposition through the extension/restriction adjunction and localized_eq gives
the same equation for localizedComparison. Naturality of tensorStalkIso and of
the exact representative/stalk comparison identifies the target with the stalk
of H(Lg'^*K). Finally cancel the invertible pullback counits and use their
naturality with eQ and eP. The resulting equation is the one displayed here.
No termwise quasi-coherence is assumed, and this argument applies on arbitrary
schemes, to zero complexes and in every integer degree. -/
theorem exists_affineBaseChangeIntoPullback_representativeIso
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ K)
    (hcP : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))) (p : X') (i : ℤ) :
    ∃ t : (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i)).left ≃+
        (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i)).left,
      ∀ x, affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i x =
        affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i (t x) := by
  let := SingleComplexBaseChange.leftAlgebra f g' p
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  let a := eQ ≪≫ eP.symm
  obtain ⟨e, he, _⟩ := SingleComplexBaseChange.exists_comparisonSourceIso
    f f' g g' sq p Q P a i
  have hn := SingleComplexBaseChange.comparisonIntoPullback_naturality
    f f' g g' sq p Q P hQ hP hcQ hcP a i e he
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (SingleComplexBaseChange.R f g' p)
      (SingleComplexBaseChange.A g' p) (SingleComplexBaseChange.B f' p))
        (SingleComplexBaseChange.C p))
  obtain ⟨δ, hδ⟩ := exists_stalkCohomologyComparison X' p i
  let F := SingleComplexBaseChange.comparisonStalkCohomology X' p i
  let G := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i ⋙
      RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  have hnormal (N : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (eN : DerivedCategory.Q.obj N ≅ K)
      (hcN : IsIso ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj N))) :
      affineBaseChangeIntoPullback f f' g g' sq K N eN hcN p i =
        SingleComplexBaseChange.comparisonIntoPullback f f' g g' sq p N hcN i ≫
          F.map ((derivedPullback g').map eN.hom) ≫
            δ.hom.app ((derivedPullback g').obj K) := by
    have := hcN
    let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj N
    have hd := δ.hom.naturality
      (inv ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          (derivedPullback g').map eN.hom)
    change F.map _ ≫ δ.hom.app _ = δ.hom.app (DerivedCategory.Q.obj T) ≫ G.map _ at hd
    rw [hδ T] at hd
    have hd' := congrArg (fun b ↦
      (SingleComplexBaseChange.comparisonStalkHomologyIso X' p T i).inv ≫ b) hd
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc] at hd'
    let : HasDerivedCategory.{w} X'.Modules :=
      inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace)))
    have htransport :
        (DerivedCategory.quotientCompQhIso.{w} _).inv.app T ≫
          inv ((SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          (derivedPullback g').map ((DerivedCategory.quotientCompQhIso _).hom.app N ≫ eN.hom) =
        inv ((SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          (derivedPullback g').map eN.hom := by
      simp only [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso,
        Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
      repeat erw [Category.id_comp]
    dsimp only [affineBaseChangeIntoPullback]
    erw [htransport]
    simpa only [SingleComplexBaseChange.comparisonIntoPullback, F, G, T, cast_eq,
      Functor.comp_map, Functor.map_comp, Category.assoc] using
        congrArg (fun b ↦
          (SingleComplexBaseChange.cohomologyModel f f' g g' sq p N).localizedComparison i ≫
            HomologicalComplex.homologyMap
              (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p N).hom i ≫ b) hd'.symm
  have ha : (derivedPullback g').map a.hom ≫ (derivedPullback g').map eP.hom =
      (derivedPullback g').map eQ.hom := by
    rw [← Functor.map_comp]
    simp [a]
  have hsq : affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i =
      E.map e.hom ≫ affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i := by
    rw [hnormal Q eQ hcQ, hnormal P eP hcP]
    have hh := congrArg (fun b ↦ b ≫ F.map ((derivedPullback g').map eP.hom) ≫
      δ.hom.app ((derivedPullback g').obj K)) hn
    simp only [Category.assoc] at hh ⊢
    change _ ≫ F.map ((derivedPullback g').map a.hom) ≫
      F.map ((derivedPullback g').map eP.hom) ≫ _ = _ at hh
    rw [← Functor.map_comp_assoc, ha] at hh
    exact hh
  refine ⟨(CategoryTheory.Iso.toLinearEquiv (E.mapIso e)).toAddEquiv, ?_⟩
  intro x
  exact congrArg (fun b ↦ b x) hsq

end AlgebraicGeometry
