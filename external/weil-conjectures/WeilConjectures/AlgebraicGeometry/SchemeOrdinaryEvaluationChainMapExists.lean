/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation
/-! # Ordinary evaluation: a step of the chain calculation
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
/-- Ordinary evaluation factors through the single coefficient unit, independently of F.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, steps 1 and 2.
(blueprint: lem-pc-scheme-ordinary-evaluation-chain-map-exists).

Proof: Put O equal to the single unit and V=Hom(P,O). For every total degree n,
extend over the coproduct the maps V^q tensor P^r to O^n, q+r=n, given by
symmetry followed by the inverse tensor-Hom adjunction applied to the chosen
Hom projection. This is an explicit construction, not a choice of data from
an arbitrary existence theorem. Project the Hom differential onto each
Hom(P^r,O^n); the equation is d_O composed with the projection minus (-1)^q
times precomposition by d_P. The additive tensor-Hom adjunction transports
this to the total tensor differential equation, so these maps form a chain
map e. On each summand, naturality of the projections and of uncurrying in
the coefficient morphism eta_O identifies the uncurrying of Hom(P,eta_O)
with the component of e followed by eta_O. Coproduct extensionality gives
its chain-map equality. No boundedness is used; zero complexes and the empty
scheme give the same equations with zero components. -/
theorem schemeOrdinaryEvaluation_chain_map_exists (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
    ∃ e : pullbackTensorTotal Y V P ⟶ O,
      schemeTensorHomUncurry Y V P O phiO = e ≫ eta.app O := by
  classical
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex (R := Y.sheaf) P O
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
  let U := schemeTensorHomUncurry Y V P O phiO
  have hg (n : ℤ) : U.f n = schemeOrdinaryEvaluationGraded Y P O n ≫ (eta.app O).f n :=
    schemeOrdinaryEvaluationGraded_augmentation Y P O (eta.app O) n
  have : Mono (eta.app O) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ O).1
  let e : pullbackTensorTotal Y V P ⟶ O :=
    { f := schemeOrdinaryEvaluationGraded Y P O
      comm' := fun n m _ ↦ by
        apply (cancel_mono ((eta.app O).f m)).1
        have hc := (eta.app O).comm n m
        change (eta.app O).f n ≫ ((schemeHomKInjectiveResolution Y).obj O).d n m =
          O.d n m ≫ (eta.app O).f m at hc
        rw [Category.assoc, ← hc, ← Category.assoc, ← hg n, Category.assoc, ← hg m]
        exact U.comm n m }
  refine ⟨e, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  exact hg n
end AlgebraicGeometry
