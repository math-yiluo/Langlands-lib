/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import WeilConjectures.AlgebraicGeometry.CechComparisonMapNaturality

/-! # Canonical scalar Cech comparison

Source: Stacks Project, Tags 01EQ and 01XD.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A scalar comparison is the canonical module comparison after forgetting scalars.
The two explicit Cech comparisons use the same underlying additive presheaf.
Source: Stacks, Tag 01EQ (blueprint: lem-sc-picard-scalar-cech-comparison). -/
def IsPicardScalarCechComparison
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens)
    (F : X.Modules) (p : ℕ)
    (e : ((picardCechFunctor f U).obj F).homology p →ₗ[k] scalarCohomology f F p) :
    Prop :=
  ∃ c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F,
    IsModuleCechComparison U F p c ∧ ∀ a,
      c ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) p).hom a)) =
          e a

/-- Affine-intersection covers have canonical scalar Cech comparisons.
Source: Stacks, Tags 01EQ, 01XD
(blueprint: lem-sc-picard-scalar-cech-comparison).

Proof: Fix an injective resolution. The beta augmentation is a quasi-isomorphism
by affine acyclicity, and alpha is a quasi-isomorphism by the sheaf gluing theorem.
Compose H(beta), inverse H(alpha), and the inverse resolution identification.
This is the canonical module comparison, independent of the chosen resolution.
Use the explicit additive Cech identifications to compare the scalar Cech complex
with the ordinary module Cech complex. Multiplication by r in k is multiplication
by scalarMap(f,top)(r) on the latter: sectionwise this is functoriality of the
structure sheaf and restriction of scalars. Naturality of the explicit Cech
homology identification for scalar multiplication therefore makes the resulting
additive isomorphism k-linear. Its inverse is linear as well, giving e and the
stated canonical-comparison equation. No finiteness is required; empty covers
of the empty scheme and zero coefficients give zero complexes. -/
theorem picardScalarCechComparison_exists
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ∃ e : ((picardCechFunctor f U).obj F).homology p ≃ₗ[k] scalarCohomology f F p,
      IsPicardScalarCechComparison f U F p e := by
  classical
  obtain ⟨c, hc⟩ := ((cechComparisonMapNaturality X U hcover).2 p).1 F
  have : IsIso c := moduleCechComparison_isIso_of_affine X U hU hcover F p c hc
  let S := TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) p
  let M := TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p
  have hmul (r : k) :
      Functor.whiskerRight (r • 𝟙 (scalarPresheaf f F))
          (forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}) =
        Functor.whiskerRight ((scalarMap f ⊤ r) • 𝟙 F.presheafModuleCat)
          (forget₂ (ModuleCat.{w} Γ(X, ⊤)) AddCommGrpCat.{w}) := by
    ext Q x
    change (scalarMap f Q.unop r) • (show F.val.obj Q from x) =
      (X.presheaf.map (homOfLE le_top : Q.unop ⟶ ⊤).op).hom
        (scalarMap f ⊤ r) • (show F.val.obj Q from x)
    congr 1
    simp [scalarMap]
  have hlinear (r : k) (x : ((picardCechFunctor f U).obj F).homology p) :
      M.inv (S.hom (r • x)) = (scalarMap f ⊤ r) •
        (show ((cechComplexFunctor U).obj F.presheafModuleCat).homology p from
          M.inv (S.hom x)) := by
    apply (ConcreteCategory.bijective_of_isIso M.hom).1
    rw [Iso.inv_hom_id_apply]
    rw [show M.hom ((scalarMap f ⊤ r) •
        (show ((cechComplexFunctor U).obj F.presheafModuleCat).homology p from
          M.inv (S.hom x))) =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (Functor.whiskerRight ((scalarMap f ⊤ r) • 𝟙 F.presheafModuleCat)
          (forget₂ (ModuleCat.{w} Γ(X, ⊤)) AddCommGrpCat.{w}))) p
        (M.hom (M.inv (S.hom x))) from
      TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_smul U F.presheafModuleCat p
        (scalarMap f ⊤ r) (M.inv (S.hom x))]
    rw [Iso.inv_hom_id_apply]
    exact (TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_smul U
      (scalarPresheaf f F) p r x).trans (by rw [hmul]; rfl)
  let e : ((picardCechFunctor f U).obj F).homology p ≃ₗ[k] scalarCohomology f F p :=
    { toFun := fun x ↦ c (M.inv (S.hom x))
      invFun := fun y ↦ S.inv (M.hom ((asIso c).inv y))
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      map_add' := by
        intro x y
        change c.hom (M.inv.hom (S.hom.hom (x + y))) = _
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro r x
        change c (M.inv (S.hom (r • x))) = (scalarMap f ⊤ r) • c (M.inv (S.hom x))
        rw [hlinear]
        exact c.hom.map_smul _ _ }
  exact ⟨e, c, hc, fun _ ↦ rfl⟩

end AlgebraicGeometry.Scheme.Modules
