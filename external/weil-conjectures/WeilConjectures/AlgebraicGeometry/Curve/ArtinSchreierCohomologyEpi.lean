/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Frobenius minus identity is onto in first additive cohomology of a curve.
Source: blueprint `proposition-p-torsion-smooth-proper-curve--3`, steps 3--7; Stacks 0A3L and 0A3N.
(blueprint: lem-sc-artin-schreier-first-cohomology-epi)

Proof: The natural section equivalences identify G with the additive etale
structure sheaf and wp with x ↦ x^p-x. Compactify the smooth connected curve;
it is either proper or affine (lemma-proper-smooth-model--1,
proposition-p-torsion-smooth-proper-curve--3). In the affine case its first additive cohomology
vanishes by lemma-p-torsion-affine-curve-characteristic--4, so every endomorphism is onto.
In the proper case scalar multiplication on sections induces a k-vector-space
structure on H^1(C,G). Additivity of cohomology transports the sectionwise
relations for scalar multiplication, Frobenius, and subtraction, so H^1(wp)
is F-1 for a p-semilinear F. Naturality of the etale/Zariski comparison
(lem-sc-etale-zariski-qcoh-comparison) identifies this vector space linearly
with H^1(C,O_C). Proper coherent cohomology is finite dimensional by
lem-pc-coherent-hi and pqf-def-cohomology. Lang--Steinberg
(proposition-p-torsion-smooth-proper-curve--3, Stacks 0A3L) gives surjectivity of F-1. The natural
injective-resolution comparison with derived global sections preserves this
map, and surjectivity in additive groups is equivalent to epimorphy. The
universe comparisons can be made on finite affine etale hypercover cochains
(quasi-compactness supplies finite refinements in each relevant degree). Lifting
identifies cocycles, coboundaries, and the maps induced by wp; one need not
assume that universe lift preserves injective sheaves. -/
theorem epi_etaleCohomology_artinSchreier_one
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x) :
    Epi ((Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)).map
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map wp)) := by
  classical
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  obtain ⟨m, hfinite, hscalar⟩ :=
    exists_finiteDimensional_etaleCohomology_one_scalar_model f G a ha
  let := m
  let := hfinite
  have : T.Additive := by
    dsimp [T, Etale.cohomology, Etale.rightDerivedGlobalSections]
    infer_instance
  let φ : G ⟶ G := wp + 𝟙 G
  have hφ (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U (φ.hom.app U x) = (a U x) ^ p := by
    change a U (wp.hom.app U x + x) = _
    rw [map_add, hwp, sub_add_cancel]
  have hsemi (c : k) (x : T.obj G) : T.map φ (c • x) = c ^ p • T.map φ x := by
    obtain ⟨μ, hμ, hμmap⟩ := hscalar c
    obtain ⟨ν, hν, hνmap⟩ := hscalar (c ^ p)
    have hcomm : μ ≫ φ = φ ≫ ν := by
      apply Sheaf.hom_ext
      ext U y
      apply (a U).injective
      change a U (φ.hom.app U (μ.hom.app U y)) =
        a U (ν.hom.app U (φ.hom.app U y))
      rw [hφ, hμ, hν, hφ]
      let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
      change (a U y * ρ c) ^ p = (a U y) ^ p * ρ (c ^ p)
      rw [mul_pow, map_pow]
    rw [← hμmap, ← AddCommGrpCat.comp_apply, ← T.map_comp, hcomm, T.map_comp,
      AddCommGrpCat.comp_apply, hνmap]
  let F : T.obj G →ₛₗ[frobenius k p] T.obj G :=
    { toFun := T.map φ
      map_add' := (T.map φ).hom.map_add
      map_smul' := fun c x ↦ by simpa only [frobenius_def] using hsemi c x }
  have hF (x : T.obj G) : F x - x = T.map wp x := by
    change T.map (wp + 𝟙 G) x - x = _
    rw [T.map_add, T.map_id]
    change (T.map wp x + x) - x = _
    exact add_sub_cancel_right _ _
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := LinearMap.Frobenius.surjective_sub_id F y
  exact ⟨x, (hF x).symm.trans hx⟩

end AlgebraicGeometry
