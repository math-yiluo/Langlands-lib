/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.IsProperOrIsAffine
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Finite-dimensional scalar model for first additive étale cohomology -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scalar action on first additive étale cohomology induced by multiplication
on sections is finite-dimensional.
Source: Stacks 0A3N, proof, with 03P2 and 02O6; blueprint
`proposition-p-torsion-smooth-proper-curve--3`, steps 3--6.
(blueprint: lem-sc-additive-cohomology-finite-dimensional)

Proof: The natural section equivalences identify G with the universe lift of
the associated étale sheaf of O_C. A smooth connected curve is proper or affine
by compactification and affineness of a proper curve minus a nonempty finite
set. If affine, quasi-coherent étale acyclicity makes H^1 zero, so any k-action
on it is finite-dimensional. If proper, the étale/Zariski quasi-coherent
comparison identifies H^1 with H^1(C,O_C), finite-dimensional by proper
coherent cohomology. Naturality for multiplication by c identifies the action
in the hypothesis with the usual k-action: the sectionwise formula uniquely
determines each μ_c, so no arbitrary choice of action is being compared.
Identify derived cohomology with the injective-resolution model naturally
in the sheaf. For the coefficient universe change, use finite affine étale
hypercovers: finite refinements exist in each degree, and ULift identifies
cochains, cocycles, boundaries and scalar maps. The resulting comparison is
an additive equivalence and commutes with every scalar μ_c, hence is k-linear.
This argument does not require ULift to preserve injectives. Transport
finite-dimensionality across the linear equivalence. -/
theorem finiteDimensional_etaleCohomology_one_of_scalar_model
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    let T := DerivedCategory.singleFunctor
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
    ∀ m : Module k (T.obj G),
      letI := m
      (∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : T.obj G, T.map μ x = c • x) → FiniteDimensional k (T.obj G) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  dsimp only
  intro m
  let := m
  intro hscalar
  have := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  obtain ⟨e, he⟩ := exists_addEquiv_etaleCohomology_one_structureSheaf f G a ha
  let L : T.obj G →ₗ[k] Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1 :=
    { e.toAddMonoidHom with
      map_smul' c x := by
        obtain ⟨μ, hμ, hmap⟩ := hscalar c
        rw [← hmap x]
        exact he c μ hμ x }
  rcases IsConnectedCurve.isProper_or_isAffine f with hp | haff
  · have : IsProper (C ↘ Spec (.of k)) := hp
    have : (SheafOfModules.unit C.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit C.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    let := Scheme.Modules.finiteDimensional_H_of_isProper (k := k)
      (SheafOfModules.unit C.ringCatSheaf) 1
    exact FiniteDimensional.of_injective L e.injective
  · let := haff
    let := Scheme.Modules.subsingleton_H_succ_of_isAffine
      (SheafOfModules.unit C.ringCatSheaf) 0
    let : Subsingleton (T.obj G) := e.injective.subsingleton
    infer_instance

end AlgebraicGeometry
