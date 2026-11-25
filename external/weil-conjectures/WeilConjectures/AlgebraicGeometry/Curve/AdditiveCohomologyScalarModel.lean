/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Finite-dimensional scalar model for first additive étale cohomology -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- First cohomology of the additive structure sheaf carries its finite-dimensional
scalar action, with scalar multiplication represented by actual sheaf endomorphisms.
Source: Stacks 0A3N, proof; blueprint `proposition-p-torsion-smooth-proper-curve--3`, steps 3--6.
(blueprint: lem-sc-additive-cohomology-finite-scalar-model)

Proof: Transport multiplication by the pullback of each c in k through the
natural section equivalences. Naturality of the scalar ring maps and a proves
that these section maps assemble into sheaf endomorphisms μ_c. Check μ_0 = 0,
μ_1 = id, μ_(c+d) = μ_c + μ_d and μ_(cd) = μ_d ≫ μ_c sectionwise. Applying the
additive cohomology functor yields every module axiom, with scalar action
c • x = H^1(μ_c)(x). The finite-dimensionality theorem for this scalar model
then gives finiteness. This construction involves no Frobenius or choice of
cohomology comparison. -/
theorem exists_finiteDimensional_etaleCohomology_one_scalar_model
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    let T := DerivedCategory.singleFunctor
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
    ∃ m : Module k (T.obj G),
      let := m
      FiniteDimensional k (T.obj G) ∧ ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : T.obj G, T.map μ x = c • x := by
  classical
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  have : T.Additive := by
    dsimp [T, Etale.cohomology, Etale.rightDerivedGlobalSections]
    infer_instance
  let ρ (U : C.Etaleᵒᵖ) : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hρ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (c : k) :
      g.unop.left.appTop.hom (ρ U c) = ρ V c := by
    dsimp [ρ]
    have hw : g.unop.left ≫ U.unop.hom = V.unop.hom := g.unop.w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hw]
  let μ (c : k) : G ⟶ G := ⟨{
    app U := AddCommGrpCat.ofHom {
      toFun x := (a U).symm (a U x * ρ U c)
      map_zero' := by simp
      map_add' x y := by simp [add_mul] }
    naturality U V g := by
      ext x
      apply (a V).injective
      change a V ((a V).symm (a V (G.obj.map g x) * ρ V c)) =
        a V (G.obj.map g ((a U).symm (a U x * ρ U c)))
      simp only [AddEquiv.apply_symm_apply, ha U V g]
      rw [g.unop.left.appTop.hom.map_mul, hρ] }⟩
  have hμ (c : k) (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U ((μ c).hom.app U x) = a U x * ρ U c := by
    exact (a U).apply_symm_apply _
  have hzero : μ 0 = 0 := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    rw [hμ]
    simp
  have hone : μ 1 = 𝟙 G := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    rw [hμ]
    simp
  have hadd (c d : k) : μ (c + d) = μ c + μ d := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    change a U ((μ (c + d)).hom.app U x) =
      a U ((μ c).hom.app U x + (μ d).hom.app U x)
    rw [map_add, hμ, hμ, hμ, map_add, mul_add]
  have hmul (c d : k) : μ (c * d) = μ d ≫ μ c := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    change a U ((μ (c * d)).hom.app U x) =
      a U ((μ c).hom.app U ((μ d).hom.app U x))
    rw [hμ, hμ, hμ, map_mul]
    ring
  let m : Module k (T.obj G) := {
    smul c x := T.map (μ c) x
    one_smul x := by
      change T.map (μ 1) x = x
      rw [hone, T.map_id]
      rfl
    mul_smul c d x := by
      change T.map (μ (c * d)) x = T.map (μ c) (T.map (μ d) x)
      rw [hmul, T.map_comp]
      rfl
    smul_zero c := (T.map (μ c)).hom.map_zero
    smul_add c x y := (T.map (μ c)).hom.map_add x y
    zero_smul x := by
      change T.map (μ 0) x = 0
      rw [hzero, T.map_zero]
      rfl
    add_smul c d x := by
      change T.map (μ (c + d)) x = T.map (μ c) x + T.map (μ d) x
      rw [hadd, T.map_add]
      rfl }
  let := m
  have hscalar : ∀ c : k, ∃ μ' : G ⟶ G,
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (μ'.hom.app U x) = a U x * ρ U c) ∧
      ∀ x : T.obj G, T.map μ' x = c • x := by
    intro c
    exact ⟨μ c, hμ c, fun _ ↦ rfl⟩
  exact ⟨m, finiteDimensional_etaleCohomology_one_of_scalar_model f G a ha m hscalar,
    hscalar⟩

end AlgebraicGeometry
