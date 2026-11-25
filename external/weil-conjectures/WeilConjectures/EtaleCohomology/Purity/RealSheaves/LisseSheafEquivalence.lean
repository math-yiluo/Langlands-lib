/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseRepAbelian
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections

/-!
# Lisse Weil sheaves on a curve as representations of the Weil group

The two subsection statements of the real-sheaves chapter about the lisse sheaf–representation
equivalence on a smooth geometrically connected curve `C₀` over a finite field:

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_tensor_shortExact` (blueprint
  `definition-weil-representation--1`): `ℱ ↦ (ℱ_η̄, ρ_ℱ)` is an exact tensor equivalence
  between lisse Weil sheaves on `C₀` and lisse representations of `W(C₀)`;
- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_globalSections_upperStar` (blueprint
  `lemma-degree-zero-top-cohomology--1`): for a nonempty open `U₀ ⊆ C₀`,
  `H⁰(U, ℱ|_U) = V ^ {π₁(U)}`, compatibly with the Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- Blueprint `definition-weil-representation--1`: lisse Weil sheaves are lisse
representations of the Weil group.

The functor `ℱ ↦ (ℱ_η̄, ρ_ℱ)` is an exact tensor equivalence between lisse Weil sheaves on `C₀`
and the lisse representations of `W(C₀)`: there is an equivalence `e` which is, naturally in
`ℱ` (`η`), the Weil fundamental representation `(ℱ_t, ρ_ℱ)` at the geometric base point `t` of
some base point data `B` (the analogue of the geometric generic point, for some monodromy `M`
of lisse sheaves on the geometric curve), which is compatible with tensor products (`τ`, via
`η` the identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t`) and sends `ℚ̄_ℓ` to the trivial
representation, and such that a short complex `0 → ℱ' → ℱ → ℱ'' → 0` of lisse Weil sheaves is
short exact if and only if `0 → V' → V → V'' → 0` is. Subobjects, quotients and subquotients
therefore match on the two sides. -/
theorem exists_equivalence_isLisse_tensor_shortExact :
    ∃ (M : ProEtale.LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K) (B : BasePointData W)
      (e : LisseWeilSheaf K l C ≌ (W.isLisseRep l).FullSubcategory)
      (η : e.functor ⋙ ObjectProperty.ι _ ⋙ Rep.uliftFunctor.{u, u + 1} (PadicAlgCl l) W.carrier ≅
        fundamentalRepFunctor M B.weilMonodromyData)
      (τ : LisseWeilSheaf.tensor K l C ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
        (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
          Rep.tprodFunctor.{u} (PadicAlgCl l) W.carrier),
      (∀ (F G : LisseWeilSheaf K l C)
          (v : (e.functor.obj ((LisseWeilSheaf.tensor K l C).obj (F, G))).obj.V),
        ((fundamentalRepTensorIso M B.weilMonodromyData).hom.app (F, G)).hom
            ((η.hom.app ((LisseWeilSheaf.tensor K l C).obj (F, G))).hom (ULift.up v)) =
          TensorProduct.map
            ((η.hom.app F).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((η.hom.app G).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((τ.hom.app (F, G)).hom v)) ∧
      Nonempty ((e.functor.obj (LisseWeilSheaf.unit K l C)).obj.ρ.Equiv
        (Representation.trivial (PadicAlgCl l) W.carrier (PadicAlgCl l))) ∧
      ∀ S : ShortComplex (LisseWeilSheaf K l C),
        (S.map (ObjectProperty.ι _)).ShortExact ↔
          (S.map (e.functor ⋙ ObjectProperty.ι _)).ShortExact := by
  obtain ⟨M, B, e, η, τ, hτ, h1⟩ := W.exists_equivalence_isLisse_tensor l
  exact ⟨M, B, e, η, τ, hτ, h1, isLisse_shortExact_iff (e := e)⟩

/-- Blueprint `lemma-degree-zero-top-cohomology--1`: global sections over an open subcurve are
invariants.

There is an equivalence `e` between lisse Weil sheaves on `C₀` and lisse representations of
`W(C₀)`, identifying the stalk of `ℱ` at every closed point `x` with `V = e ℱ`, Frobenius `F_x`
becoming `ρ (Frob_x)`, such that for every nonempty open subcurve `j : U₀ ⟶ C₀` with restriction
of Weil groups `R : W(U₀) → W(C₀)`,

`H⁰(U, ℱ|_U) ≅ V ^ {π₁(U)}`,

`π₁(U)` acting through `R`, compatibly with the Frobenius of the global sections and the
residual action of the Frobenius lift `ρ (R γ_U)`. -/
theorem exists_equivalence_isLisse_globalSections_upperStar :
    ∃ e : LisseWeilSheaf K l C ≌ (W.isLisseRep l).FullSubcategory,
      (∀ (F : LisseWeilSheaf K l C) (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      ∀ {U : Scheme.{u}} [U.Over (Spec (.of K))] [IsCurve (U ↘ Spec (.of K))]
        {WU : WeilGroup (U ↘ Spec (.of K))} (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
        [j.IsOver (Spec (.of K))] (R : Restriction j WU W) (F : LisseWeilSheaf K l C),
        ∃ f : ((WeilSheaf.upperStar j).obj F.obj).globalSections.carrier ≃ₗ[PadicAlgCl l]
            Representation.invariants
              (((e.functor.obj F).obj.ρ.comp R.restrict).comp WU.geometric.subtype),
          ∀ v, (f (((WeilSheaf.upperStar j).obj F.obj).globalSections.frobenius v) :
              (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ (R.restrict WU.frobeniusLift) (f v) := by
  obtain ⟨e, hst, -, hgl, -⟩ := W.exists_equivalence_isLisse l
  exact ⟨e, hst, fun j _ _ _ R F ↦ exists_globalSections_upperStar_linearEquiv_invariants e hgl R F⟩

end AlgebraicGeometry.WeilGroup
