/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineGlobalComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Affine formal maps and inverse limits of sections

Source: Stacks Project, Tags 087W, 00MA and 0889(1).
(blueprint: lem-weil-pbc-affine-formal-map-limit-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A coherent affine tilde presentation has a finite module of coefficients.
Source: Stacks Project, Tags 01IB, 01PB and 01XZ. -/
private theorem finite_presentation_module
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X]
    (H : CoherentModules X) (P : ModuleCat.{u} Γ(X, ⊤))
    (ε : (tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom).obj P ≅ H.obj) :
    Module.Finite Γ(X, ⊤) P := by
  have hH := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X H.obj).mp H.property
  have : H.obj.IsQuasicoherent := hH.1
  have : H.obj.IsFiniteType := hH.2
  have : Module.Finite Γ(X, ⊤) Γ(H.obj, ⊤) :=
    (Scheme.Modules.affine_finiteType_generatingSections X H.obj).1
  let M := H.obj.restrict X.isoSpec.inv
  let e₀ := Scheme.Modules.sectionsRestrictFromSpecLinearEquiv H.obj (isAffineOpen_top X)
  have : Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj M) := by
    apply Module.Finite.equiv
      (show Γ(H.obj, ⊤) ≃ₗ[Γ(X, ⊤)] (moduleSpecΓFunctor.obj M) from ?_)
    exact e₀.symm ≪≫ₗ (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := X))).app
        H.obj)).toLinearEquiv
  let T := tilde.functor Γ(X, ⊤)
  let R := Scheme.Modules.restrictFunctor X.isoSpec.inv
  let e : T.obj P ≅ M :=
    ((Scheme.Modules.restrictFunctorId (X := Spec Γ(X, ⊤))).app (T.obj P)).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr X.isoSpec.inv_hom_id).app (T.obj P)).symm ≪≫
    (Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.isoSpec.hom).app (T.obj P) ≪≫
    R.mapIso ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app (T.obj P)) ≪≫
    R.mapIso ε
  let eP := (tilde.toTildeΓNatIso (R := Γ(X, ⊤))).app P ≪≫
    moduleSpecΓFunctor.mapIso e
  exact Module.Finite.equiv eP.toLinearEquiv.symm

/-- A full faithful realization transports a morphism across an equivalence, compatibly
with a second natural comparison. -/
private theorem affine_comparison_factorization
    {M N V W : Type*} [Category M] [Category N] [Category V] [Category W]
    (E : M ≌ N) (ι : N ⥤ V) [ι.Full] [ι.Faithful]
    (R : M ⥤ W) (C : W ⥤ V) (D : V ⥤ W)
    (β : E.functor ⋙ ι ≅ R ⋙ C) (γ : R ≅ E.functor ⋙ ι ⋙ D)
    (B : M) {N₀ H : N} (δ : N₀ ⟶ H) (τ : C.obj (R.obj B) ≅ ι.obj H) :
    ∃ (Q : M) (ψ : Q ⟶ B) (ρ : ι.obj N₀ ≅ C.obj (R.obj Q))
      (a : R.obj Q ≅ D.obj (ι.obj N₀)) (b : R.obj B ≅ D.obj (ι.obj H)),
      ι.map δ = ρ.hom ≫ C.map (R.map ψ) ≫ τ.hom ∧
        R.map ψ ≫ b.hom = a.hom ≫ D.map (ι.map δ) := by
  let Q := E.inverse.obj N₀
  let c := E.counitIso.app N₀
  let t : ι.obj (E.functor.obj B) ≅ ι.obj H := β.app B ≪≫ τ
  let t' : E.functor.obj B ≅ H := ι.preimageIso t
  let f : E.functor.obj Q ⟶ E.functor.obj B := c.hom ≫ δ ≫ t'.inv
  let ψ : Q ⟶ B := E.functor.preimage f
  have hψt : ι.map (E.functor.map ψ) ≫ t.hom = ι.map c.hom ≫ ι.map δ := by
    dsimp only [ψ]
    rw [E.functor.map_preimage]
    dsimp only [f]
    simp only [Functor.map_comp, t', Functor.preimageIso_inv, Functor.map_preimage,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨Q, ψ, ι.mapIso c.symm ≪≫ β.app Q,
    γ.app Q ≪≫ D.mapIso (ι.mapIso c), γ.app B ≪≫ D.mapIso t, ?_, ?_⟩
  · have hβ := β.hom.naturality ψ
    change ι.map (E.functor.map ψ) ≫ (β.app B).hom =
      (β.app Q).hom ≫ C.map (R.map ψ) at hβ
    change ι.map δ = (ι.map c.inv ≫ (β.app Q).hom) ≫ C.map (R.map ψ) ≫ τ.hom
    rw [Category.assoc, ← Category.assoc (β.app Q).hom, ← hβ,
      Category.assoc]
    change ι.map δ = ι.map c.inv ≫ ι.map (E.functor.map ψ) ≫ t.hom
    rw [hψt, ← ι.map_comp_assoc, c.inv_hom_id, ι.map_id, Category.id_comp]
  · have hγ := γ.hom.naturality ψ
    change R.map ψ ≫ (γ.app B).hom =
      (γ.app Q).hom ≫ D.map (ι.map (E.functor.map ψ)) at hγ
    change R.map ψ ≫ ((γ.app B).hom ≫ D.map t.hom) =
      ((γ.app Q).hom ≫ D.map (ι.map c.hom)) ≫ D.map (ι.map δ)
    rw [← Category.assoc, hγ, Category.assoc, ← D.map_comp, hψt,
      D.map_comp, Category.assoc]

/-- The affine dictionary identifies a formal morphism with a completed linear map,
and identifies that map with the actual inverse limit of its section maps.
No torsion hypothesis or annihilator conclusion is involved.

Source: Stacks Project, Tags 087W, 00MA and 0889(1), affine comparison before
applying Remark 0888.
(blueprint: lem-weil-pbc-affine-formal-map-limit-dictionary).

Proof:
1. Coherence makes the top sections of H finite. Restrict epsilon to Spec A, use
   the tilde unit and the natural affine section comparison to identify P with
   those sections. Hence P is finite over A and B = S tensor P is finite over S.
2. Use the affine equivalence E from finite S-modules to coherent formal systems,
   with its quotient-system comparison beta and section-limit comparison gamma.
   Put Q = E.inverse(N) and let c : E(Q) isomorphic to N be the counit. Put
   t = beta(B), followed by eta inverse and completion(epsilon). Lift t to the
   coherent formal subcategory. Fullness gives psi : Q -> B whose image is
   c.hom followed by delta and t inverse. Its underlying S-linear map is phi.
   Set rho = c inverse followed by beta(Q). Naturality of beta and cancellation
   of the counit and t give the displayed factorization.
3. Define a as gamma(Q) followed by lim sections c, and b as gamma(B) followed by
   lim sections t. These composites are A-linear equivalences. Naturality of
   gamma for psi, followed by lim sections t, gives the commuting square, since
   E(psi) followed by t equals c followed by delta. Evaluate this equality of
   ModuleCat morphisms at x. The construction uses the given eta without changing it.
These constructions use finite-module completeness over the Noetherian completed
ring. For I=0 the quotient systems are constant, and for I=A all formal modules
and limits are zero. Thus the same comparisons apply to these cases and to the
zero ring. No data definition chooses a witness from this existence theorem.
-/
theorem affine_formal_map_limit_dictionary
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∀ (P : ModuleCat.{u} A) (ε : L.obj P ≅ H.obj)
      (η : C.obj P ≅ C.obj (ModuleCat.of A (S ⊗[A] P))),
    ∃ Q : ModuleCat.{u} S,
      letI := Module.restrictScalars A S Q
      letI := IsScalarTower.restrictScalars A S Q
      ∃ (φ : Q →ₗ[S] S ⊗[A] P)
        (ρ : N.obj ≅ C.obj (ModuleCat.of A Q))
        (a : Q ≃ₗ[A] ↥(limit (N.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A))
        (b : (S ⊗[A] P) ≃ₗ[A] ↥(limit (((completion X J).obj H).obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A)),
        δ.hom = ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫
          η.inv ≫ (formalCompletionFunctor J).map ε.hom ∧
        ∀ x : Q, b (φ x) =
          (lim.map (Functor.whiskerRight δ.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))).hom (a x) := by
  classical
  intro A I S L C P ε η
  let R := ObjectProperty.ι (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) ⋙
    ModuleCat.restrictScalars (algebraMap A S)
  let ι := (IsCoherentFormalModule J).ι
  let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)).obj
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let D := W ⋙ lim
  have : Module.Finite A P := finite_presentation_module H P ε
  have : Module.Finite S (S ⊗[A] P) := inferInstance
  obtain ⟨E, ⟨β⟩, ⟨γ⟩⟩ := coherentFormalModules_affine_global_comparison X J
  let B : ObjectProperty.FullSubcategory
      (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) :=
    ⟨ModuleCat.of S (S ⊗[A] P), inferInstance⟩
  obtain ⟨Q, ψ, ρ, a, b, hδ, hs⟩ := affine_comparison_factorization
    E ι R C D β γ B δ (η.symm ≪≫ (formalCompletionFunctor J).mapIso ε)
  let := Module.restrictScalars A S Q.obj
  let := IsScalarTower.restrictScalars A S Q.obj
  refine ⟨Q.obj, ψ.hom.hom, ρ, a.toLinearEquiv, b.toLinearEquiv, ?_, ?_⟩
  · exact hδ
  · intro x
    exact congrArg (fun g ↦ g x) hs

end AlgebraicGeometry
