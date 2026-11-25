/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalFunctionsAffineRestrictionDictionary
import WeilConjectures.AlgebraicGeometry.TheoremFormalFunctions
import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Formal functions on an affine open of the base

Source: Stacks Project, Theorem 02OC, degree zero, and Lemma 088B.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private lemma quotientTransport_comp_mkQ {R : Type*} [CommRing R]
    (I : Ideal R) {M N P Q : ModuleCat R} (a : M ≅ N) (b : P ⟶ Q)
    (θ : (N ⧸ (I • (⊤ : Submodule R N))) →ₗ[R] P) (ρ : N ⟶ P)
    (hθ : θ.comp (Submodule.mkQ (I • (⊤ : Submodule R N))) = ρ.hom) :
    ModuleCat.ofHom ((b.hom.comp
      (θ.comp ((a.toLinearEquiv.toLinearMap.reduceModIdeal I).restrictScalars R))).comp
        (Submodule.mkQ (I • (⊤ : Submodule R M)))) = a.hom ≫ ρ ≫ b := by
  ext x
  exact congrArg b (LinearMap.congr_fun hθ (a.hom x))

private lemma limitIsoTransport_π {C D J : Type*}
    [Category C] [Category D] [Category J]
    (E : C ⥤ D) (T : J ⥤ C) [HasLimit T] [PreservesLimit T E]
    (S : J ⥤ D) [HasLimit S] [HasLimit (T ⋙ E)]
    {A B : D} (c : A ≅ B) (e : B ≅ limit S) (b : S ≅ T ⋙ E) (j : J) :
    (c ≪≫ e ≪≫ HasLimit.isoOfNatIso b ≪≫ (preservesLimitIso E T).symm).hom ≫
        E.map (limit.π T j) = c.hom ≫ (e.hom ≫ limit.π S j) ≫ b.hom.app j := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    preservesLimitIso_inv_π, HasLimit.isoOfNatIso_hom_π]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport degree-zero formal functions to an arbitrary affine open of the base.
Source: Stacks Project, Theorem 02OC and Lemma 088B.
(blueprint: lem-weil-pbc-formal-functions-affine-pushforward-sections)

Proof: Write U as Spec A using its affine chart. Since Y is Noetherian, A is Noetherian.
Base change f along U -> Y; the resulting morphism to U is proper. Restrict F to the
inverse image of U, preserving coherence, and transport it along the affine chart.
The restricted ideal J is the ideal sheaf of I = J(U); its pullback is the restriction
of J.comap f. Restriction preserves ideal products, powers, and cokernels, so the
restricted quotient system is the quotient system in globalSections_formal_functions.
The identity Gamma(U,f_*F) = Gamma(f^(-1)U,F) supplies its module M, including the
A-action induced by f. Apply globalSections_formal_functions to obtain theta_n and
its canonical isomorphism. Pushforward on sections is evaluation on the inverse image,
and evaluation preserves limits. Transport the isomorphism and both projection equations
through these identifications. The quotient equation below is the transported theta_n
factorization; the last equation is the transported limit projection equation.
For J=0 this is the constant-section system; for J=1 its quotients and completion are
zero. F=0 and the empty open also give zero modules. No coherence assumption on f_*F
and no natural transformation kappa are needed for this transport step.
-/
theorem formalFunctions_affine_pushforward_sections {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (F : CoherentModules X)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let H := (Scheme.Modules.pushforward f).obj F.obj
    let M := Γ(H, U)
    let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ θ : ∀ n : ℕ,
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) →ₗ[R] E.obj (T.obj (op n)),
      (∀ n : ℕ, ModuleCat.ofHom
        ((θ n).comp (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))) =
          E.map ((Scheme.Modules.pushforward f).map
            (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))) ∧
      ∃ e : ModuleCat.of R (AdicCompletion I M) ≅ E.obj (limit T),
        ∀ n : ℕ, e.hom ≫ E.map (limit.π T (op n)) =
          ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval I M (n + 1))) := by
  let R := Γ(Y, U)
  let I := J.ideal ⟨U, hU⟩
  let V := f ⁻¹ᵁ U
  let Z := V.toScheme
  let g := (f ∣_ U) ≫ hU.isoSpec.hom
  let K := (J.comap f).comap V.ι
  let P := (Scheme.Modules.restrictFunctor V.ι).obj F.obj
  let G := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
  let H := (Scheme.Modules.pushforward f).obj F.obj
  let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨hg, hP, hK, a, b, hb⟩ :=
    formalFunctions_affine_restriction_dictionary J f F U hU
  let : IsProper g := hg
  obtain ⟨θ₀, hθ₀, _, e₀, he₀⟩ := globalSections_formal_functions (A := R) I g K hK P hP
  let α := a.toLinearEquiv
  let θ : ∀ n : ℕ, (Γ(H, U) ⧸ (I ^ (n + 1) • (⊤ : Submodule R Γ(H, U)))) →ₗ[R]
      E.obj (T.obj (op n)) := fun n ↦ (b.hom.app (op n)).hom.comp
        ((θ₀ n).comp ((α.toLinearMap.reduceModIdeal (I ^ (n + 1))).restrictScalars R))
  have hθ (n : ℕ) : ModuleCat.ofHom
      ((θ n).comp (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R Γ(H, U))))) =
      E.map ((Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) := by
    exact (quotientTransport_comp_mkQ (I ^ (n + 1)) a (b.hom.app (op n))
      (θ₀ n) (G.map (formalModuleQuotientπ K (n + 1) P)) (hθ₀ n)).trans (hb n)
  let c := ((AdicCompletion.congr I α).restrictScalars R).toModuleIso
  let d := preservesLimitIso E T
  let e := c ≪≫ e₀ ≪≫ HasLimit.isoOfNatIso b ≪≫ d.symm
  refine ⟨θ, hθ, e, ?_⟩
  intro n
  refine (limitIsoTransport_π E T _ c e₀ b (op n)).trans ?_
  rw [he₀]
  apply ModuleCat.hom_ext
  ext x
  rfl

end AlgebraicGeometry
