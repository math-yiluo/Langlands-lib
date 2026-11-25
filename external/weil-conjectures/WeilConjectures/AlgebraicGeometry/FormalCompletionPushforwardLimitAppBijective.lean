/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineSections
import WeilConjectures.AlgebraicGeometry.FormalFunctionsAffinePushforwardSections
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine section comparison is bijective by the formal functions theorem.
Source: Stacks Project, Theorem 02OC and Lemma 088B.
(blueprint: lem-weil-pbc-formal-completion-pushforward-limit-app-bijective)

Proof: Write U = Spec A and I = J(U), transporting along the affine chart.
The ring A is Noetherian because Y is Noetherian. Base change f to U; the restricted
morphism is proper, and the restriction of F is coherent. Put H = f_*F and
M = Gamma(U,H) = Gamma(f^(-1)U,F). Coherence of H gives quasi-coherence.
The affine ideal-product, power, and cokernel section formulas identify
Gamma(U,H/J^(n+1)H) with M/I^(n+1)M. Their quotient projections are surjective,
and the identifications intertwine transitions because both transitions commute
with the quotient projections. Restriction preserves products and quotients, so
pushforward sections of the target system are Gamma(f^(-1)U,F/(J O_X)^(n+1)F).
Evaluating hκ and cancelling the surjective quotient projection therefore identifies
κ_n on sections with the canonical quotient-induced map of globalSections_formal_functions.
The projection equations of that theorem identify the inverse limit of these maps
with its isomorphism from the I-adic completion of M. Evaluation of sheaves of modules
preserves limits, and its limit comparison is natural in κ. Thus (lim.map κ).app U
is conjugate to this isomorphism, hence bijective. Only sections on the given affine
open are calculated here; passing from this calculation to a sheaf isomorphism is
the separate affine-basis criterion in the parent module. If J is zero the systems
are constant; if J is the unit ideal they are zero. The zero module and empty open
also give zero limits.
-/
theorem formalCompletion_pushforward_limit_app_bijective {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Bijective ((lim.map κ).app U) := by
  let H := (Scheme.Modules.pushforward f).obj F.obj
  let R := Γ(Y, U)
  let I := J.ideal ⟨U, hU⟩
  let M := Γ(H, U)
  let S := formalCompletionSystem J H
  let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : H.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y H).mp h).1
  obtain ⟨q, hq, eS, heS⟩ := formalCompletion_affine_sections J H U hU
  obtain ⟨θ, hθ, eT, heT⟩ := formalFunctions_affine_pushforward_sections J f F U hU
  have hlevel (n : ℕ) : (q n).hom ≫ E.map (κ.app (op n)) = ModuleCat.ofHom (θ n) := by
    let π := ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ
    have : Epi π := (ModuleCat.epi_iff_surjective π).mpr
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ_surjective
    apply (cancel_epi π).1
    change (ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ) ≫
      (q n).hom ≫ E.map (κ.app (op n)) = _
    rw [← Category.assoc, hq, ← E.map_comp, hκ, ← hθ]
    rfl
  have hcomparison : eS.hom ≫ E.map (lim.map κ) = eT.hom := by
    apply (isLimitOfPreserves E (limit.isLimit T)).hom_ext
    intro n
    obtain ⟨n⟩ := n
    change (eS.hom ≫ E.map (lim.map κ)) ≫ E.map (limit.π T (op n)) =
      eT.hom ≫ E.map (limit.π T (op n))
    have hw : lim.map κ ≫ limit.π T (op n) =
        limit.π S (op n) ≫ κ.app (op n) := limMap_π κ (op n)
    rw [Category.assoc, ← E.map_comp, hw, E.map_comp,
      ← Category.assoc, heS, Category.assoc, hlevel, heT]
    rfl
  have hmap : E.map (lim.map κ) = eS.inv ≫ eT.hom := by
    rw [← hcomparison, Iso.inv_hom_id_assoc]
  change Function.Bijective (E.map (lim.map κ))
  rw [hmap]
  exact (eT.toLinearEquiv.bijective).comp (eS.symm.toLinearEquiv.bijective)

end AlgebraicGeometry
