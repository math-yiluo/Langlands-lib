/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalAffineSectionLimit
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsionKernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine sections of the finite-level completion quotients

Source: Stacks Project, Lemma 0881, affine quotient identification.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affine sections identify the positive-level completion quotients with the module
quotients, compatibly with transitions and coherent-module maps. No inverse limit,
realization equivalence, or reflection of limits is asserted here.

Source: Stacks Project, Lemma 0881, proof, affine identification of the quotient system;
Lemma 01IB for the affine sections/tilde equivalence.
(blueprint: lem-weil-pbc-formal-completion-affine-quotients).

Proof: Restriction to the open subscheme preserves ideal products, their powers,
and cokernels. Use the equality hρ to identify the underlying system with the
restricted quotients of G. Pushforward followed by sections on U recovers sections
of those quotients on the original affine open. The affine ideal dictionary and
exactness of sections on quasi-coherent modules identify the image of I^(n+1)G
with J^(n+1)Γ(G,U) and the cokernel with its module quotient. This gives θ.
For transitions, precompose both proposed maps with the surjective quotient map
Γ(G,U) -> Γ(G,U)/J^(m+1)Γ(G,U). Both composites are the quotient projection
at level n, by the defining equation of formalModuleQuotientMap. For a coherent
map f, precompose with the quotient projection for G; naturality of the cokernel
projection makes both composites the quotient projection for H after Γ(f,U).
Surjectivity proves both equalities. All powers are positive. For J=0 the quotient
maps are identities, for J=1 both quotients are zero, and the zero module and empty
open satisfy the same cokernel argument. -/
theorem formalCompletion_affine_quotients
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι)) :
    let T := formalAffineSectionTower X U (I.comap U.ι)
    let J := I.ideal ⟨U, hU⟩
    ∃ θ : ∀ (G : CoherentModules X) (n : ℕ),
      (Γ(G.obj, U) ⧸ (J ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj, U))) ≃ₗ[Γ(X, U)]
        (T.obj (ρ.obj ((completion X I).obj G))).obj (op n),
      (∀ (G : CoherentModules X) (n m : ℕ) (h : n ≤ m),
        ((T.obj (ρ.obj ((completion X I).obj G))).map (homOfLE h).op).hom.comp
            (θ G m).toLinearMap =
          (θ G n).toLinearMap.comp
            (AdicCompletion.transitionMap J Γ(G.obj, U) (Nat.succ_le_succ h))) ∧
      (∀ (G H : CoherentModules X) (f : G ⟶ H) (n : ℕ),
        ((T.map (ρ.map ((completion X I).map f))).app (op n)).hom.comp
            (θ G n).toLinearMap =
          (θ H n).toLinearMap.comp
            (((f.hom.val.app (op U)).hom.reduceModIdeal (J ^ (n + 1))).restrictScalars
              Γ(X, U))) :=
  by
  classical
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let R := Scheme.Modules.restrictFunctor U.ι
  let S := formalAffineSections X U
  let adj := Scheme.Modules.restrictAdjunction U.ι
  have he (M : X.Modules) : IsIso (E.map (adj.unit.app M)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective ((adj.unit.app M).app U)
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have hopen : U.ι ''ᵁ U.ι ⁻¹ᵁ U = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
    have hh : homOfLE (U.ι.image_preimage_le U) = eqToHom hopen := Subsingleton.elim _ _
    rw [hh]
    exact ConcreteCategory.bijective_of_isIso _
  let s : E ≅ R ⋙ S := NatIso.ofComponents
    (fun M ↦ by have := he M; exact asIso (E.map (adj.unit.app M))) (by
      intro M N f
      change E.map f ≫ E.map (adj.unit.app N) =
        E.map (adj.unit.app M) ≫ E.map ((R ⋙ Scheme.Modules.pushforward U.ι).map f)
      rw [← E.map_comp, ← E.map_comp]
      exact E.congr_map (adj.unit.naturality f))
  let W := Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat.{u} Γ(X, U))
  let V := Functor.whiskeringRight ℕᵒᵖ U.toScheme.Modules (ModuleCat.{u} Γ(X, U))
  let c := Functor.isoWhiskerLeft (ObjectProperty.ι (IsCoherentFormalModule I))
    (W.mapIso s)
  let b := Functor.isoWhiskerRight (eqToIso hρ) (V.obj S)
  let a : (IsCoherentFormalModule I).ι ⋙ W.obj E ≅
      ρ ⋙ formalAffineSectionTower X U (I.comap U.ι) := c ≪≫ b.symm
  let T := formalAffineSectionTower X U (I.comap U.ι)
  let J : Ideal Γ(X, U) := I.ideal ⟨U, hU⟩
  let M (G : CoherentModules X) := T.obj (ρ.obj ((completion X I).obj G))
  let aG (G : CoherentModules X) := a.app ((completion X I).obj G)
  let p (G : CoherentModules X) (n : ℕ) : Γ(G.obj, U) →ₗ[Γ(X, U)]
      E.obj (formalModuleQuotient I (n + 1) G.obj) :=
    (E.map (formalModuleQuotientπ I (n + 1) G.obj)).hom
  have hq (G : CoherentModules X) (n : ℕ) :
      Function.Surjective (p G n) ∧
        LinearMap.ker (p G n) = J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj, U)) := by
    have : G.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp G.property).1
    exact (quotient_affine I G.obj ⟨U, hU⟩ (n + 1) (by omega)).2
  let t (G : CoherentModules X) (n : ℕ) :=
    (Submodule.quotEquivOfEq _ _ (hq G n).2.symm).trans
      ((p G n).quotKerEquivOfSurjective (hq G n).1)
  let θ (G : CoherentModules X) (n : ℕ) :=
    (t G n).trans ((aG G).app (op n)).toLinearEquiv
  have ht (G : CoherentModules X) (n : ℕ) (x : Γ(G.obj, U)) :
      θ G n (Submodule.Quotient.mk x) = (aG G).hom.app (op n) (p G n x) := by
    simp only [θ, t, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl
  refine ⟨θ, ?_, ?_⟩
  · intro G n m h
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      (J ^ (m + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj, U))) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (M G).map (homOfLE h).op (θ G m (Submodule.Quotient.mk y)) =
      θ G n (Submodule.Quotient.mk y)
    rw [ht, ht]
    have ha := ConcreteCategory.congr_hom ((aG G).hom.naturality (homOfLE h).op)
      (p G m y)
    change (aG G).hom.app (op n)
      ((E.map (formalModuleQuotientMap I (𝟙 G.obj) (Nat.succ_le_succ h))) (p G m y)) =
      (M G).map (homOfLE h).op ((aG G).hom.app (op m) (p G m y)) at ha
    rw [← ha]
    congr 1
    change ((E.map (formalModuleQuotientπ I (m + 1) G.obj) ≫
      E.map (formalModuleQuotientMap I (𝟙 G.obj) (Nat.succ_le_succ h)))) y = _
    rw [← E.map_comp]
    simp only [formalModuleQuotientMap, formalModuleQuotientπ, cokernel.π_desc, p,
      Category.id_comp]
    rfl
  · intro G H f n
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      (J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj, U))) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change ((T.map (ρ.map ((completion X I).map f))).app (op n))
      (θ G n (Submodule.Quotient.mk y)) =
        θ H n (Submodule.Quotient.mk ((f.hom.val.app (op U)).hom y))
    rw [ht, ht]
    have ha := NatTrans.congr_app (a.hom.naturality ((completion X I).map f)) (op n)
    have hav := ConcreteCategory.congr_hom ha (p G n y)
    change (aG H).hom.app (op n)
      ((E.map (formalModuleQuotientMap I f.hom (Nat.le_refl (n + 1)))) (p G n y)) =
      ((T.map (ρ.map ((completion X I).map f))).app (op n))
        ((aG G).hom.app (op n) (p G n y)) at hav
    rw [← hav]
    congr 1
    change ((E.map (formalModuleQuotientπ I (n + 1) G.obj) ≫
      E.map (formalModuleQuotientMap I f.hom (Nat.le_refl (n + 1))))) y = _
    rw [← E.map_comp]
    simp only [formalModuleQuotientMap, formalModuleQuotientπ, cokernel.π_desc, p]
    rfl


end AlgebraicGeometry
