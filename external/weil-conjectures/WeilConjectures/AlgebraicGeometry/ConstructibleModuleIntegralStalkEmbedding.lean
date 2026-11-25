/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.ExtremalEpi

/-!
# Integral pushforward maps detecting a prescribed point

Source: Stacks Project, Tag 09Z6, the generic trivialization and normalization argument.
(blueprint: lem-weil-pbc-constructible-module-integral-stalk-embedding).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A constructible module sheaf has a map to an integral pushforward of a finite constant
module which is injective at every geometric point above a prescribed point.

Source: Stacks Project, Tag 09Z6, proof of (1), the paragraph starting with the reduced
closure of `x`, transferred to (3).
(blueprint: lem-weil-pbc-constructible-module-integral-stalk-embedding).

Proof: Pull back to Spec of the residue field of x. The constructible stratification pulls
back, so the resulting sheaf becomes a constant finite module M after a finite separable
extension K. Normalize the reduced closure of x in K. This gives a normal integral scheme
Y and an integral morphism nu : Y -> X with generic point Spec K. On Y the unit from the
constant module sheaf to the pushforward of its generic restriction is an isomorphism
(09Z5). First use the generic-point adjunction, then the nu adjunction, to obtain a map
phi : F -> nu_* M. These adjunctions and the constant-sheaf comparison are module-linear.
Every geometric point above x lifts to Spec K, since its algebraically closed residue field
contains a copy of the finite extension K. The pullback of the first adjoint map at this
lift is the chosen constant-sheaf isomorphism: the two triangle identities and naturality
of the counit give this equality. At the resulting point of Y, its stalk is therefore an
isomorphism. The stalk map of phi followed by restriction to this stalk of M is that
isomorphism, under the inverse-image stalk comparison. Hence the stalk map of phi is
injective. This works for every geometric point above x. There is no point to choose when
X is empty; for the zero sheaf the same construction uses the zero module. -/
theorem exists_integral_lowerStar_stalk_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        ∃ (φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
            ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
              Function.Injective
                (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map φ) := by
  classical
  obtain ⟨Y, ν, hν, K, hK, g, M, hM, hu, e, hlift⟩ :=
    exists_constructible_module_normalized_generic_data Λ F hF x
  let : Field K := hK
  let : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := hu
  let A := (upperStar (ModuleCat.{u + 1} Λ) ν).obj F
  let B := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  -- Adjunction along g and the invertible unit extend the generic isomorphism.
  let ψ : A ⟶ B := adj.homEquiv A _ e.some.hom ≫ inv (adj.unit.app B)
  have hψ : (upperStar (ModuleCat.{u + 1} Λ) g).map ψ = e.some.hom := by
    dsimp only [ψ]
    rw [Functor.map_comp, Functor.map_inv]
    rw [IsIso.inv_eq_of_hom_inv_id (adj.left_triangle_components B)]
    exact (adj.homEquiv A _).symm_apply_apply e.some.hom
  let adjν := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν
  let φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj B := adjν.homEquiv F B ψ
  have hφ : (upperStar (ModuleCat.{u + 1} Λ) ν).map φ ≫ adjν.counit.app B = ψ :=
    (adjν.homEquiv F B).symm_apply_apply ψ
  refine ⟨Y, ν, hν, M, hM, φ, ?_⟩
  intro Ω _ _ s hs
  obtain ⟨w, hw⟩ := hlift Ω s hs
  rw [← Category.assoc] at hw
  subst s
  let c := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g w
  -- Naturality transports the generic isomorphism to the stalk on Y.
  have hψstalk : IsIso
      (((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    have he : IsIso ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ) := by
      rw [hψ]
      infer_instance
    have he' : IsIso
        (((Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ)) := inferInstance
    have hn := c.hom.naturality ψ
    have eq : ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ =
        c.inv.app A ≫
          ((Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
            ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ) ≫ c.hom.app B := by
      rw [← cancel_epi (c.hom.app A)]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.comp_map] using hn.symm
    rw [eq]
    infer_instance
  let d := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν (w ≫ g)
  -- The stalk of φ has an invertible composite, so it is a monomorphism.
  have hfac :
      ((Scheme.pointSmallEtale ((w ≫ g) ≫ ν)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map φ ≫
          (d.inv.app ((lowerStar (ModuleCat.{u + 1} Λ) ν).obj B) ≫
            ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
              (A := ModuleCat.{u + 1} Λ)).map (adjν.counit.app B)) =
      d.inv.app F ≫ ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ := by
    rw [← Category.assoc, d.inv.naturality]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, hφ]
  have htarget : IsIso (d.inv.app F ≫
      ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    let : IsIso (((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ) := hψstalk
    infer_instance
  have hm : Mono (d.inv.app F ≫
      ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    exact (ModuleCat.mono_iff_injective _).2
      (ConcreteCategory.bijective_of_isIso
        (d.inv.app F ≫ ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map ψ)).1
  let := hm
  have : Mono (((Scheme.pointSmallEtale ((w ≫ g) ≫ ν)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map φ) := mono_of_mono_fac hfac
  exact (ModuleCat.mono_iff_injective _).mp this

end AlgebraicGeometry.Etale
