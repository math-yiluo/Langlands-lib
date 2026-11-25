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
import Mathlib.FieldTheory.IsAlgClosed.Basic
/-!
# Geometric points lift through normalized residue-field extensions

Source: Stacks Project, Tag 09Z6, algebraically closed extension argument.
(blueprint: new-normalized-generic-data-lifts).
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- Geometric points lift through normalized generic data.
Source: Stacks Project, Tag 09Z6, algebraically closed extension argument.
(blueprint: new-normalized-generic-data-lifts).
The supplied finite residue-field algebra and factorization retain the normalization square.
Extend the residue-field map along the finite algebraic extension K and use
functoriality of Spec and the normalization factorization. -/
theorem normalized_generic_data_lifts
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (_hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X)
    (Y : Scheme.{u}) (ν : Y ⟶ X) (_hν : IsIntegralHom ν)
    (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
    (a : Algebra (X.residueField x) K)
    (ha : @Module.Finite (X.residueField x) K _ _ a.toModule)
    (hcomp : Spec.map (CommRingCat.ofHom (@algebraMap (X.residueField x) K _ _ a)) ≫
      X.fromSpecResidueField x = g ≫ ν)
    (M : ModuleCat.{u + 1} Λ) (_hM : Finite M)
    (_hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    (_he : Nonempty
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
       (upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
        ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s := by
  let := a
  let := ha
  intro Ω _ _ s hs
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective s
  obtain rfl : y = x := by simpa [Scheme.SpecToEquivOfField] using hs
  let : Algebra (X.residueField y) Ω := φ.hom.toAlgebra
  let e : K →ₐ[X.residueField y] Ω := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom), ?_⟩
  rw [← hcomp, ← Spec.map_comp_assoc]
  congr 2
  ext r
  exact e.commutes r
end AlgebraicGeometry.Etale
