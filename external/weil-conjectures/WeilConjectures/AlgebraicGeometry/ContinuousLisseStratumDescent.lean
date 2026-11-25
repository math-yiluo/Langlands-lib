/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.AlgebraicGeometry.ContinuousLissePullbackSystem
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lattice of `p^* P` over `U` descends to a lattice of `j^* P` over a stratum `W`, given a
commutative square `r ≫ p = q ≫ j` with `q` finite étale surjective and descent of lattices
along `q`.
Source: Bhatt--Scholze, proof of Lemma 6.8.13.
(auxiliary; not a blueprint node) -/
theorem continuousLisse_lattice_on_stratum
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] (D : PullbackSystemCore Λ₀ Λ₁ φ)
    {X U V W : Scheme.{u}} [TopologicalSpace.NoetherianSpace W]
    (p : U ⟶ X) (j : W ⟶ X) (r : V ⟶ U) (q : V ⟶ W)
    [IsFinite q] [Etale q] [Surjective q] (w : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X))
    (hP : IsLocallyFree (condensedRingObj (Λ₁) X) P)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Λ₀) U))
    (hM : IsLocallyFree (condensedRingObj (Λ₀) U) M)
    (e : (Mod.extendScalars (coefficientMap (φ) U)).obj M ≅
      (CondensedRing.upperStar (Λ₁) p).obj P)
    (hdescent : ∀ (P' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ₁ W)), IsLocallyFree (condensedRingObj Λ₁ W) P' →
      ∀ (M' : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj Λ₀ V)), IsLocallyFree (condensedRingObj Λ₀ V) M' →
      Nonempty ((Mod.extendScalars (coefficientMap φ V)).obj M' ≅
        (CondensedRing.upperStar Λ₁ q).obj P') →
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₀ W),
        IsLocallyFree (condensedRingObj Λ₀ W) N ∧
        Nonempty ((Mod.extendScalars (coefficientMap φ W)).obj N ≅ P')) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj (Λ₀) W),
      IsLocallyFree (condensedRingObj (Λ₀) W) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (φ) W)).obj N ≅
        (CondensedRing.upperStar (Λ₁) j).obj P) := by
  obtain ⟨P', hP', ⟨iP⟩⟩ : ∃ P' : Mod _
      (condensedRingObj (Λ₁) W),
      IsLocallyFree _ P' ∧ Nonempty
        (P' ≅ (D.rational j).obj P) :=
    ⟨_, D.rationalFree j hP, ⟨Iso.refl _⟩⟩
  obtain ⟨M', hM', ⟨iM⟩⟩ : ∃ M' : Mod _
      (condensedRingObj (Λ₀) V),
      IsLocallyFree _ M' ∧ Nonempty
        (M' ≅ (D.integral r).obj M) :=
    ⟨_, D.integralFree r hM, ⟨Iso.refl _⟩⟩
  have e' : (Mod.extendScalars (coefficientMap (φ) _)).obj M' ≅
      (D.rational q).obj P' :=
    pullbackSystem_scalarSquareIso _ _ _ D p j r q w P M P' M' iP iM e
  obtain ⟨N, hN, eN⟩ := hdescent P' hP' M' hM' ⟨e' ≪≫ (D.rationalIso q).app P'⟩
  exact ⟨N, hN, ⟨eN.some ≪≫ iP ≪≫ (D.rationalIso j).app P⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
