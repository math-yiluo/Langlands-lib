/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Cover detection for condensed module isomorphisms

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lemma-artin-schreier-character-sheaf, proof Step 5, sheaf descent
(blueprint: lem-fd-as-trace-tensor-add-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ArtinSchreierTrace

/-- A morphism of condensed module sheaves which becomes invertible on a pro-etale cover
is an isomorphism.
Source: the equalizer descent clause of the sheaf tensor structure, as used in
blueprint lemma-artin-schreier-character-sheaf, proof Step 5 (blueprint:
lem-fd-as-trace-tensor-add-descent).

Proof: apply the local isomorphism criterion for sheaves of modules to the underlying
abelian-sheaf morphism.  The cover maps are jointly conservative, so the local inverses
and the two inverse identities descend through the equalizer diagrams.  The resulting
inverse is a morphism of module objects because the module equalizer is created by the
underlying sheaf. -/
theorem condensedArtinSchreier_tensor_add_of_local_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}}
    {A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (e : A ⟶ B)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (he : ∀ i : U.I₀,
      IsIso ((ProEtale.CondensedRing.upperStar Λ (U.f i)).map e)) :
    Nonempty (A ≅ B) := by
  have hweak (i : U.I₀) : WeaklyEtale (U.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X U.mem₀) ⟨i⟩
  have : IsIso ((Mod.forget (condensedRingObj Λ X)).map e) := by
    apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ U.f U.mem₀
    intro i
    let e' : CondensedRing.upperStar Λ (U.f i) ⋙ Mod.forget _ ≅
        Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} (U.f i) :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          ((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X))
          (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (U.f i))))
        (Mod.forget _)
    have h := he i
    have h' : IsIso ((upperStar Ab.{u + 1} (U.f i)).map e.hom) :=
      (NatIso.isIso_map_iff e' e).1 (by
        change IsIso ((Mod.forget _).map ((CondensedRing.upperStar Λ (U.f i)).map e))
        infer_instance)
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (U.f i) (hweak i)) e.hom).1 h'
  have : IsIso e := isIso_of_reflects_iso e (Mod.forget _)
  exact ⟨asIso e⟩

end AlgebraicGeometry.ArtinSchreierTrace
