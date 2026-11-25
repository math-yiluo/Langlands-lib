/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStep
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

/-!
# Assembly of finite coefficient models on strata

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
noetherian induction and extension descent, steps 4--7 of the parent descent node.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite coefficient models of the restrictions to a finite stratification assemble
to a constructible finite coefficient model of the original module. The fields may
differ from stratum to stratum; the extension classes must also be descended.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
steps 4--7 of lem-weil-pbc-condensed-finite-presentation-descent.
(auxiliary; not a blueprint node).

Proof: induct on closed supports in the noetherian space T. Pull the given stratification
and its already supplied models back to each closed subscheme in the induction. These
pullbacks preserve finite presentations. The empty support has the zero model. On a
nonempty support, finite irreducible components provide a nonempty open contained in
one stratum image. The base change to that stratum is a surjective closed immersion,
which need not be an isomorphism. Empty-complement ringed
open-closed localization identifies its module category with that of the open; the
identification is coefficient-compatible and reflects local finite presentation on
slices. Thus the supplied model on that stratum gives a finite coefficient model on
the open. Apply induction to the proper closed complement. Enlarge the two coefficient
fields to their finite compositum.

The localization sequence presents the original module as an extension of the closed
direct image by the open extension by zero. Their finite coefficient models are
constructible: combine their stratifications, and their restrictions to the opposite
part vanish. Scalar extension commutes with open extension by zero by tensor adjunction,
and with the closed direct image by finite freeness and its filtered-colimit continuity.
For finite fields, a finite field basis identifies scalar extension with a finite direct
sum; the coefficient colimit then makes extension to the closure exact. Scalar restriction
is exact since it changes only the action. The tensor-restriction adjunction thus induces
an adjunction of their termwise derived functors. The same coefficient colimit identifies
the restricted extended open model with the filtered colimit of its finite extensions.
Classify the extension as a degree-one derived map. This adjunction and
Ext-continuity for the constructible closed term descend this class to a further finite
field. Realize the class there by a short exact sequence. Serre closure makes its middle
term constructible. Exact scalar extension preserves the extension class, so the
injectivity of extension classification gives its scalar-extension isomorphism to the
original M. This proves the induction step. Empty strata contribute zero objects; an
empty stratification forces empty T, where the same zero model applies. No descent of
presentation matrices or transition maps is required here: the stratum models are inputs. -/
theorem exists_finiteCoefficient_model_of_stratum_models
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (M_E : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E))),
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
        Nonempty ((Mod.extendScalars ((upperStar Ab.{u + 1} (S.immersion a)).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅
            (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
              (padicAlgClRingObj T ℓ)).obj M))) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M) := by
  have supportModels : ∀ (D : TopologicalSpace.Closeds T) (Y : Scheme.{u}) (i : Y ⟶ T)
      [IsClosedImmersion i], Set.range i ⊆ D →
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)),
        IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M) := by
    intro D
    induction D using WellFoundedLT.induction with
    | ind D ih =>
      exact exists_finiteCoefficient_model_on_closed_support_step T ℓ M S hS D ih
  obtain ⟨E, P, hP, ⟨e⟩⟩ := supportModels ⊤ T (𝟙 T) (Set.subset_univ _)
  exact ⟨E, P, hP, ⟨e ≪≫ (profinitePointModuleIdentity
    (Profinite.padicAlgClRingObj ℓ) T).app M⟩⟩

end AlgebraicGeometry.ProEtale
