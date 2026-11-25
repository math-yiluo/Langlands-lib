/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedFiniteModelImmersionRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Topology.StratificationDense

/-! Open-piece part of the nonempty support induction step. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma exists_nonempty_open_in_stratum
    {T Y : Scheme.{u}} (S : Scheme.Stratification T)
    (i : Y ⟶ T) [Nonempty Y] :
    ∃ (a : Fin S.n) (U : Y.Opens), Nonempty U ∧
      Set.range (U.ι ≫ i) ⊆ Set.range (S.immersion a) := by
  let S' := S.pullback i
  obtain ⟨y, hy⟩ := S'.dense_iUnion_interior_stratum.nonempty
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
  let U : Y.Opens := ⟨interior (S'.stratum a), isOpen_interior⟩
  refine ⟨a, U, ⟨⟨y, ha⟩⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [S.range_immersion]
  exact interior_subset (s := S'.stratum a) x.property

private lemma constructible_of_lfp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : IsLocallyFinitelyPresented R P) : IsConstructibleModuleObject R P := by
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  exact localFinitePresentation_pullback _ hP

private noncomputable def normalizedModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T V : Scheme.{u}} (f : V ⟶ T)
    (P : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T))) :
    Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V) :=
  (Mod.extendScalars (condensedPullbackHom Λ f)).obj P

private lemma normalizedModel_lfp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T V : Scheme.{u}} (f : V ⟶ T)
    (P : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T)))
    (hP : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T)) P) :
    IsLocallyFinitelyPresented (condensedRingObj Λ V) (normalizedModel Λ f P) := by
  unfold normalizedModel
  exact localFinitePresentation_of_iso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app P).symm
    (localFinitePresentation_comap (inv (condensedPullbackHom Λ f)) hP)

private noncomputable def normalizedModelIso
    (Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [MonObj Ω] [IsCommMonObj Λ] [IsCommMonObj Ω]
    (a : Λ ⟶ Ω) [IsMonHom a] {T V : Scheme.{u}} (f : V ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Ω T))
    (P : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T)))
    (e : (Mod.extendScalars ((upperStar Ab.{u + 1} f).map (coefficientMap a T))).obj P ≅
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Ω T)).obj M)) :
    (Mod.extendScalars (coefficientMap a V)).obj (normalizedModel Λ f P) ≅
      (CondensedRing.upperStar Ω f).obj M := by
  unfold normalizedModel
  let α := condensedPullbackHom Λ f
  let β := condensedPullbackHom Ω f
  exact ((Mod.extendScalarsComp α (coefficientMap a V)).app P).symm ≪≫
    (Mod.extendScalarsIsoOfEq (map_coefficientMap_comp_condensedPullbackHom a f).symm).app P ≪≫
    (Mod.extendScalarsComp ((upperStar Ab.{u + 1} f).map (coefficientMap a T)) β).app P ≪≫
    (Mod.extendScalars β).mapIso e

attribute [local irreducible] normalizedModel

private lemma raw_finite_model_on_immersion_range
    (Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [MonObj Ω] [IsCommMonObj Λ] [IsCommMonObj Ω]
    (a : Λ ⟶ Ω) [IsMonHom a] {T V : Scheme.{u}}
    (f : V ⟶ T) [IsImmersion f]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Ω T))
    (P : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T)))
    (hP : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T)) P)
    (e : (Mod.extendScalars ((upperStar Ab.{u + 1} f).map (coefficientMap a T))).obj P ≅
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Ω T)).obj M))
    {U : Scheme.{u}} (g : U ⟶ T) (hr : Set.range g ⊆ Set.range f) :
    ∃ (Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
      IsLocallyFinitelyPresented (condensedRingObj Λ U) Q ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj Q ≅
        (CondensedRing.upperStar Ω g).obj M) := by
  let N := normalizedModel Λ f P
  have hN := normalizedModel_lfp Λ f P hP
  let eN := normalizedModelIso Λ Ω a f M P e
  exact finite_model_on_immersion_range Λ Ω a f M N hN eN g hr

/-- A nonempty open piece of the support carries the finite coefficient model
coming from the supplied stratification models.

Source: `ModuleObject/Colimit/TwoColimit.lean`, support-induction split.
Proof: pull the stratification back to Y. The union of the interiors of its
strata is dense, hence has a point. The interior of the stratum containing this
point is a nonempty open U. Normalize the given stratum model by its coefficient
comparison isomorphism, transport it along the immersion range to U, and use the
trivial stratification to turn local finite presentation into constructibility.
The scalar-extension comparisons identify the result with the restriction of M.
(auxiliary; not a blueprint node)
-/
theorem exists_nonempty_support_open_piece_model
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
              (padicAlgClRingObj T ℓ)).obj M)))
    (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y]
    :
    ∃ (U : Scheme.{u}) (j : U ⟶ Y), IsOpenImmersion j ∧ Nonempty U ∧
      ∃ (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (padicSubfieldRingObj U ℓ EU)),
        IsConstructibleModuleObject (padicSubfieldRingObj U ℓ EU) PU ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (j ≫ i)).obj M) := by
  obtain ⟨a, U, hU, hr⟩ := exists_nonempty_open_in_stratum S i
  obtain ⟨E, P, hP, ⟨e⟩⟩ := hS a
  obtain ⟨Q, hQ, eQ⟩ := raw_finite_model_on_immersion_range
    (Profinite.continuousMapRingObj E) (Profinite.padicAlgClRingObj ℓ)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (S.immersion a) M P hP e (U.ι ≫ i) hr
  exact ⟨U, U.ι, inferInstance, hU, E, Q, constructible_of_lfp hQ, eQ⟩

end AlgebraicGeometry.ProEtale
