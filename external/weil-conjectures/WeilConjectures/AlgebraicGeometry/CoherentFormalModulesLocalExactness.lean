/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionLimits
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Restriction and local exactness of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, Lemma 087X, parts (2) and (3)
(blueprint: lem-weil-pbc-coherent-formal-modules-local-exactness).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem hasHomology_of_nonempty_abelian
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (h : Nonempty (Abelian C)) (S : ShortComplex C) : S.HasHomology := by
  let z : HasZeroMorphisms C := inferInstance
  let hh := @categoryWithHomology_of_abelian C _ h.some
  have hh' : @CategoryWithHomology C _ z := by
    convert hh using 1
    exact Subsingleton.elim _ _
  exact hh'.hasHomology S

private theorem restriction_isZero_of_cover {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (hN : ∀ U : X.Opens, IsNoetherian U.toScheme)
    {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (F : CoherentFormalModule X I)
    (hF : ∀ j, IsZero ((@coherentFormalModulesRestriction X _ I (U j) (hN (U j))).obj F)) :
    IsZero F := by
  have : Abelian (CoherentFormalModule X I) :=
    (coherentFormalModule_abelian X I).1.some
  apply (isIsoZero_iff_source_target_isZero F F).mp ?_ |>.1
  apply (coherentFormalModule_isIso_of_isIso_restrict I U hU (0 : F ⟶ F) ?_).1
  intro j n
  let R := @coherentFormalModulesRestriction X _ I (U j) (hN (U j))
  let E := (IsCoherentFormalModule (I.comap (U j).ι)).ι ⋙
    (evaluation ℕᵒᵖ (U j).toScheme.Modules).obj (op n)
  have hz : IsZero (E.obj (R.obj F)) := E.map_isZero (hF j)
  have hi := (isIsoZero_iff_source_target_isZero (E.obj (R.obj F))
    (E.obj (R.obj F))).mpr ⟨hz, hz⟩
  simpa [E, R, coherentFormalModulesRestriction] using hi

/-- Restriction is the additive functor whose underlying inverse systems and maps are
termwise restrictions. It preserves short exact sequences, and exactness and short
exactness are detected on every open covering. The auxiliary `hz` supplies the proof
of zero preservation needed to form the mapped short complexes, without any new hypothesis.
The witness `hN` states that every open subscheme is Noetherian; `I.comap U.ι` is the restricted
quasi-coherent ideal. The abelian structure is supplied by `coherentFormalModule_abelian`.
Source: Stacks Project, Lemma 087X (2)--(3)
(blueprint: lem-weil-pbc-coherent-formal-modules-local-exactness).

Proof:
1. Construct the actual termwise restriction functor using the object-condition theorem
   coherentFormalModules_restriction_objects. Its full-subcategory lift is additive and
   has the stated equality after inclusion. Opens inherit Noetherianness by Mathlib.
2. coherentFormalModules_restriction_limits supplies finite-limit and finite-colimit
   preservation. Mathlib then gives preservation of short exact sequences and homology.
3. If an object restricts to zero on a cover, its zero endomorphism restricts to an
   isomorphism at every level. coherentFormalModule_isIso_of_isIso_restrict makes this
   zero endomorphism globally invertible, so the object itself is zero.
4. Apply this to the left homology of a short complex. Its restricted left homology
   is zero exactly when the restricted complex is exact; hence exactness is local.
5. Apply the same equivalence to complexes with a zero first or second arrow to detect
   monomorphisms and epimorphisms. Combine these with middle exactness for short exactness. -/
theorem coherentFormalModules_local_exactness (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    ∃ (hN : ∀ U : X.Opens, IsNoetherian U.toScheme)
      (ρ : ∀ U : X.Opens,
        CoherentFormalModule X I ⥤
          @CoherentFormalModule U.toScheme (hN U) (I.comap U.ι))
      (hz : ∀ U : X.Opens, (ρ U).PreservesZeroMorphisms),
      (∀ U : X.Opens, (ρ U).Additive ∧
        ρ U ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
          (IsCoherentFormalModule I).ι ⋙
            (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
              (Scheme.Modules.restrictFunctor U.ι) ∧
        ∀ S : ShortComplex (CoherentFormalModule X I), S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S (ρ U) (hz U)).ShortExact) ∧
      (∀ (J : Type v) (U : J → X.Opens), iSup U = ⊤ →
        ∀ S : ShortComplex (CoherentFormalModule X I),
          (S.Exact ↔ ∀ j : J,
            (@ShortComplex.map _ _ _ _ _ _ S (ρ (U j)) (hz (U j))).Exact) ∧
          (S.ShortExact ↔ ∀ j : J,
            (@ShortComplex.map _ _ _ _ _ _ S (ρ (U j)) (hz (U j))).ShortExact)) := by
  classical
  let hN : ∀ U : X.Opens, IsNoetherian U.toScheme := fun U ↦ by
    have : TopologicalSpace.NoetherianSpace U.toScheme :=
      (Scheme.Hom.isOpenEmbedding U.ι).isInducing.noetherianSpace
    exact {
      toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let R := fun U : X.Opens ↦ @coherentFormalModulesRestriction X _ I U (hN U)
  have hAdd : ∀ U, (R U).Additive := fun U ↦ inferInstance
  have hz : ∀ U, (R U).PreservesZeroMorphisms := fun U ↦ inferInstance
  have hlim : ∀ U, PreservesFiniteLimits (R U) := fun U ↦
    (@coherentFormalModules_restriction_limits X _ I U (hN U)).1
  have hcolim : ∀ U, PreservesFiniteColimits (R U) := fun U ↦
    (@coherentFormalModules_restriction_limits X _ I U (hN U)).2
  have : HasZeroObject (CoherentFormalModule X I) := by
    have : Abelian (CoherentFormalModule X I) :=
      (coherentFormalModule_abelian X I).1.some
    infer_instance
  have hzero : ∀ U : X.Opens,
      HasZeroObject (@CoherentFormalModule U.toScheme (hN U) (I.comap U.ι)) := fun U ↦ by
    have : Abelian (@CoherentFormalModule U.toScheme (hN U) (I.comap U.ι)) :=
      (@coherentFormalModule_abelian U.toScheme (hN U) (I.comap U.ι)).1.some
    infer_instance
  refine ⟨hN, R, hz, ?_, ?_⟩
  · intro U
    refine ⟨hAdd U, rfl, ?_⟩
    intro S hS
    exact hS.map_of_exact (R U)
  · intro J U hU
    have hex : ∀ S : ShortComplex (CoherentFormalModule X I),
        S.Exact ↔ ∀ j : J, (S.map (R (U j))).Exact := by
      intro S
      have : S.HasHomology :=
        hasHomology_of_nonempty_abelian (coherentFormalModule_abelian X I).1 S
      constructor
      · intro h j
        exact h.map (R (U j))
      · intro h
        apply S.leftHomologyData.exact_iff.mpr
        apply restriction_isZero_of_cover I hN U hU
        intro j
        exact (S.leftHomologyData.exact_map_iff (R (U j))).mp (h j)
    intro S
    refine ⟨hex S, ?_⟩
    constructor
    · intro h j
      exact h.map_of_exact (R (U j))
    · intro h
      have hf : Mono S.f := by
        let T := ShortComplex.mk (0 : S.X₁ ⟶ S.X₁) S.f (by simp)
        apply (T.exact_iff_mono rfl).mp
        apply (hex T).mpr
        intro j
        have := (h j).mono_f
        exact ((T.map (R (U j))).exact_iff_mono (by simp [T])).mpr (by simpa [T] using (h j).mono_f)
      have hg : Epi S.g := by
        let T := ShortComplex.mk S.g (0 : S.X₃ ⟶ S.X₃) (by simp)
        apply (T.exact_iff_epi rfl).mp
        apply (hex T).mpr
        intro j
        have := (h j).epi_g
        exact ((T.map (R (U j))).exact_iff_epi (by simp [T])).mpr (by simpa [T] using (h j).epi_g)
      exact ShortComplex.ShortExact.mk' ((hex S).mpr (fun j ↦ (h j).exact)) hf hg

end AlgebraicGeometry
