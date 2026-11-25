/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Constructible subobject presentations

Source: Stacks Project, Tags 03SA(3), 09BH(3), and 03SC, first proof paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every module sheaf on a Noetherian scheme over a finite ring is a filtered union
of constructible module subsheaves.
Source: Stacks Project, Tags 03SA(3), 09BH(3), and 03SC, first proof paragraph.
(blueprint: lem-pbc-u2-constructible-subobject-presentation)

Proof: Use the filtered constructible presentation of Tag 03SA(3), converting its
constructibility convention by the finite-ring comparison. Replace each map to F by
its image. Its kernel is constructible by the Noetherian module-subobject theorem;
its image, the cokernel of that kernel inclusion, is constructible by constructible
cokernel closure. A commuting triangle into F induces a unique transition between
images, and uniqueness gives a functor and a natural cocone of monomorphisms.
This cocone is colimiting: compatible maps from images compose with the epimorphisms
from the original stages to give a compatible family, hence a map from F. The
resulting map restricts to the prescribed image maps, by cancellation of those
epimorphisms; uniqueness follows from the original colimit. The original filtered
index remains unchanged, including its zero stage. This handles zero rings, zero
sheaves, and empty schemes without requiring nonzero sections. -/
theorem exists_filtered_colimit_constructible_subobjects
    {X : Scheme.{u}} [IsNoetherian X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const A).obj F),
      (∀ a, IsConstructibleSheaf (D.obj a)) ∧
      (∀ a, Mono (ι.app a)) ∧ Nonempty (IsColimit (Cocone.mk F ι)) := by
  classical
  obtain ⟨A, hA, hfiltered, D, hD, ι, ⟨hc⟩⟩ := exists_filtered_colimit_constructible F
  let := hA
  let := hfiltered
  let E : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    { obj := fun a ↦ image (ι.app a)
      map := fun {a b} φ ↦ image.map (Arrow.homMk' (D.map φ) (𝟙 F)
        (by simp [ι.naturality φ]))
      map_id := by
        intro a
        apply (cancel_mono (image.ι (ι.app a))).mp
        rw [image.map_homMk'_ι, Category.comp_id]
        exact (Category.id_comp _).symm
      map_comp := by
        intro a b c φ ψ
        apply (cancel_mono (image.ι (ι.app c))).mp
        simp only [Category.assoc, image.map_homMk'_ι, Category.comp_id] }
  let ε : E ⟶ (Functor.const A).obj F :=
    { app := fun a ↦ image.ι (ι.app a)
      naturality := by
        intro a b φ
        exact image.map_ι _ }
  let π : D ⟶ E :=
    { app := fun a ↦ factorThruImage (ι.app a)
      naturality := by
        intro a b φ
        dsimp only [E]
        exact (image.factor_map (Arrow.homMk' (D.map φ) (𝟙 F)
          (by simp [ι.naturality φ]))).symm }
  have hE (a : A) : IsConstructibleSheaf (E.obj a) := by
    have : IsConstructibleSheaf (D.obj a) :=
      (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (D.obj a)).mp (hD a)
    have : IsNoetherianRing Λ := inferInstance
    have : IsConstructibleSheaf (kernel (ι.app a)) :=
      constructible_of_mono_noetherian (kernel.ι (ι.app a))
    have : IsConstructibleSheaf (cokernel (kernel.ι (ι.app a))) :=
      IsConstructibleSheaf.cokernel (kernel.ι (ι.app a))
    exact IsConstructibleSheaf.of_iso (Abelian.coimageIsoImage' (ι.app a))
  refine ⟨A, hA, hfiltered, E, ε, hE, ?_, ?_⟩
  · intro a
    exact inferInstanceAs (Mono (image.ι (ι.app a)))
  · refine ⟨?_⟩
    refine
      { desc := fun s ↦ hc.desc { pt := s.pt, ι := π ≫ s.ι }
        fac := ?_
        uniq := ?_ }
    · intro s a
      apply (cancel_epi (factorThruImage (ι.app a))).mp
      change factorThruImage (ι.app a) ≫ image.ι (ι.app a) ≫ _ =
        factorThruImage (ι.app a) ≫ s.ι.app a
      rw [← Category.assoc, image.fac]
      exact hc.fac _ a
    · intro s m hm
      apply hc.hom_ext
      intro a
      rw [hc.fac]
      change ι.app a ≫ m = factorThruImage (ι.app a) ≫ s.ι.app a
      calc
        _ = (factorThruImage (ι.app a) ≫ image.ι (ι.app a)) ≫ m :=
          congrArg (fun z ↦ z ≫ m) (image.fac (ι.app a)).symm
        _ = _ := by
          rw [Category.assoc]
          exact congrArg (fun z ↦ factorThruImage (ι.app a) ≫ z) (hm a)

end AlgebraicGeometry.Scheme
