/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Total derived scalar extension computed on resolutions

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

/-- Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, and Tag 06XN.
(blueprint: lem-pc-base-derived-extension-resolution).

Proof: Take K-flat resolutions of all R-complexes. Tensoring a quasi-isomorphism
between K-flat complexes with B in degree zero is a quasi-isomorphism, by the
fixed-second-factor derived tensor construction. Termwise extension is triangulated
on the homotopy category. Apply the resolving-class left-derived construction to
obtain L and its counit, invertible on K-flat models. Every E has a quasi-isomorphism
P to E with P K-flat, giving the last clause. For unequal ring universes, lift both
rings to the common carrier universe. The restriction equivalences along the ring
isomorphisms preserve complexes and quasi-isomorphisms and intertwine extension of
scalars by the tensor universal property. Transport the universal pair, its shift
structure and triangulatedness back along these equivalences. The counit comparison
on a transported resolution stays invertible. This argument works for unbounded
complexes, zero rings and zero complexes; no flatness of B over R is assumed. -/
theorem exists_baseDerivedExtension_resolution
    [(extendScalars.{_, _, max uR uB v} (algebraMap R B)).Additive] :
    ∃ (L : DerivedCategory (ModuleCat.{max uR uB v} R) ⥤
        DerivedCategory (ModuleCat.{max uR uB v} B))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{max uR uB v} R) (.up ℤ)) ∧
      (∃ c : L.CommShift ℤ, letI := c; L.IsTriangulated) ∧
      ∀ E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ,
        ∃ (P : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (s : P ⟶ E),
          QuasiIso s ∧ IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) := by
  classical
  let C := ModuleCat.{max uR uB v} R
  let D := ModuleCat.{max uR uB v} B
  let H := HomotopyCategory.quotient C (.up ℤ)
  let G := (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory
    (.up ℤ) ⋙ (DerivedCategory.Qh : HomotopyCategory D (.up ℤ) ⥤ _)
  let S : Set (HomotopyCategory C (.up ℤ)) :=
    {X | ∃ K : CochainComplex C ℤ, K.IsKProjective ∧ H.obj K = X}
  have hresolution (E : CochainComplex C ℤ) :
      ∃ (K : CochainComplex C ℤ) (s : K ⟶ E), QuasiIso s ∧ K.IsKProjective := by
    obtain ⟨K, s, hs, F, ι, step, hz, hm, hc, he, hsp, hq⟩ :=
      CochainComplex.exists_large_filtered_free_resolution.{uR, max uB v} E
    exact ⟨K, s, hs,
      CochainComplex.isKProjective_of_filtered_free K F ι step hz hm hc he hsp hq⟩
  have hres (X : HomotopyCategory C (.up ℤ)) :
      ∃ (X' : HomotopyCategory C (.up ℤ)) (s : X' ⟶ X),
        X' ∈ S ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨E, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨K, s, hs, hK⟩ := hresolution E
    refine ⟨H.obj K, H.map s, ⟨K, hK, rfl⟩, ?_⟩
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    exact hs
  have hinv (X Y : HomotopyCategory C (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ S) (hY : Y ∈ S)
      (hs : HomotopyCategory.quasiIso C (.up ℤ) s) : IsIso (G.map s) := by
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨K', hK', rfl⟩ := hY
    let := hK
    let := hK'
    obtain ⟨a, rfl⟩ := H.map_surjective s
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] at hs
    have ha := (CochainComplex.IsKProjective.quasiIso_iff a).1 hs
    have : IsIso (H.map a) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences a).2 ha
    infer_instance
  obtain ⟨_, L, ε, hL, htri, hcompute⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) G S hres hinv
  refine ⟨L, ε, hL, htri, ?_⟩
  intro E
  obtain ⟨K, s, hs, hK⟩ := hresolution E
  exact ⟨K, s, hs, hcompute (H.obj K) ⟨K, hK, rfl⟩⟩

end ModuleCat
