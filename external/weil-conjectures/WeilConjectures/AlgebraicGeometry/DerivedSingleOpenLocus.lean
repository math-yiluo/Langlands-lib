/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.FlatRestrictionUnion
import WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology
import WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # The flat single-cohomology open locus

Source: the cohomology-sheaf gluing paragraph of the perfect-locus proof
(blueprint: lem-pc-derived-single-open-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem isZero_restrict_union {T : Scheme.{u}} (M : T.Modules)
    {ι : Type u} (U : ι → T.Opens) (hU : ∀ a, IsZero (M.restrict (U a).ι)) :
    IsZero (M.restrict (⨆ a, U a).ι) := by
  rw [isZero_restrict_iff]
  intro V hV
  refine ⟨fun s t ↦ ?_⟩
  let R : Sieve V := Sieve.generate (Presieve.ofArrows
    (fun a ↦ V ⊓ U a) (fun a ↦ homOfLE inf_le_left))
  have hR : R ∈ Opens.grothendieckTopology T V := by
    intro x hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp (hV hx)
    exact ⟨V ⊓ U a, homOfLE inf_le_left,
      ⟨_, 𝟙 _, _, Presieve.ofArrows.mk a, Category.id_comp _⟩, ⟨hx, ha⟩⟩
  refine (M.isSheaf_presheaf_comp_forget _ hR).isSeparatedFor.ext fun Z l hl ↦ ?_
  obtain ⟨Y, g, f, hf, rfl⟩ := hl
  obtain ⟨a⟩ := hf
  exact ((isZero_restrict_iff M (U a)).mp (hU a) Z
    ((leOfHom g).trans inf_le_right)).elim _ _

/-- A connective derived object locally concentrated in one finite locally free degree
on a set of points is a flat single object on an open neighbourhood of that set.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, cohomology-sheaf gluing
paragraph; the first step of lem-pc-derived-pullback-single-cohomology.
(blueprint: lem-pc-derived-single-open-locus).

Proof: take W to be the union of all opens satisfying the local hypothesis. Every point
of the given set lies in W. Exact open restriction preserves negative vanishing. In
nonnegative degrees other than i the cohomology sheaves vanish on the covering opens,
hence on W by the sheaf condition. The degree-i sheaf is locally finite free on this
cover and therefore flat: tensoring is exact locally, hence exact globally. Exactness
of open restriction identifies these sheaves with the cohomology of L(W.ι)^* E.
Standard truncations of an object with cohomology in degree i only give its isomorphism
to its degree-i cohomology placed in degree i. This construction uses no uniform rank,
and works on the empty open and with the zero sheaf. -/
theorem exists_flat_single_open_locus
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T : Scheme.{u}} (S : Set T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ S, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    ∃ W : T.Opens, S ⊆ W ∧
      SheafOfModules.IsFlat ((Modules.restrictFunctor W.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E)) ∧
      Nonempty ((AlgebraicGeometry.derivedPullback W.ι).obj E ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj
            ((Modules.restrictFunctor W.ι).obj ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E))) := by
  classical
  let M : ℕ → T.Modules := fun q ↦ (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E
  let A := {U : T.Opens // ∃ r : ℕ,
    IsFiniteLocallyFreeInDegree (fun q ↦ (restrictFunctor U.ι).obj (M q)) i r}
  let U : A → T.Opens := fun a ↦ a.val
  let W : T.Opens := ⨆ a, U a
  have hSW : S ⊆ W := by
    intro t ht
    obtain ⟨V, htV, r, hV⟩ := hloc t ht
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, r, hV⟩, htV⟩
  have hflat := isFlat_restrict_iSup_of_finiteLocallyFree (M i) U (by
    intro a
    obtain ⟨r, hr⟩ := a.property
    exact ⟨r, hr.isFiniteLocallyFreeOfRank⟩)
  have hzero (q : ℕ) (hq : q ≠ i) :
      IsZero ((restrictFunctor W.ι).obj (M q)) := by
    exact isZero_restrict_union (M q) U (fun a ↦ (a.property.choose_spec).isZero q hq)
  let D := (AlgebraicGeometry.derivedPullback W.ι).obj E
  let B := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)
  have hc (n : ℤ) :
      Nonempty ((DerivedCategory.homologyFunctor B n).obj D ≅
        (restrictFunctor W.ι).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E)) :=
    nonempty_homology_derivedOpenPullback_iso_restrict W E n
  have hz (n : ℤ) (hn : n ≠ (i : ℤ)) :
      IsZero ((DerivedCategory.homologyFunctor B n).obj D) := by
    obtain ⟨c⟩ := hc n
    apply IsZero.of_iso _ c
    by_cases hlt : n < 0
    · exact isZero_restrict_of_isZero (hneg n hlt) W
    · have hnat : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      have hneq : n.toNat ≠ i := by omega
      simpa only [M, hnat] using hzero n.toNat hneq
  have : D.IsGE (i : ℤ) := (DerivedCategory.isGE_iff D i).mpr
    (fun n hn ↦ hz n (by omega))
  have : D.IsLE (i : ℤ) := (DerivedCategory.isLE_iff D i).mpr
    (fun n hn ↦ hz n (by omega))
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D i
  obtain ⟨c⟩ := hc i
  let d : N ≅ (restrictFunctor W.ι).obj (M i) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso B (i : ℤ)).app N).symm ≪≫
      (DerivedCategory.homologyFunctor B (i : ℤ)).mapIso e.symm ≪≫ c
  exact ⟨W, hSW, hflat, ⟨e ≪≫ (DerivedCategory.singleFunctor B (i : ℤ)).mapIso d⟩⟩

end AlgebraicGeometry.Scheme.Modules
