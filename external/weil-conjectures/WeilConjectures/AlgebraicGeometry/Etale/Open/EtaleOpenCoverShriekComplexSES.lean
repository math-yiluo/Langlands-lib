/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekNaturalSES

/-! # The termwise extension-by-zero short exact sequence

Source: Stacks Project, Tag 0GKK, proof of `lemma-mayer-vietoris-shriek`.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The short exact complex before passage to the derived category.
Source: Stacks Project, Tag 0GKK, proof of `lemma-mayer-vietoris-shriek`.
(blueprint: lem-weil-pbc-etale-open-cover-shriek-complex-ses).

Proof: For each degree of L take the canonical nested-open extension maps
from the intersection, with a negative sign on the V component, and the
sum of the two extension-by-zero counits. Naturality makes these maps of
complexes. The composite is zero because the composites of the two nested
maps with their respective counits are both the intersection counit.
On a geometric stalk in both opens the sequence is diagonal difference
followed by addition; in precisely one open it is the identity sequence
on the only nonzero summand. The covering assumption excludes the fourth
case. Thus the sheaf sequence in each degree is short exact by exactness
and conservativity of geometric stalks, and degreewise short exactness
is short exactness in the abelian category of complexes. Empty opens,
coincident opens, and the zero ring give the same exact stalk sequences.
-/
theorem exists_shortExact_openCover_lowerShriek_complex
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    let E (T : X.Opens) :=
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
    ∃ (α : E (U ⊓ V) ⟶ E U ⊞ E V) (β : E U ⊞ E V ⟶ L) (hz : α ≫ β = 0),
      (ShortComplex.mk α β hz).ShortExact := by
  obtain ⟨tU, tV, hS⟩ := exists_natural_shortExact_openCover_lowerShriek Λ U V hcover
  let E (T : X.Opens) :=
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
  let iU : E (U ⊓ V) ⟶ E U :=
    { f := fun n ↦ tU.app (L.X n)
      comm' := fun i j _ ↦ (tU.naturality (L.d i j)).symm }
  let iV : E (U ⊓ V) ⟶ E V :=
    { f := fun n ↦ tV.app (L.X n)
      comm' := fun i j _ ↦ (tV.naturality (L.d i j)).symm }
  let ε (T : X.Opens) : E T ⟶ L :=
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app L
  have hz : biprod.lift iU (-iV) ≫ biprod.desc (ε U) (ε V) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (biprod.lift iU (-iV) ≫ biprod.desc (ε U) (ε V)).f n = 0
    rw [biprod.lift_desc]
    change tU.app (L.X n) ≫ _ + (-(tV.app (L.X n))) ≫ _ = 0
    simpa only [biprod.lift_desc, ε,
      Adjunction.mapHomologicalComplex_counit_app_f] using (hS (L.X n)).choose
  refine ⟨biprod.lift iU (-iV), biprod.desc (ε U) (ε V), hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨hzn, hn⟩ := hS (L.X n)
  let Q := HomologicalComplex.eval
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ) n
  let e := Q.mapBiprod (E U) (E V)
  apply ShortComplex.shortExact_of_iso _ hn
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · change Q.map (biprod.lift iU (-iV)) =
      biprod.lift (Q.map iU) (-(Q.map iV)) ≫ e.inv
    simpa only [Functor.map_neg] using
      (biprod.lift_mapBiprod Q (E U) (E V) iU (-iV)).symm
  · change e.inv ≫ Q.map (biprod.desc (ε U) (ε V)) =
      biprod.desc (Q.map (ε U)) (Q.map (ε V))
    exact biprod.mapBiprod_inv_map_desc Q (E U) (E V) (ε U) (ε V)

end AlgebraicGeometry.Etale
