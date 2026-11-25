/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleRestrictionClassCore

/-!
# Constructible representatives of restricted cohomology classes

Source: Stacks Project, Tags 03SA(3) and 03Q5.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A cohomology class in the restriction of a module sheaf comes from a constructible
module sheaf mapping to it. No injectivity or properness is needed.

Source: Stacks Project, Tags 03SA(3) and 03Q5.
(blueprint: lem-weil-pbc-constructible-restriction-class)

Proof: Express F as a small filtered colimit of constructible module sheaves Gₐ by
03SA(3), with cocone maps aₐ : Gₐ → F. Forgetting modules preserves colimits; inverse
image also preserves colimits, and naturally commutes with forgetting modules.
Thus the underlying abelian restriction of F is the filtered colimit of the underlying
abelian restrictions of Gₐ. On the quasi-compact quasi-separated scheme X₀, 03Q5
identifies the cohomology of this colimit with the filtered colimit of their cohomology
groups. Every element of a filtered colimit of abelian groups comes from one stage.
Choose that stage Gₐ and its class z, and take a = aₐ. The canonical cohomology map
from that stage is precisely H^q of the underlying restricted a, giving the equality.
This includes q = 0, zero classes, empty schemes, and the zero coefficient ring. -/
theorem exists_constructible_restriction_class
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q) :
    ∃ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Scheme.IsConstructibleEtaleModuleSheaf G ∧
      ∃ (a : G ⟶ F)
        (z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj G)) q),
        Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map a)) q z = c := by
  classical
  obtain ⟨A, _, hA, D, hD, ι, hι⟩ :=
    Scheme.exists_filtered_colimit_constructible F
  obtain ⟨a, z, hz⟩ := exists_restriction_class_of_filtered_presentation
    (i := i) (Λ := Λ) ι hι q c
  exact ⟨D.obj a, hD a, ι.app a, z, hz⟩

end AlgebraicGeometry.Etale
