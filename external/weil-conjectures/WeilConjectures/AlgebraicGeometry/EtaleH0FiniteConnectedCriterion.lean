/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-!
# A finite-cover connectedness criterion for étale module sections

Source: Stacks Project, Tags 09ZG and 09ZF, the spectral restriction lemma and
Gabber's degree-zero criterion.
(blueprint: lem-weil-pbc-etale-module-h0-finite-connected-criterion).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Restriction of étale module sections to a closed subscheme is an isomorphism if
all irreducible closed subsets of every finite cover meet that subscheme in a
nonempty connected subset.

Source: Stacks Project, Lemmas 59.82.4 and 59.82.2 (Tags 09ZG and 09ZF).
(blueprint: lem-weil-pbc-etale-module-h0-finite-connected-criterion).

Proof: A finite scheme X' over the quasi-compact, quasi-separated X is again
quasi-compact and quasi-separated, hence spectral. The base change of i is a closed
immersion, with image h⁻¹(range i). Tag 09ZG applied to this spectral space and closed
subset gives bijective restriction on global sections of every Zariski sheaf of
sets. The connectedness assumption includes nonemptiness. For X itself use h = id;
for every finite cover use the corresponding h. Tag 09ZF now gives bijective
restriction for every étale sheaf of sets on X.

Apply this to the underlying sheaf of sets of F. Forgetting module structure commutes
with inverse image: presheaf inverse image is computed by filtered colimits, which the
module forgetful functor preserves, and sheafification is computed by local matching
families, whose module operations are pointwise. These identifications carry the
adjunction unit to the set-valued adjunction unit. Evaluation at the terminal étale
object and the canonical terminal-base-change isomorphism therefore identify the
underlying function of globalSectionsUpperStarMap with the bijection of Tag 09ZF,
up to bijective identifications of its source and target. A bijective module
homomorphism has a module-linear inverse, so the restriction map is an isomorphism.
The set-valued statements here use Type (u + 1), the universe of the underlying
modules; the spectral restriction argument is independent of the value universe. -/
theorem isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hconn : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      ∀ C : Set X', IsClosed C → IsIrreducible C →
        IsConnected (C ∩ h ⁻¹' Set.range i))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let G := (sheafCompose X.smallEtaleTopology U).obj F
  have hG :=
    isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
      i hconn G
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F
  let θ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G
  have hθ : IsIso (θ.hom.app (Opposite.op (⊤_ X.Etale))) := by
    unfold globalSectionsUpperStarMap at hG
    have h' : IsIso (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op (⊤_ X.Etale))).map θ) := by
      simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hG
    exact h'
  let H := (sheafCompose Z.smallEtaleTopology U).obj
    ((i)^*[ModuleCat.{u + 1} Λ].obj F)
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i
  let c := (adj.homEquiv G H).symm
    ((sheafCompose X.smallEtaleTopology U).map η)
  have : IsIso c := isIso_moduleAbelianInverseImageComparison i Λ F
  have hw : θ ≫ (i)_*[AddCommGrpCat.{u + 1}].map c =
      (sheafCompose X.smallEtaleTopology U).map η := by
    exact ((adj.homEquiv G H).apply_symm_apply
      ((sheafCompose X.smallEtaleTopology U).map η) : _).trans rfl
  have hw' := congrArg (fun f ↦ f.hom.app (Opposite.op (⊤_ X.Etale))) hw
  change θ.hom.app (Opposite.op (⊤_ X.Etale)) ≫
    ((i)_*[AddCommGrpCat.{u + 1}].map c).hom.app
      (Opposite.op (⊤_ X.Etale)) = U.map (η.hom.app (Opposite.op (⊤_ X.Etale))) at hw'
  have : IsIso (U.map (η.hom.app (Opposite.op (⊤_ X.Etale)))) := by
    rw [← hw']
    infer_instance
  have : IsIso (η.hom.app (Opposite.op (⊤_ X.Etale))) :=
    isIso_of_reflects_iso _ U
  have : IsIso (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (Opposite.op (⊤_ X.Etale))).map η) := ‹IsIso (η.hom.app _)›
  have : IsIso (((i)^*[ModuleCat.{u + 1} Λ].obj F).obj.map
      (PreservesTerminal.iso i.Etale).inv.op) := by infer_instance
  unfold globalSectionsUpperStarMap
  infer_instance

end AlgebraicGeometry.Etale
