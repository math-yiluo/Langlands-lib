/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
import WeilConjectures.AlgebraicGeometry.ModuleAbelianStalkExchange

/-!
# Exchange on total-space cohomology over strictly henselian bases

Source: Stacks Project, Tags 03QO and 03FD, and the stalk-map calculation in the
proof of Tag 095T. This comparison involves total spaces, not closed fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Higher-direct-image stalk exchange over strict local bases is total-space pullback.

Source: Stacks Project, Tag 03QO (exact global sections are the closed-point stalk),
Tag 03FD (module cohomology agrees with underlying abelian cohomology), and
Tag 095T, the paragraph computing the map on stalks.
(blueprint: lem-weil-pbc-strict-local-total-cohomology-exchange)

Proof: the germ isomorphism Gamma(S, J) = J_s for a strictly henselian local
scheme is natural and exact. The inverse-image stalk isomorphism identifies the
stalk at the closed point of B of g^* J with the stalk at the closed point of A
of J: locality ensures that the closed point maps to the closed point, and the
extension between separably closed residue fields does not change this stalk.
Choose an injective module resolution F -> I. Applying f_* and then the exact
closed-point stalk computes the source as the cohomology of Gamma(X, I).
The acyclic comparison of Tag 03FD identifies this with the abelian Ext groups,
without asserting that forgetting modules preserves injectives. Resolve the
exact inverse image g'^* I on X' by an injective module complex J. Applying
f'_* and the exact closed-point stalk computes the target as Gamma(X', J),
hence as the cohomology of the abelian inverse image of F. In degree zero the
unit-square-isomorphism-counit mate pulls a section on X back to X'. The same
calculation term by term, followed by the comparison g'^* I -> J, therefore
induces the usual Ext pullback in every degree. Homotopy uniqueness of the
resolution comparison makes the two identifications compatible with that map.
No properness, torsion, or closed-fibre comparison is used; the argument also
applies to q = 0, the zero ring of coefficients, and empty total spaces. -/
theorem Etale.exists_addEquiv_strictLocal_totalCohomology_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    ∃ (a₁ : ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ)) f q).obj F) ≃+
        Sheaf.H ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
      (a₂ : ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((g')^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q),
      ∀ x, a₂ ((((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap g'
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
          q (a₁ x) := by
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_module_abelian_stalk_exchange
    Λ f f' g' (Spec.map (CommRingCat.ofHom φ)) sq
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) F q
  obtain ⟨a₁, a₂, ha⟩ := Etale.exists_addEquiv_strictLocal_abelian_total_exchange
    φ f f' g' sq
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q
  refine ⟨b₁.trans a₁, b₂.trans a₂, ?_⟩
  intro x
  change a₂ (b₂ _) = Etale.cohomologyMap g' _ q (a₁ (b₁ x))
  rw [hb x]
  exact ha (b₁ x)

end AlgebraicGeometry
