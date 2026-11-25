/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionVertical
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionHorizontal

/-! # Properties of explicit subset insertion

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Totalization has the displayed differential on the explicit subset insertion.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-insertion-differential).

Proof: Expand the insertion as a finite sum and distribute the total differential.
On the column p=card S-1 its vertical part is (-1)^p times the coefficient differential.
Naturality of restriction and section transport identifies this with the vertical
term displayed below. Its horizontal part is the signed face restriction. A face
of the increasing enumeration deletes j, and its position is the number of elements
of the target subset smaller than j. Regroup the finite sum by target subsets.
Transport coefficient degrees with he; proof irrelevance identifies all equality
transports. Empty deletions contribute zero because there is no negative column.
For each source subset, the two contributions agree in every target tuple coordinate.
Reassemble those coordinates using their total summand inclusions. Every source element
is the finite sum of its single-coordinate elements, so additivity proves the equality
for arbitrary s. Zero summands and the empty cover cause no exception. -/
theorem principalSubsetInsertion_differential
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let D := principalSubsetOpen A r f
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (s : principalSubsetCoordinates A r f J n),
      (principalSubsetTotal A r f J).d n (n + 1)
        (principalSubsetInsertion A r f J n s) =
      principalSubsetInsertion A r f J (n + 1) (fun S ↦
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) (s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) (s ⟨S.val.erase j.val, h⟩))
          else 0) := by
  classical
  intro D hle he n s
  let V := principalSubsetUnion A r f
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
  let H := forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  change (H.map ((K.total (ComplexShape.up ℤ)).d n (n + 1)))
    (principalSubsetInsertion A r f J n s) = _
  rw [HomologicalComplex₂.total_d, H.map_add]
  change (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
      (principalSubsetInsertion A r f J n s) +
    (H.map (K.D₂ (ComplexShape.up ℤ) n (n + 1)))
      (principalSubsetInsertion A r f J n s) = _
  rw [principalSubsetInsertion_horizontal A r f J hle he n s,
    principalSubsetInsertion_vertical A r f J n s]
  exact (add_comm _ _).trans ((map_add (principalSubsetInsertion A r f J (n + 1)).hom
    _ _).symm)


end AlgebraicGeometry
