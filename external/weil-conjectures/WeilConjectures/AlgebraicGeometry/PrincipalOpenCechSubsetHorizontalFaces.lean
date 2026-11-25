/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetRowReassembly
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate

/-! # Ordered horizontal faces of a single principal-open subset

Source: Stacks Project, Tags 08C1, 08C0, and 01FG.
(blueprint: lem-sc-principal-open-cech-subset-horizontal-faces).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance] Classical.propDecidable

/-- Ordered face calculation for one supported tuple, followed by total inclusion.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1) (Tag 08C0), and
Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-horizontal-faces).

Proof: At a target increasing tuple t, expand alternatingCechDifferential as the
sum of restrictions from faces obtained by deleting each position k. The supported
source tuple vanishes unless the face has range S₀. Increasing order embeddings
with the same range agree. Identify each target tuple with the increasing
enumeration of its range T. The position of j in this enumeration is the number
of elements of T smaller than j, giving the exponent in the statement.
Presheaf functoriality and naturality of overFunctorEquiv move section transport
past each face restriction; the open maps agree because opens form a thin category.
The supplied degree equality identifies the source coefficient with J.X q in
precisely the nonzero terms. Reassemble the target tuple product, apply the inverse
extension isomorphism, and include bidegree (p+1,q) in the total. Other subset
cardinalities have zero coefficients because their deleted subset cannot equal S₀.
For singleton targets every deletion is empty and contributes zero. For r=0 there
is no nonempty source subset, so the assertion is vacuous. -/
theorem principalSubsetHorizontalFaces
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let D := principalSubsetOpen A r f
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (S₀ : {S : Finset (Fin r) // S.Nonempty})
      (x : (modulesSpecToSheaf.obj (J.X (n + 1 - (S₀.val.card : ℤ)))).obj.obj
        (op (D S₀.val))),
      let p := S₀.val.card - 1
      let q := n + 1 - (S₀.val.card : ℤ)
      let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
      let L := alternatingCechComplex U P
      let e : (K.X ((p + 1 : ℕ) : ℤ)).X q ≅ L.X (p + 1) :=
        L.extendXIso ComplexShape.embeddingUpNat rfl
      ∀ (hdeg : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (((p + 1 : ℕ) : ℤ), q) = n + 1),
      (H.map (e.inv ≫ K.ιTotal (ComplexShape.up ℤ) ((p + 1 : ℕ) : ℤ) q (n + 1) hdeg))
        ((alternatingCechDifferential U P p).hom
          (Pi.single (principalSubsetTuple r S₀)
            ((principalSubsetSectionTransport A r f (J.X q) S₀).hom x))) =
      principalSubsetInsertion A r f J (n + 1) (fun S ↦
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val)))
                    ((Pi.single S₀ x : principalSubsetCoordinates A r f J n)
                      ⟨S.val.erase j.val, h⟩))
          else 0) := by
  classical
  intro V U K H D hle he n S₀ x p q P L e hdeg
  apply principalSubsetRowReassembly A r f J (n + 1) (p + 1) q hdeg
  · intro S hcard
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · have hne : (⟨S.val.erase j.val, h⟩ :
          {S : Finset (Fin r) // S.Nonempty}) ≠ S₀ := by
        intro heq
        have hv := congrArg Subtype.val heq
        have hc := Finset.card_erase_of_mem j.property
        have hp := S₀.property.card_pos
        dsimp only [p] at hcard
        change S.val.erase j.val = S₀.val at hv
        rw [hv] at hc
        omega
      rw [Pi.single_eq_of_ne hne, map_zero, map_zero, smul_zero]
    · rfl
  · intro S hcard
    exact principalSubsetHorizontalFaceCoordinate A r f J hle he n S₀ x S hcard


end AlgebraicGeometry
