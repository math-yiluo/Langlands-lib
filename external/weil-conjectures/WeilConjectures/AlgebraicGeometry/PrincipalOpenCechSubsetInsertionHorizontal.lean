/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaces

/-! # Horizontal differential of explicit subset insertion

Source: Stacks Project, Tag 08C1 and equation (20.40.0.1) (Tag 08C0),
and Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-insertion-horizontal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem sum_apply {α : Type*} [Fintype α]
    {G H : AddCommGrpCat.{u}} (F : α → (G ⟶ H)) (x : G) :
    (∑ i, F i) x = ∑ i, F i x := by
  change (AddCommGrpCat.homAddEquiv (∑ i, F i)) x = _
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rfl

private theorem principalSubsetInsertOne_horizontal
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
      (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
        (principalSubsetInsertOne A r f J n S₀ x) =
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
  intro V U K H D hle he n S₀ x
  let p : ℕ := S₀.val.card - 1
  let q : ℤ := n + 1 - (S₀.val.card : ℤ)
  let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
  let L := alternatingCechComplex U P
  let e : (K.X (p : ℤ)).X q ≅ L.X p :=
    L.extendXIso ComplexShape.embeddingUpNat rfl
  let e' : (K.X ((p + 1 : ℕ) : ℤ)).X q ≅ L.X (p + 1) :=
    L.extendXIso ComplexShape.embeddingUpNat rfl
  let v : AddCommGrpCat.of
      (P.obj (op (alternatingCechIntersection U (principalSubsetTuple r S₀)))) ⟶
      H.obj (L.X p) :=
    AddCommGrpCat.ofHom (AddMonoidHom.single
      (fun t : Fin (p + 1) ↪o Fin r ↦ P.obj (op (alternatingCechIntersection U t)))
        (principalSubsetTuple r S₀))
  have hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((p : ℤ), q) = n := by
    change (p : ℤ) + q = n
    dsimp [p, q]
    rw [Nat.cast_sub (by have := S₀.property.card_pos; omega)]
    push_cast
    omega
  have hpq' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (((p + 1 : ℕ) : ℤ), q) = n + 1 := by
    change ((p + 1 : ℕ) : ℤ) + q = n + 1
    change (p : ℤ) + q = n at hpq
    push_cast
    omega
  change (((principalSubsetSectionTransport A r f (J.X q) S₀).hom ≫ v ≫
    H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q n hpq) ≫
      H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1))) x) = _
  with_unfolding_all
    simp only [← H.map_comp, HomologicalComplex₂.ι_D₁]
  with_unfolding_all
    rw [K.d₁_eq (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel (p : ℤ) ((p + 1 : ℕ) : ℤ) by
        change (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ); omega) q (n + 1) hpq']
  have hd : (K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).f q =
      e.hom ≫ alternatingCechDifferential U P p ≫ e'.inv := by
    change (L.extend ComplexShape.embeddingUpNat).d (p : ℤ) ((p + 1 : ℕ) : ℤ) = _
    have h := L.extend_d_eq ComplexShape.embeddingUpNat
      (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) (i := p) (j := p + 1) rfl rfl
    change _ = e.hom ≫ L.d p (p + 1) ≫ e'.inv at h
    have hL : L.d p (p + 1) = alternatingCechDifferential U P p := by
      simp only [L, alternatingCechComplex, CochainComplex.of_d]
    rw [hL] at h
    exact h
  have hε : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((p : ℤ), q) = 1 := rfl
  with_unfolding_all
    rw [hd, hε, one_smul]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact principalSubsetHorizontalFaces A r f J hle he n S₀ x hpq'

/-- The horizontal total differential on explicit subset coordinates.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1) (Tag 08C0), and
Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-insertion-horizontal).

Proof: Expand insertion as its finite sum, and apply Mathlib's `ι_D₁` and
`d₁_eq` to each summand. Its horizontal sign is one. Extension by zero identifies
the horizontal map with alternatingCechDifferential, whose target tuple coordinate
is the signed sum of restrictions from the tuples obtained by deleting one entry.
Increasing tuples are uniquely determined by their ranges. For the increasing
enumeration of a target subset S, deleting the position occupied by j gives the
increasing enumeration of S.erase j. That position is exactly the cardinality of
the elements of S smaller than j. Section transport commutes with restrictions:
compose the open equality maps and use functoriality of the presheaf, naturality
of restriction, and the natural isomorphism overFunctorEquiv. The resulting open
map is the one from hle, since opens form a thin category. Use he to identify the
coefficient degrees, and proof irrelevance to identify the equality transports.
Regroup the finite sums by target subsets, and reassemble the tuple coordinates
using the total inclusions. For singleton targets the erased set is empty: the
source column would be negative and is zero by extension. For an empty cover
all sums are zero. These cover the boundary cases without a coefficient bound. -/
theorem principalSubsetInsertion_horizontal
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
      (n : ℤ) (s : principalSubsetCoordinates A r f J n),
      (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
        (principalSubsetInsertion A r f J n s) =
      principalSubsetInsertion A r f J (n + 1) (fun S ↦
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) (s ⟨S.val.erase j.val, h⟩))
          else 0) := by
  classical
  intro V U K H D hle he n s
  let b : principalSubsetCoordinates A r f J n →+
      principalSubsetCoordinates A r f J (n + 1) :=
    { toFun := fun s S ↦
        ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
          (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
            (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
              (homOfLE (hle S.val j.val)).op
              ((modulesSpecToSheaf.map
                (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                  (op (D (S.val.erase j.val))) (s ⟨S.val.erase j.val, h⟩))
        else 0
      map_zero' := by
        funext S
        apply Finset.sum_eq_zero
        intro j _
        split_ifs with h
        · rw [show (0 : principalSubsetCoordinates A r f J n)
              ⟨S.val.erase j.val, h⟩ = 0 from rfl]
          simp only [map_zero, smul_zero]
        · rfl
      map_add' := by
        intro s t
        funext S
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp [map_add, smul_add] }
  change (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
    (principalSubsetInsertion A r f J n s) =
      principalSubsetInsertion A r f J (n + 1) (b s)
  have hs : (∑ S, Pi.single S (s S) : principalSubsetCoordinates A r f J n) = s := by
    funext T
    simp
  change ((principalSubsetInsertion A r f J n ≫
    H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1))) s) = _
  simp only [principalSubsetInsertion, Preadditive.sum_comp, Category.assoc]
  with_unfolding_all
    rw [sum_apply]
  change (∑ S, (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
    (principalSubsetInsertOne A r f J n S (s S))) =
      principalSubsetInsertion A r f J (n + 1) (b s)
  calc
    _ = ∑ S, principalSubsetInsertion A r f J (n + 1) (b (Pi.single S (s S))) := by
      apply Finset.sum_congr rfl
      intro S _
      exact principalSubsetInsertOne_horizontal A r f J hle he n S (s S)
    _ = _ := by
      rw [← map_sum (principalSubsetInsertion A r f J (n + 1)).hom,
        ← map_sum b, hs]

end AlgebraicGeometry
