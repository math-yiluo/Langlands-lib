/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionTransport
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Data.Finset.Sort

/-! # Explicit insertion of subset coordinates into the tuple total

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

noncomputable section

variable (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)

/-- The union of the indexed principal opens. -/
abbrev principalSubsetUnion : (Spec (.of A)).Opens :=
  ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)

/-- The basic open associated with a subset of indices. -/
abbrev principalSubsetOpen (S : Finset (Fin r)) : (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (∏ j ∈ S, f j)

theorem basicOpen_finset_prod (S : Finset (Fin r)) :
    PrimeSpectrum.basicOpen (∏ j ∈ S, f j) = ⨅ j ∈ S, PrimeSpectrum.basicOpen (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.basicOpen_mul, ih]
    simpa only [Finset.mem_insert, Set.mem_insert_iff, Finset.mem_coe] using
      (iInf_insert (s := (S : Set (Fin r))) (b := j)
        (f := fun i ↦ PrimeSpectrum.basicOpen (f i))).symm

theorem principalSubsetOpen_le (S : {S : Finset (Fin r) // S.Nonempty}) :
    principalSubsetOpen A r f S.val ≤ principalSubsetUnion A r f := by
  obtain ⟨j, hj⟩ := S.property
  change PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j) ≤ _
  rw [basicOpen_finset_prod]
  exact (iInf_le_of_le j (iInf_le _ hj)).trans (le_iSup (fun i ↦
    PrimeSpectrum.basicOpen (f i)) j)

/-- The increasing enumeration of a nonempty subset. -/
def principalSubsetTuple (S : {S : Finset (Fin r) // S.Nonempty}) :
    Fin (S.val.card - 1 + 1) ↪o Fin r :=
  S.val.orderEmbOfFin (by have := S.property.card_pos; omega)

theorem principalSubsetIntersection
    (S : {S : Finset (Fin r) // S.Nonempty}) :
    alternatingCechIntersection
      (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
      (principalSubsetTuple r S) =
        (principalSubsetUnion A r f).ι ⁻¹ᵁ principalSubsetOpen A r f S.val := by
  classical
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ ((↑(⨅ k, (principalSubsetUnion A r f).ι ⁻¹ᵁ
    PrimeSpectrum.basicOpen (f ((principalSubsetTuple r S) k)))) : Set _) ↔
    x ∈ ((↑((principalSubsetUnion A r f).ι ⁻¹ᵁ
      PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j))) : Set _)
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  change (∀ k, (principalSubsetUnion A r f).ι x ∈
    PrimeSpectrum.basicOpen (f ((principalSubsetTuple r S) k))) ↔
    (principalSubsetUnion A r f).ι x ∈ PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j)
  rw [basicOpen_finset_prod]
  change _ ↔ (principalSubsetUnion A r f).ι x ∈
    ((↑(⨅ j ∈ S.val, PrimeSpectrum.basicOpen (f j))) : Set (PrimeSpectrum A))
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro h j
    by_cases hj : j ∈ S.val
    · rw [iInf_pos hj]
      obtain ⟨k, hk⟩ := (Finset.range_orderEmbOfFin S.val
        (show S.val.card = S.val.card - 1 + 1 by have := S.property.card_pos; omega)).ge hj
      exact hk ▸ h k
    · rw [iInf_neg hj]
      exact Set.mem_univ _
  · intro h k
    have hx := h ((principalSubsetTuple r S) k)
    have ht : (principalSubsetTuple r S) k ∈ S.val :=
      Finset.orderEmbOfFin_mem _ _ k
    rw [iInf_pos ht] at hx
    exact hx

/-- Restrict a coefficient section to the tuple intersection. All maps are explicit. -/
def principalSubsetSectionTransport
    (M : (Spec (.of A)).Modules) (S : {S : Finset (Fin r) // S.Nonempty}) :
    AddCommGrpCat.of ((modulesSpecToSheaf.obj M).obj.obj
      (op (principalSubsetOpen A r f S.val))) ≅
    AddCommGrpCat.of
      (((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
        (principalSubsetUnion A r f) ⋙
          (Scheme.Modules.overEquiv (principalSubsetUnion A r f)).functor).obj M).val.obj
        (op (alternatingCechIntersection
          (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
          (principalSubsetTuple r S)))) := by
  let V := principalSubsetUnion A r f
  let W := alternatingCechIntersection
    (fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) (principalSubsetTuple r S)
  have hW : V.ι ''ᵁ W = principalSubsetOpen A r f S.val := by
    dsimp only [W, V]
    rw [principalSubsetIntersection, V.ι.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (principalSubsetOpen_le A r f S)]
  exact M.presheaf.mapIso (eqToIso hW).op ≪≫
    (M.restrictAppIso V.ι W).symm ≪≫
    ((Scheme.Modules.toPresheaf V.toScheme ⋙
      (evaluation _ _).obj (op W)).mapIso
        ((Scheme.Modules.overFunctorEquiv V).app M).symm)

/-- Termwise restriction of the coefficient complex to the union. -/
abbrev principalSubsetRestriction
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :=
  ((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
    (principalSubsetUnion A r f) ⋙
      (Scheme.Modules.overEquiv (principalSubsetUnion A r f)).functor).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J

/-- The additive tuple total on the union. -/
abbrev principalSubsetTotal (J : CochainComplex (Spec (.of A)).Modules ℤ) :=
  ((forget₂ (ModuleCat.{u}
    ((moduleRings (principalSubsetUnion A r f).toScheme.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechTotalFunctor
        (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))).obj
          (principalSubsetRestriction A r f J))

/-- The additive group of subset coordinates in total degree n. -/
abbrev principalSubsetCoordinates
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (∀ S : {S : Finset (Fin r) // S.Nonempty},
    (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
      (op (principalSubsetOpen A r f S.val)))

/-- Insert one subset coordinate into its tuple and total summand. -/
def principalSubsetInsertOne
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) :
    AddCommGrpCat.of ((modulesSpecToSheaf.obj
      (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
        (op (principalSubsetOpen A r f S.val))) ⟶ (principalSubsetTotal A r f J).X n := by
  classical
  let V := principalSubsetUnion A r f
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let q : ℤ := n + 1 - (S.val.card : ℤ)
  let p : ℕ := S.val.card - 1
  let M := (principalSubsetRestriction A r f J).X q
  let P := (alternatingCechModulePresheaf (X := V.toScheme)).obj M
  let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
  let L := (alternatingCechComplex U P)
  let H := forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let e : (K.X (p : ℤ)).X q ≅ L.X p :=
    L.extendXIso ComplexShape.embeddingUpNat rfl
  let v : AddCommGrpCat.of
      (P.obj (op (alternatingCechIntersection U (principalSubsetTuple r S)))) ⟶
      H.obj (L.X p) :=
    AddCommGrpCat.ofHom (AddMonoidHom.single
      (fun t : Fin (p + 1) ↪o Fin r ↦
        P.obj (op (alternatingCechIntersection U t))) (principalSubsetTuple r S))
  have hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((p : ℤ), q) = n := by
    change (p : ℤ) + q = n
    dsimp [p, q]
    have := S.property.card_pos
    rw [Nat.cast_sub (by omega)]
    push_cast
    omega
  exact (principalSubsetSectionTransport A r f (J.X q) S).hom ≫ v ≫
    H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q n hpq)

/-- Insert all subset coordinates by the finite sum of total summand inclusions.
Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: def-sc-principal-open-cech-subset-insertion). -/
def principalSubsetInsertion
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    principalSubsetCoordinates A r f J n ⟶ (principalSubsetTotal A r f J).X n := by
  classical
  exact ∑ S : {S : Finset (Fin r) // S.Nonempty},
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ S) ≫ principalSubsetInsertOne A r f J n S

end
end AlgebraicGeometry
