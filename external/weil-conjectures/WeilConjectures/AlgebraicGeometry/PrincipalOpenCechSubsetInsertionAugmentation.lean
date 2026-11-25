/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSingletonAugmentationComponent

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

open Classical in
private theorem sum_singleton_subsets (r : ℕ)
    (M : (Fin 1 ↪o Fin r) → Type u) [∀ t, AddCommGroup (M t)]
    (z : ∀ t, M t) :
    (∑ S : {S : Finset (Fin r) // S.Nonempty},
      if h : S.val.card = 1 then
        Pi.single (S.val.orderEmbOfFin h) (z (S.val.orderEmbOfFin h)) else 0) = z := by
  classical
  funext t
  rw [Finset.sum_apply]
  let S : {S : Finset (Fin r) // S.Nonempty} := ⟨{t 0}, Finset.singleton_nonempty _⟩
  have hS : S.val.card = 1 := Finset.card_singleton _
  have ht : S.val.orderEmbOfFin hS = t := by
    apply DFunLike.ext
    intro k
    have hm := Finset.orderEmbOfFin_mem S.val hS k
    have hk : k = 0 := Subsingleton.elim _ _
    simpa only [S, Finset.mem_singleton, hk] using hm
  rw [Finset.sum_eq_single S]
  · rw [dite_eq_left hS]
    change Pi.single (S.val.orderEmbOfFin hS) (z (S.val.orderEmbOfFin hS)) t = z t
    rw [ht]
    simp
  · intro T _ hTS
    by_cases hT : T.val.card = 1
    · rw [dite_eq_left hT, Pi.single_eq_of_ne]
      intro h
      apply hTS
      apply Subtype.ext
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hT
      have hm := Finset.orderEmbOfFin_mem T.val hT (0 : Fin 1)
      have hmi : (T.val.orderEmbOfFin hT) 0 = i :=
        Finset.mem_singleton.mp (hi ▸ hm)
      have hit : i = t 0 :=
        hmi.symm.trans (congrArg (fun a : Fin 1 ↪o Fin r ↦ a 0) h).symm
      simpa [S, hit] using hi
    · simp [hT]
  · simp

open Classical in
private theorem map_sum_singleton_subsets
    (r : ℕ) (M : (Fin 1 ↪o Fin r) → Type u) [∀ t, AddCommGroup (M t)]
    {β : Type u} [AddCommGroup β] (b : (∀ t, M t) →+ β) (z : ∀ t, M t) :
    (∑ S : {S : Finset (Fin r) // S.Nonempty},
      b (if h : S.val.card = 1 then
        Pi.single (S.val.orderEmbOfFin h) (z (S.val.orderEmbOfFin h)) else 0)) = b z := by
  rw [← map_sum b, sum_singleton_subsets]

private theorem principalSubsetInsertion_hom_apply
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (c : principalSubsetCoordinates A r f J n) :
    (principalSubsetInsertion A r f J n).hom c =
      ∑ S, principalSubsetInsertOne A r f J n S (c S) := by
  unfold principalSubsetInsertion
  rw [show (∑ S, AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ S) ≫
      principalSubsetInsertOne A r f J n S).hom =
      ∑ S, (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ S) ≫
        principalSubsetInsertOne A r f J n S).hom from
    map_sum (AddCommGrpCat.homAddEquiv.toAddMonoidHom) _ _]
  rw [AddMonoidHom.finsetSum_apply]
  change (∑ S, principalSubsetInsertOne A r f J n S (c S)) = _
  rfl

private theorem map_iso_cancel_apply
    {C : Type*} [Category C] (H : C ⥤ AddCommGrpCat.{u})
    {X Y Z W : C} (a : X ⟶ Y) (e : Y ≅ Z) (t : Y ⟶ W) (x : H.obj X) :
    (H.map (a ≫ e.hom) ≫ (H.map e.inv ≫ H.map t)) x = H.map (a ≫ t) x := by
  rw [← H.map_comp, ← H.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- Explicit subset insertion agrees with the singleton augmentation.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-insertion-augmentation).

Proof: Expand the augmentation as restriction into the degree-zero tuple column
followed by its total summand inclusion. In the finite subset insertion, all coordinates
except singleton subsets are zero, and their insertions vanish by additivity.
For a singleton, increasing enumeration is its unique one-tuple. Naturality of the
restriction equivalence identifies restriction after transporting a global section
with transporting its restriction to the corresponding principal open. The equality
hes identifies the coefficient degrees, and proof irrelevance equates the transports.
Summing these singleton insertions gives the degree-zero column inclusion, hence the
augmentation. For the empty cover the sum and the degree-zero column are both zero. -/
theorem principalSubsetInsertion_augmentation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let D := principalSubsetOpen A r f
    ∀ (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        (Scheme.Modules.overEquiv V).functor
      let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
      let U : Fin r → V.toScheme.Opens :=
        fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
      let G := (forget₂
        (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)
      ∀ (n : ℤ) (s : (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V)),
          principalSubsetInsertion A r f J n (fun S ↦ if h : S.val.card = 1 then
            (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
              (homOfLE (hls S h)).op
              ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
                (op V) s) else 0) =
            (G.map ((alternatingCechAugmentation U).app J')).f n
              (by
                change (forget₂
                  (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
                  AddCommGrpCat).obj
                    ((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).obj
                      (R.obj (J.X n)))
                exact (principalOpenSectionTransport A V (J.X n)).hom s) := by
  classical
  intro V D hls hes R J' U G n s
  let c : principalSubsetCoordinates A r f J n := fun S ↦
    if h : S.val.card = 1 then
      (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
        (homOfLE (hls S h)).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
          (op (principalSubsetUnion A r f)) s) else 0
  change (principalSubsetInsertion A r f J n).hom c = _
  rw [principalSubsetInsertion_hom_apply]
  let V := principalSubsetUnion A r f
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let J' := principalSubsetRestriction A r f J
  let L := alternatingCechComplex U ((alternatingCechModulePresheaf).obj (J'.X n))
  let K := (alternatingCechDoubleFunctor U).obj J'
  let H := forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let e : (K.X 0).X n ≅ L.X 0 := L.extendXIso ComplexShape.embeddingUpNat rfl
  let z := (H.map (alternatingCechZero U (J'.X n) ≫ e.hom))
    ((principalOpenSectionTransport A V (J.X n)).hom s)
  let b := H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
  have hc (S : {S : Finset (Fin r) // S.Nonempty}) :
      principalSubsetInsertOne A r f J n S (c S) =
      b (if h : S.val.card = 1 then
        Pi.single (S.val.orderEmbOfFin h) (z (S.val.orderEmbOfFin h)) else 0) := by
    by_cases h : S.val.card = 1
    · dsimp only [c]
      rw [dite_eq_left h, dite_eq_left h]
      exact principalSubsetInsertOne_singleton_augmentation A r f J n S h
        (hls S h) (hes S h n) s
    · simpa only [c, dite_eq_right h] using
        (map_zero (principalSubsetInsertOne A r f J n S).hom).trans (map_zero b.hom).symm
  change (∑ S, principalSubsetInsertOne A r f J n S (c S)) = _
  simp_rw [hc]
  refine (map_sum_singleton_subsets r _ b.hom z).trans ?_
  change (H.map (alternatingCechZero U (J'.X n) ≫ e.hom) ≫ b).hom
    ((principalOpenSectionTransport A V (J.X n)).hom s) = _
  exact map_iso_cancel_apply H (alternatingCechZero U (J'.X n)) e
    (K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    ((principalOpenSectionTransport A V (J.X n)).hom s)

end AlgebraicGeometry
