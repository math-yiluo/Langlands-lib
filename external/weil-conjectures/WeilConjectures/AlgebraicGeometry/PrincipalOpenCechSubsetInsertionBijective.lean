/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import Mathlib.Algebra.Category.ModuleCat.Products

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

private noncomputable def subsetTotalProjection {R : Type u} [Ring R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) (p q n : ℤ) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc fun a b _ ↦
    if h : a = p ∧ b = q then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0

private noncomputable def subsetReadOne
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) :
    (principalSubsetTotal A r f J).X n ⟶
      AddCommGrpCat.of ((modulesSpecToSheaf.obj
        (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
          (op (principalSubsetOpen A r f S.val))) := by
  classical
  let V := principalSubsetUnion A r f
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let q : ℤ := n + 1 - (S.val.card : ℤ)
  let p : ℕ := S.val.card - 1
  let P := (alternatingCechModulePresheaf (X := V.toScheme)).obj
    ((principalSubsetRestriction A r f J).X q)
  let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
  let L := alternatingCechComplex U P
  let H := forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let e : (K.X (p : ℤ)).X q ≅ L.X p :=
    L.extendXIso ComplexShape.embeddingUpNat rfl
  exact H.map (subsetTotalProjection K (p : ℤ) q n) ≫ H.map e.hom ≫
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ (principalSubsetTuple r S)) ≫
      (principalSubsetSectionTransport A r f (J.X q) S).inv

@[reassoc]
private theorem single_eval {ι : Type} (G : ι → Type u) [∀ i, AddCommGroup (G i)]
    (i : ι) [DecidableEq ι] :
    AddCommGrpCat.ofHom (AddMonoidHom.single G i) ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom G i) = 𝟙 _ := by
  apply AddCommGrpCat.ext
  intro x
  change Pi.single i x i = x
  exact Pi.single_eq_same i x

private theorem subsetInsertRead_self
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) :
    principalSubsetInsertOne A r f J n S ≫ subsetReadOne A r f J n S = 𝟙 _ := by
  classical
  dsimp only [principalSubsetInsertOne, subsetReadOne]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    subsetTotalProjection]
  simp only [Functor.comp_obj, ModuleCat.forget₂_obj, ComplexShape.π_def,
    HomologicalComplex₂.ι_totalDesc_assoc, and_self, ↓reduceDIte,
    HomologicalComplex₂.XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    Iso.inv_hom_id, ModuleCat.forget₂_map, ModuleCat.hom_id]
  change _ ≫ _ ≫ (𝟙 _) ≫ _ ≫ _ = _
  simp only [Category.id_comp]
  rw [single_eval_assoc, Iso.hom_inv_id]

private theorem single_transport_eval_zero {R : Type u} [Ring R] {r : ℕ}
    [∀ p : ℕ, DecidableEq (Fin (p + 1) ↪o Fin r)]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    (G : (p : ℕ) → ℤ → (Fin (p + 1) ↪o Fin r) → ModuleCat.{u} R)
    (e : ∀ (p : ℕ) (q : ℤ), (K.X (p : ℤ)).X q ≅
      ModuleCat.of R (∀ t : Fin (p + 1) ↪o Fin r, G p q t))
    (p p' : ℕ) (q q' : ℤ) (hp : p = p') (hq : q = q')
    (t : Fin (p + 1) ↪o Fin r) (s : Fin (p' + 1) ↪o Fin r)
    (hne : Set.range t ≠ Set.range s) :
    let H := forget₂ (ModuleCat.{u} R) AddCommGrpCat
    AddCommGrpCat.ofHom (AddMonoidHom.single (fun t ↦ G p q t) t) ≫
      H.map (e p q).inv ≫
      H.map (K.XXIsoOfEq _ _ _ (congrArg Int.ofNat hp) hq).hom ≫
      H.map (e p' q').hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun s ↦ G p' q' s) s) = 0 := by
  subst p'
  subst q'
  dsimp only
  rw [HomologicalComplex₂.XXIsoOfEq_rfl, Iso.refl_hom]
  change _ ≫ _ ≫ (𝟙 _) ≫ _ ≫ _ = 0
  rw [Category.id_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  change _ ≫ (𝟙 _) ≫ _ = 0
  rw [Category.id_comp]
  have hts : t ≠ s := fun h ↦ hne (congrArg (fun t : Fin (p + 1) ↪o Fin r ↦ Set.range t) h)
  apply AddCommGrpCat.ext
  intro x
  change (Pi.single t x : ∀ s, G p q s) s = 0
  exact Pi.single_eq_of_ne (M := fun s ↦ (G p q s : Type u)) hts.symm x

private theorem subsetInsertRead_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S T : {S : Finset (Fin r) // S.Nonempty}) (hST : T ≠ S) :
    principalSubsetInsertOne A r f J n T ≫ subsetReadOne A r f J n S = 0 := by
  classical
  dsimp only [principalSubsetInsertOne, subsetReadOne]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    subsetTotalProjection, HomologicalComplex₂.ι_totalDesc_assoc]
  split_ifs with h
  · let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let P (q : ℤ) := (alternatingCechModulePresheaf (X := V.toScheme)).obj
      ((principalSubsetRestriction A r f J).X q)
    let G (p : ℕ) (q : ℤ) (t : Fin (p + 1) ↪o Fin r) :=
      (P q).obj (op (alternatingCechIntersection U t))
    let e (p : ℕ) (q : ℤ) : (K.X (p : ℤ)).X q ≅
        ModuleCat.of _ (∀ t : Fin (p + 1) ↪o Fin r, G p q t) :=
      (alternatingCechComplex U (P q)).extendXIso ComplexShape.embeddingUpNat rfl
    have hp : T.val.card - 1 = S.val.card - 1 := by omega
    have hne : Set.range (principalSubsetTuple r T) ≠
        Set.range (principalSubsetTuple r S) := by
      intro heq
      apply hST
      apply Subtype.ext
      apply Finset.coe_injective
      simpa only [principalSubsetTuple, Finset.range_orderEmbOfFin] using heq
    have hz := single_transport_eval_zero K G e _ _ _ _ hp h.2
      (principalSubsetTuple r T) (principalSubsetTuple r S) hne
    have hh := congrArg (fun z ↦
      (principalSubsetSectionTransport A r f (J.X (n + 1 - (T.val.card : ℤ))) T).hom ≫
        z ≫ (principalSubsetSectionTransport A r f
          (J.X (n + 1 - (S.val.card : ℤ))) S).inv) hz
    simpa only [Category.assoc, Functor.map_comp, comp_zero, zero_comp] using hh
  · simp only [Functor.map_zero, comp_zero, zero_comp]

private theorem sum_apply {M N : AddCommGrpCat.{u}} {ι : Type*}
    (f : ι → (M ⟶ N)) (s : Finset ι) (x : M) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)

private theorem insertion_single
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty})
    (x : (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
      (op (principalSubsetOpen A r f S.val))) :
    principalSubsetInsertion A r f J n (Pi.single S x) =
      principalSubsetInsertOne A r f J n S x := by
  classical
  unfold principalSubsetInsertion
  rw [sum_apply, Finset.sum_eq_single S]
  · change principalSubsetInsertOne A r f J n S
      ((Pi.single S x : principalSubsetCoordinates A r f J n) S) = _
    rw [Pi.single_eq_same]
  · intro T _ hTS
    change principalSubsetInsertOne A r f J n T
      ((Pi.single S x : principalSubsetCoordinates A r f J n) T) = 0
    rw [Pi.single_eq_of_ne hTS, map_zero]
  · simp

private theorem total_induction {R : Type u} [Ring R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) (n : ℤ)
    (P : (K.total (ComplexShape.up ℤ)).X n → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hι : ∀ (p q : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
      (x : (K.X p).X q), P (K.ιTotal (ComplexShape.up ℤ) p q n h x))
    (y : (K.total (ComplexShape.up ℤ)).X n) : P y := by
  classical
  let π := ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let F := K.toGradedObject.mapObjFun π n
  let h := K.toGradedObject.isColimitCofanMapObj π n
  let e : (K.total (ComplexShape.up ℤ)).X n ≅
      ModuleCat.of _ (DirectSum _ (fun i ↦ (F i : Type u))) :=
    h.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit F)
  suffices ∀ z : DirectSum _ (fun i ↦ (F i : Type u)), P (e.inv z) by
    simpa only [Iso.hom_inv_id_apply] using this (e.hom y)
  intro z
  induction z using DirectSum.induction_on with
  | zero => simpa only [map_zero] using h0
  | add x y hx hy => simpa only [map_add] using hadd _ _ hx hy
  | of i x =>
    have he := h.comp_coconePointUniqueUpToIso_inv
      (ModuleCat.coproductCoconeIsColimit F) (Discrete.mk i)
    have hx := congrArg (fun f ↦ f x) he
    change e.inv (DirectSum.of (fun i ↦ (F i : Type u)) i x) =
      K.ιTotal (ComplexShape.up ℤ) i.val.1 i.val.2 n i.property x at hx
    rw [hx]
    exact hι _ _ _ x

private theorem subsetInsertion_surjective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    Function.Surjective (principalSubsetInsertion A r f J n) := by
  classical
  let V := principalSubsetUnion A r f
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
  let P (q : ℤ) := (alternatingCechModulePresheaf (X := V.toScheme)).obj
    ((principalSubsetRestriction A r f J).X q)
  let B := (principalSubsetInsertion A r f J n).hom.range
  intro y
  change y ∈ B
  apply total_induction K n (fun y ↦ y ∈ B) B.zero_mem
    (fun _ _ hx hy ↦ B.add_mem hx hy) _ y
  intro p q hpq x
  by_cases hp : 0 ≤ p
  · lift p to ℕ using hp
    let e : (K.X (p : ℤ)).X q ≅ (alternatingCechComplex U (P q)).X p :=
      (alternatingCechComplex U (P q)).extendXIso ComplexShape.embeddingUpNat rfl
    have hx : x = e.inv (e.hom x) := (Iso.hom_inv_id_apply e x).symm
    rw [hx, ← Finset.univ_sum_single (e.hom x)]
    simp only [map_sum]
    apply B.sum_mem
    intro t _
    generalize hs : (⟨Finset.univ.map t.toEmbedding,
      by exact ⟨t 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩⟩ :
        {S : Finset (Fin r) // S.Nonempty}) = S
    have hcard : S.val.card = p + 1 := by
      rw [← hs]
      simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hpS : p = S.val.card - 1 := by omega
    have hq : q = n + 1 - (S.val.card : ℤ) := by
      change (p : ℤ) + q = n at hpq
      omega
    subst p
    subst q
    have ht : t = principalSubsetTuple r S := by
      apply Finset.orderEmbOfFin_unique'
      intro i
      have hsval := congrArg Subtype.val hs
      exact (congrArg (fun W : Finset (Fin r) ↦ t i ∈ W) hsval).mp
        (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    subst t
    let z := e.hom x (principalSubsetTuple r S)
    let a := (principalSubsetSectionTransport A r f
      (J.X (n + 1 - (S.val.card : ℤ))) S).inv z
    refine ⟨Pi.single S a, ?_⟩
    change principalSubsetInsertion A r f J n (Pi.single S a) = _
    rw [insertion_single]
    dsimp only [principalSubsetInsertOne]
    change K.ιTotal (ComplexShape.up ℤ) _ _ n _
      (e.inv (Pi.single (principalSubsetTuple r S)
        ((principalSubsetSectionTransport A r f
          (J.X (n + 1 - (S.val.card : ℤ))) S).hom a))) = _
    dsimp only [a]
    rw [Iso.inv_hom_id_apply]
  · have hz : IsZero ((K.X p).X q) :=
      (alternatingCechComplex U (P q)).isZero_extend_X ComplexShape.embeddingUpNat p
        (fun i hi ↦ by change (i : ℤ) = p at hi; omega)
    have : Subsingleton ((K.X p).X q) := ModuleCat.isZero_iff_subsingleton.mp hz
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, map_zero]
    exact B.zero_mem

private theorem subsetInsertion_read
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) :
    principalSubsetInsertion A r f J n ≫ subsetReadOne A r f J n S =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ S) := by
  classical
  unfold principalSubsetInsertion
  rw [Preadditive.sum_comp, Finset.sum_eq_single S]
  · rw [Category.assoc, subsetInsertRead_self, Category.comp_id]
  · intro T _ hTS
    rw [Category.assoc, subsetInsertRead_zero A r f J n S T hTS, comp_zero]
  · simp

/-- The explicit finite sum of subset insertions is bijective.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-insertion-bijective).

Proof: In column p, the extension by zero identifies the nonnegative component with
sections on increasing (p+1)-tuples. Increasing enumeration bijects these tuples with
subsets of cardinality p+1. Section transport is an additive isomorphism on each
coordinate. Negative columns are zero, and columns p >= r have no tuples and are zero.
On each total diagonal the only nonzero summands are therefore the finitely many
columns 0 <= p < r. The universal coproduct is the finite direct sum of these groups,
which is their finite product. The map defined by summing the summand insertions is
this product-to-coproduct isomorphism. Its inverse reads each tuple coordinate after
projecting to its column and applies inverse section transport. These maps are inverse
on every summand and coordinate. For r=0 all families are empty and both groups are zero.
Repeated opens retain different indices, and all arguments apply to zero section groups. -/
theorem principalSubsetInsertion_bijective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    Function.Bijective (principalSubsetInsertion A r f J n) := by
  classical
  constructor
  · intro x y hxy
    funext S
    have hx := congrArg (fun z ↦ z x) (subsetInsertion_read A r f J n S)
    have hy := congrArg (fun z ↦ z y) (subsetInsertion_read A r f J n S)
    change subsetReadOne A r f J n S
      (principalSubsetInsertion A r f J n x) = x S at hx
    change subsetReadOne A r f J n S
      (principalSubsetInsertion A r f J n y) = y S at hy
    rw [← hx, ← hy, hxy]
  · exact subsetInsertion_surjective A r f J n

/-- The inverse is determined uniquely by the bijective explicit insertion map. -/
noncomputable def principalSubsetInsertionIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    principalSubsetCoordinates A r f J n ≅ (principalSubsetTotal A r f J).X n :=
  (AddEquiv.ofBijective (principalSubsetInsertion A r f J n).hom
    (principalSubsetInsertion_bijective A r f J n)).toAddCommGrpIso

end AlgebraicGeometry
