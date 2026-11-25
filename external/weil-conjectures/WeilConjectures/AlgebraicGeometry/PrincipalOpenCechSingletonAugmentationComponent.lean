/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # The singleton component of subset insertion

Source: Stacks Project, Tags 08C1 and 01FM.
(blueprint: lem-sc-principal-open-cech-singleton-augmentation-component).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem sectionTransport_restriction
    (A : Type u) [CommRing A] (M : (Spec (.of A)).Modules)
    (V D : (Spec (.of A)).Opens) (W : V.toScheme.Opens)
    (hl : D ≤ V) (hW : V.ι ''ᵁ W = D)
    (s : (modulesSpecToSheaf.obj M).obj.obj (op V)) :
    let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
      (Scheme.Modules.overEquiv V).functor
    ((Scheme.Modules.overFunctorEquiv V).inv.app M).app W
      (M.presheaf.map (eqToHom hW).op (M.presheaf.map (homOfLE hl).op s)) =
      ((R.obj M).val.map (homOfLE (le_top (a := W))).op).hom
        ((principalOpenSectionTransport A V M).hom s) := by
  intro R
  let e := (Scheme.Modules.overFunctorEquiv V).inv.app M
  have hn := congrArg (fun g ↦ g (M.presheaf.map (eqToHom V.ι_image_top).op s))
    (e.mapPresheaf.naturality (homOfLE (le_top (a := W))).op)
  change e.app W
      (M.presheaf.map (eqToHom hW).op (M.presheaf.map (homOfLE hl).op s)) =
    ((R.obj M).presheaf.map (homOfLE (le_top (a := W))).op)
      (e.app ⊤ (M.presheaf.map (eqToHom V.ι_image_top).op s))
  change e.app W
      (M.presheaf.map
        (homOfLE (Scheme.Hom.image_mono V.ι (le_top (a := W)))).op
        (M.presheaf.map (eqToHom V.ι_image_top).op s)) =
    ((R.obj M).presheaf.map (homOfLE (le_top (a := W))).op)
      (e.app ⊤ (M.presheaf.map (eqToHom V.ι_image_top).op s)) at hn
  rw [← hn]
  congr 1
  change (M.presheaf.map (homOfLE hl).op ≫
    M.presheaf.map (eqToHom hW).op) s =
    (M.presheaf.map (eqToHom V.ι_image_top).op ≫
      M.presheaf.map
        (homOfLE (Scheme.Hom.image_mono V.ι (le_top (a := W)))).op) s
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  rfl

open Classical in
private theorem insertOne_reindex
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty})
    (p : ℕ) (q : ℤ) (hc : S.val.card = p + 1)
    (hq : q = n + 1 - (S.val.card : ℤ))
    (hpq : (p : ℤ) + q = n)
    (s : (modulesSpecToSheaf.obj (J.X q)).obj.obj
      (op (principalSubsetOpen A r f S.val))) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let W := alternatingCechIntersection U (S.val.orderEmbOfFin hc)
    ∀ (hW : V.ι ''ᵁ W = principalSubsetOpen A r f S.val),
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let L := alternatingCechComplex U
      ((alternatingCechModulePresheaf).obj ((principalSubsetRestriction A r f J).X q))
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let e : (K.X (p : ℤ)).X q ≅ L.X p :=
      L.extendXIso ComplexShape.embeddingUpNat rfl
    principalSubsetInsertOne A r f J n S
      ((modulesSpecToSheaf.map (eqToHom (congrArg J.X hq))).hom.app
        (op (principalSubsetOpen A r f S.val)) s) =
      (H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q n hpq))
        (Pi.single (S.val.orderEmbOfFin hc)
          (((Scheme.Modules.overFunctorEquiv V).inv.app (J.X q)).app W
            ((J.X q).presheaf.map (eqToHom hW).op s))) := by
  have hp : p = S.val.card - 1 := by omega
  subst p
  subst q
  intro V U W hW K L H e
  simp only [eqToHom_refl]
  rfl

open Classical in
/-- A singleton restriction inserts exactly its degree-zero tuple coordinate.
Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-singleton-augmentation-component).

Proof: Write S={i} using card S=1. Its increasing enumeration is the one-tuple
with value i. Its principal open is D(f_i), and its intersection in V is the
inverse image of D(f_i). Expand principalSubsetSectionTransport and
principalOpenSectionTransport. Naturality of the inverse overFunctorEquiv and
of restrictAppIso with respect to this open inclusion identifies the transported
restriction with the i-th coordinate of alternatingCechZero. The degree equality
identifies J^n with the coefficient in insertOne; proof irrelevance identifies
all equality transports. Since card S-1=0, the extendXIso and total inclusion
in insertOne are precisely those displayed on the right. -/
theorem principalSubsetInsertOne_singleton_augmentation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = 1)
    (hl : principalSubsetOpen A r f S.val ≤ principalSubsetUnion A r f)
    (he : n = n + 1 - (S.val.card : ℤ))
    (s : (modulesSpecToSheaf.obj (J.X n)).obj.obj (op (principalSubsetUnion A r f))) :
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
    principalSubsetInsertOne A r f J n S
      ((modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
        (homOfLE hl).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X he))).hom.app (op V) s)) =
      (H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)))
        (Pi.single (S.val.orderEmbOfFin h) (z (S.val.orderEmbOfFin h))) := by
  intro V U J' L K H e z
  have hW : V.ι ''ᵁ alternatingCechIntersection U (S.val.orderEmbOfFin h) =
      principalSubsetOpen A r f S.val := by
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    rcases S with ⟨S, hS⟩
    dsimp only at hi
    subst S
    have ht (k : Fin 1) : ({i} : Finset (Fin r)).orderEmbOfFin h k = i :=
      Finset.orderEmbOfFin_singleton i k
    simp only [alternatingCechIntersection, principalSubsetOpen, Finset.prod_singleton]
    simp_rw [ht]
    rw [iInf_const]
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) = _
    rw [V.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup (fun j ↦ PrimeSpectrum.basicOpen (f j)) i)
  let g := eqToHom (congrArg J.X he)
  have hn := congrArg (fun a ↦ a s)
    ((modulesSpecToSheaf.map g).hom.naturality (homOfLE hl).op)
  change ((modulesSpecToSheaf.map g).hom.app
      (op (principalSubsetOpen A r f S.val)))
      (((modulesSpecToSheaf.obj (J.X n)).obj.map (homOfLE hl).op) s) =
    ((modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ))))).obj.map
      (homOfLE hl).op (((modulesSpecToSheaf.map g).hom.app (op V)) s) at hn
  rw [← hn]
  rw [insertOne_reindex A r f J n S 0 n (by simpa using h) he
    (Int.zero_add n) _ hW]
  have hz : z (S.val.orderEmbOfFin h) =
      ((J'.X n).val.map
        (homOfLE (le_top (a := alternatingCechIntersection U (S.val.orderEmbOfFin h)))).op).hom
        ((principalOpenSectionTransport A V (J.X n)).hom s) := by
    dsimp only [z, e, L]
    simp only [alternatingCechZero, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [hz]
  congr 2
  exact sectionTransport_restriction A (J.X n) V (principalSubsetOpen A r f S.val)
    (alternatingCechIntersection U (S.val.orderEmbOfFin h)) hl hW s

end AlgebraicGeometry
