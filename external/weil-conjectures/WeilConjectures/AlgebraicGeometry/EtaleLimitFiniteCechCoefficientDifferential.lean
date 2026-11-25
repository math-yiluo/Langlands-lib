/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Canonical coefficient maps on descended Čech complexes

Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YP. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- Nonempty products in an over category have jointly monic underlying projections.
private theorem over_pi_ext
    {C : Type*} [Category C] {U Z : C} {n : ℕ}
    (X : Fin (n + 1) → Over U) [HasProduct X]
    (f g : Z ⟶ (∏ᶜ X).left)
    (h : ∀ a, f ≫ (Pi.π X a).left = g ≫ (Pi.π X a).left) : f = g := by
  have hw : g ≫ (∏ᶜ X).hom = f ≫ (∏ᶜ X).hom := by
    erw [← (Pi.π X 0).w, ← Category.assoc, ← Category.assoc, h 0]
  let f' : Over.mk (f ≫ (∏ᶜ X).hom) ⟶ ∏ᶜ X := Over.homMk f rfl
  let g' : Over.mk (f ≫ (∏ᶜ X).hom) ⟶ ∏ᶜ X := Over.homMk g hw
  have hh : f' = g' := by
    apply Pi.hom_ext
    intro a
    apply Over.OverMorphism.ext
    exact h a
  exact congrArg Over.Hom.left hh

-- Projection compatibility determines compatibility with every tuple reindexing.
private theorem nerve_iso_reindex
    {C : Type*} [Category C] {D : Type*} [Category D]
    {K : Type (u + 1)} {S : C} {T : D}
    [HasFiniteProducts (Over S)] [HasFiniteProducts (Over T)]
    (X : K → Over S) (Y : K → Over T) (B : C ⥤ D)
    (v : ∀ k, B.obj (X k).left ⟶ (Y k).left)
    (e : ∀ (n : ℕ) (t : Fin (n + 1) → K),
      B.obj (∏ᶜ fun a ↦ X (t a)).left ≅ (∏ᶜ fun a ↦ Y (t a)).left)
    (he : ∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
      (e n t).hom ≫ (Pi.π (fun a ↦ Y (t a)) a).left =
        B.map (Pi.π (fun a ↦ X (t a)) a).left ≫ v (t a))
    (n r : ℕ) (g : Fin (r + 1) → Fin (n + 1)) (t : Fin (n + 1) → K) :
    (e n t).hom ≫ (Pi.lift fun a ↦ Pi.π (fun a ↦ Y (t a)) (g a)).left =
      B.map (Pi.lift fun a ↦ Pi.π (fun a ↦ X (t a)) (g a)).left ≫
        (e r (t ∘ g)).hom := by
  apply over_pi_ext (fun a ↦ Y (t (g a)))
  intro a
  have hY := congrArg Over.Hom.left
    (Pi.lift_comp_π (fun a ↦ Pi.π (fun a ↦ Y (t a)) (g a)) a)
  have hX := congrArg Over.Hom.left
    (Pi.lift_comp_π (fun a ↦ Pi.π (fun a ↦ X (t a)) (g a)) a)
  dsimp only [Over.comp_left] at hY hX
  simp only [Category.assoc]
  erw [hY, he n t (g a), he r (t ∘ g) a, ← Category.assoc, ← B.map_comp, hX]
  rfl

-- The two pullback projections determine naturality of the prescribed transport.
private theorem pullback_transport_naturality
    {S₀ S T : Scheme.{u}} (p : S ⟶ S₀) (q : T ⟶ S) (r : T ⟶ S₀)
    {X Y : S₀.Etale} (f : X ⟶ Y)
    (eX : (MorphismProperty.Over.pullback @Etale ⊤ q).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ p).obj X) ≅
        (MorphismProperty.Over.pullback @Etale ⊤ r).obj X)
    (eY : (MorphismProperty.Over.pullback @Etale ⊤ q).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ p).obj Y) ≅
        (MorphismProperty.Over.pullback @Etale ⊤ r).obj Y)
    (hX : eX.hom.left ≫ pullback.fst X.hom r =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ p).obj X).hom q ≫
        pullback.fst X.hom p)
    (hY : eY.hom.left ≫ pullback.fst Y.hom r =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ p).obj Y).hom q ≫
        pullback.fst Y.hom p) :
    (MorphismProperty.Over.pullback @Etale ⊤ q).map
        ((MorphismProperty.Over.pullback @Etale ⊤ p).map f) ≫ eY.hom =
      eX.hom ≫ (MorphismProperty.Over.pullback @Etale ⊤ r).map f := by
  ext1
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    erw [hY, ← Category.assoc]
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst, Category.assoc]
    simpa only [Category.assoc] using congrArg (· ≫ f.left) hX.symm
  · have ha := MorphismProperty.Over.w eX.hom
    have hb := MorphismProperty.Over.w eY.hom
    simp only [MorphismProperty.Comma.comp_left, Category.assoc,
      MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
    erw [hb, pullback.lift_snd, ha]
    rfl

-- Transport the geometric square from descended objects to the actual nerve objects.
private theorem transport_square
    {C : Type*} [Category C] {D : Type*} [Category D] (B : C ⥤ D)
    {Ws Ws' Ns Ns' : C} {Wt Wt' Nt Nt' : D}
    (es : Ws ≅ Ns) (es' : Ws' ≅ Ns') (et : Wt ≅ Nt) (et' : Wt' ≅ Nt')
    (γ : B.obj Ws ≅ Wt) (γ' : B.obj Ws' ≅ Wt')
    (s : Ws ⟶ Ws') (t : Wt ⟶ Wt') (f : Ns ⟶ Ns') (g : Nt ⟶ Nt')
    (hs : es.hom ≫ f = s ≫ es'.hom) (ht : et.hom ≫ g = t ≫ et'.hom)
    (hγ : B.map s ≫ γ'.hom = γ.hom ≫ t) :
    ((B.mapIso es.symm) ≪≫ γ ≪≫ et).hom ≫ g =
      B.map f ≫ ((B.mapIso es'.symm) ≪≫ γ' ≪≫ et').hom := by
  apply (cancel_epi (B.map es.hom)).1
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  erw [← B.map_comp_assoc, es.hom_inv_id, B.map_id, Category.id_comp, ht]
  erw [← Category.assoc (B.map es.hom), ← B.map_comp, hs, B.map_comp]
  simp only [Category.assoc]
  erw [← B.map_comp_assoc es'.hom es'.inv, es'.hom_inv_id,
    B.map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg (· ≫ et'.hom) hγ.symm

-- Cancel the auxiliary isomorphisms in the prescribed coefficient equation.
private theorem coefficient_transport_component
    {C : Type*} [Category C] {D : Type*} [Category D]
    {A : Type*} [Category A] (B : C ⥤ D) (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
    (η : P ⟶ B.op ⋙ Q) {Ws Ns : C} {Wt Nt : D}
    (es : Ws ≅ Ns) (et : Wt ≅ Nt) (γ : B.obj Ws ≅ Wt)
    {Z : A} (m : Z ⟶ Q.obj (op Nt)) (ps : Z ⟶ P.obj (op Ns))
    (h : m ≫ Q.map et.hom.op =
      ps ≫ P.map es.hom.op ≫ η.app (op Ws) ≫ Q.map γ.inv.op) :
    m ≫ Q.map (((B.mapIso es.symm) ≪≫ γ ≪≫ et).hom.op) = ps ≫ η.app (op Ns) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, op_comp, Q.map_comp]
  erw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  erw [← Q.map_comp_assoc, ← op_comp, γ.hom_inv_id, op_id, Q.map_id,
    Category.id_comp]
  have hn := η.naturality es.inv.op
  dsimp only [Functor.comp_map, Functor.op_map] at hn
  erw [← hn, ← P.map_comp_assoc, ← op_comp, es.inv_hom_id, op_id, P.map_id,
    Category.id_comp]

-- Tuplewise naturality gives a cosimplicial map; Mathlib then gives the cochain map.
set_option backward.isDefEq.respectTransparency false in
private theorem cech_map_of_transport
    {C : Type*} [Category C] {D : Type*} [Category D]
    {A : Type*} [Category A] [Preadditive A] [HasProducts.{u + 1} A]
    {K : Type (u + 1)} {S : C} {T : D}
    [HasFiniteProducts (Over S)] [HasFiniteProducts (Over T)]
    (X : K → Over S) (Y : K → Over T) (B : C ⥤ D)
    (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A) (η : P ⟶ B.op ⋙ Q)
    (e : ∀ (n : ℕ) (t : Fin (n + 1) → K),
      B.obj (∏ᶜ fun a ↦ X (t a)).left ≅ (∏ᶜ fun a ↦ Y (t a)).left)
    (he : ∀ (n r : ℕ) (g : Fin (r + 1) → Fin (n + 1)) (t : Fin (n + 1) → K),
      (e n t).hom ≫ (Pi.lift fun a ↦ Pi.π (fun a ↦ Y (t a)) (g a)).left =
        B.map (Pi.lift fun a ↦ Pi.π (fun a ↦ X (t a)) (g a)).left ≫
          (e r (t ∘ g)).hom)
    (m : ∀ n : ℕ,
      ((cechComplexFunctor X).obj ((Over.forget S).op ⋙ P)).X n ⟶
        ((cechComplexFunctor Y).obj ((Over.forget T).op ⋙ Q)).X n)
    (hm : ∀ (n : ℕ) (t : Fin (n + 1) → K),
      m n ≫ Pi.π (fun t ↦ Q.obj (op (∏ᶜ fun a ↦ Y (t a)).left)) t ≫
          Q.map (e n t).hom.op =
        Pi.π (fun t ↦ P.obj (op (∏ᶜ fun a ↦ X (t a)).left)) t ≫
          η.app (op (∏ᶜ fun a ↦ X (t a)).left)) :
    ∀ n r : ℕ,
      m n ≫ ((cechComplexFunctor Y).obj ((Over.forget T).op ⋙ Q)).d n r =
        ((cechComplexFunctor X).obj ((Over.forget S).op ⋙ P)).d n r ≫ m r := by
  let EP := Limits.FormalCoproduct.cosimplicialObjectFunctor
    (Limits.FormalCoproduct.mk K X).cech |>.obj ((Over.forget S).op ⋙ P)
  let EQ := Limits.FormalCoproduct.cosimplicialObjectFunctor
    (Limits.FormalCoproduct.mk K Y).cech |>.obj ((Over.forget T).op ⋙ Q)
  have hnat : ∀ {n r : SimplexCategory} (g : n ⟶ r),
      m n.len ≫ EQ.map g = EP.map g ≫ m r.len := by
    intro n r g
    apply Pi.hom_ext
    intro t
    change Fin (r.len + 1) → K at t
    apply (cancel_mono (Q.map (e r.len t).hom.op)).1
    dsimp [EP, EQ, Limits.FormalCoproduct.cosimplicialObjectFunctor,
      Limits.FormalCoproduct.evalOp, Limits.FormalCoproduct.cech,
      Limits.FormalCoproduct.mapPower, Limits.FormalCoproduct.power]
    simp only [Category.assoc, Pi.lift_comp_π_assoc]
    erw [hm r.len t]
    simp only [← Category.assoc]
    erw [Pi.lift_comp_π]
    simp only [Category.assoc]
    erw [← Q.map_comp]
    erw [← op_comp, he r.len n.len g.toOrderHom.toFun t]
    erw [op_comp, Q.map_comp]
    simp only [← Category.assoc]
    have hmn := hm n.len (t ∘ g.toOrderHom.toFun)
    simp only [← Category.assoc] at hmn
    erw [hmn]
    simp only [Category.assoc]
    have hn := η.naturality
      (Pi.lift fun a ↦ Pi.π (fun a ↦ X (t a)) (g.toOrderHom.toFun a)).left.op
    dsimp only [Functor.comp_map, Functor.op_map] at hn
    erw [← hn]
    rfl
  let α : EP ⟶ EQ := { app n := m n.len, naturality _ _ g := (hnat g).symm }
  exact fun n r ↦ ((AlgebraicTopology.alternatingCofaceMapComplex A).map α).comm n r

set_option linter.unusedVariables false in
/-- The prescribed tuple maps commute with the Čech differential.
Source: Stacks Project, Tag 09YP, proof of lemma-colimit, the displayed Čech
comparison, and Tag 03AM for the alternating differential.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-coefficient-differential).

Proof: Fix a coordinate deletion. The two maps between the initial products
are determined by the retained projections. Apply the base-change functors.
The identities hNj and hNlim identify these maps with the stage and cone-point
nerve maps. For gamma and delta, their first-projection identities identify
the two ways to transport each nerve map: compare first projections to W0,
and use the structural morphism for the second pullback projection. Pullback
uniqueness gives equality. Naturality of the adjunction unit, phi, eG.inv,
and the leg of L now makes the prescribed section map commute with this face.
The maps eNj and eNlim are isomorphisms, so their presheaf images can be
cancelled. Product extensionality proves commutation with the coface map.
Summing with signs proves commutation with d n (n+1). For any other pair the
shape-up differential is zero, so the equation follows from zero composition.
The proof uses no coefficient identity/composition law or cocone equation hG.
For empty K all tuple sets are empty and product extensionality is vacuous.
-/
theorem etale_limit_finite_cech_coefficient_differential
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G)
    (U : c.pt.Etale)
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k)
    (he : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f₀ k) ≫
        eU.hom = (eV k).hom ≫ f k) :
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    let Cj := fun j : J ↦
      (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
        ((Over.forget (Uj j)).op ⋙ (F j.val).obj)
    let CX := (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
      ((Over.forget U).op ⋙ L.pt.obj)
    ∀ (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t)
      (hNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a))
      (hNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom)
      (hγ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op))
      (hδ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)),
      ∀ (m : ∀ (j k : J) (a : j ⟶ k) (n : ℕ), (Cj j).X n ⟶ (Cj k).X n)
        (l : ∀ (j : J) (n : ℕ), (Cj j).X n ⟶ CX.X n),
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (m j k a n) ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (l j n) ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op) →
      (∀ (j k : J) (a : j ⟶ k) (n r : ℕ),
        m j k a n ≫ (Cj k).d n r = (Cj j).d n r ≫ m j k a r) ∧
      (∀ (j : J) (n r : ℕ), l j n ≫ CX.d n r = (Cj j).d n r ≫ l j r) := by
  intro J B Blim Uj Vj fj W₀ pr₀ Wj Wlim Nj Nlim Pj Plim Cj CX
    eNj eNlim γ δ hNj hNlim hγ hδ m l h
  obtain ⟨hm, hl⟩ := h
  have hstage (j : J) := nerve_iso_reindex
    (fun k ↦ Over.mk (f₀ k)) (fun k ↦ Over.mk (fj j k)) (B j)
    (fun _ ↦ 𝟙 _) (eNj j) (by simpa only [Category.comp_id] using hNj j)
  have hlimit := nerve_iso_reindex
    (fun k ↦ Over.mk (f₀ k)) (fun k ↦ Over.mk (f k)) Blim
    (fun k ↦ (eV k).hom) eNlim hNlim
  constructor
  · intro j k a
    let q := D.map (show j.val ⟶ k.val from a).op
    let Bq := MorphismProperty.Over.pullback @Etale ⊤ q
    let η : (F j.val).obj ⟶ Bq.op ⋙ (F k.val).obj :=
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app (F j.val)) ≫
        (lowerStar AddCommGrpCat.{u + 1} q).map
          (φ (show j.val ⟶ k.val from a))).hom
    apply cech_map_of_transport (fun x ↦ Over.mk (fj j x))
      (fun x ↦ Over.mk (fj k x)) Bq (F j.val).obj (F k.val).obj η
      (fun n t ↦ Bq.mapIso (eNj j n t).symm ≪≫ γ j k a n t ≪≫ eNj k n t)
    · intro n r g t
      apply transport_square Bq
        (eNj j n t) (eNj j r (t ∘ g)) (eNj k n t) (eNj k r (t ∘ g))
        (γ j k a n t) (γ j k a r (t ∘ g))
        ((B j).map (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left)
        ((B k).map (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left)
        _ _ (hstage j n r g t) (hstage k n r g t)
      exact pullback_transport_naturality
        (D.map (homOfLE j.property).op) q (D.map (homOfLE k.property).op)
        (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left
        (γ j k a n t) (γ j k a r (t ∘ g))
        (hγ j k a n t) (hγ j k a r (t ∘ g))
    · intro n t
      apply coefficient_transport_component Bq (F j.val).obj (F k.val).obj η
        (eNj j n t) (eNj k n t) (γ j k a n t)
        (m j k a n ≫ Pi.π (Pj k n) t) (Pi.π (Pj j n) t)
      dsimp only [η, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      erw [lowerStar_map_hom_app]
      simpa only [Category.assoc] using hm j k a n t
  · intro j
    let q := c.π.app (op j.val)
    let Bq := MorphismProperty.Over.pullback @Etale ⊤ q
    let η : (F j.val).obj ⟶ Bq.op ⋙ L.pt.obj :=
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app (F j.val)) ≫
        (lowerStar AddCommGrpCat.{u + 1} q).map
          ((eG j.val).inv ≫ L.ι.app j.val)).hom
    apply cech_map_of_transport (fun x ↦ Over.mk (fj j x))
      (fun x ↦ Over.mk (f x)) Bq (F j.val).obj L.pt.obj η
      (fun n t ↦ Bq.mapIso (eNj j n t).symm ≪≫ δ j n t ≪≫ eNlim n t)
    · intro n r g t
      apply transport_square Bq
        (eNj j n t) (eNj j r (t ∘ g)) (eNlim n t) (eNlim r (t ∘ g))
        (δ j n t) (δ j r (t ∘ g))
        ((B j).map (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left)
        (Blim.map (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left)
        _ _ (hstage j n r g t) (hlimit n r g t)
      exact pullback_transport_naturality
        (D.map (homOfLE j.property).op) q (c.π.app (op i₀))
        (Pi.lift fun x ↦ Pi.π (fun x ↦ Over.mk (f₀ (t x))) (g x)).left
        (δ j n t) (δ j r (t ∘ g)) (hδ j n t) (hδ j r (t ∘ g))
    · intro n t
      apply coefficient_transport_component Bq (F j.val).obj L.pt.obj η
        (eNj j n t) (eNlim n t) (δ j n t)
        (l j n ≫ Pi.π (Plim n) t) (Pi.π (Pj j n) t)
      dsimp only [η, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      erw [lowerStar_map_hom_app]
      simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        Category.assoc] using hl j n t

end AlgebraicGeometry.Etale
