/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalModule.InternalModule
public import WeilConjectures.CategoryTheory.Finite.FiniteContinuousModule

set_option linter.privateModule false

/-!
# Equivalences of module objects and finite continuous linear actions

Source: Stacks Project, Tag 0DV5, proof of (2)-(3)
(blueprint: lem-pod-equivalence-induces-module-objects).
-/

@[expose] public section

section

universe r v₁ v₂ u₁ u₂ g u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory

namespace InternalModule

private theorem map_pair
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    {T X Y : C} (a : T ⟶ X) (b : T ⟶ Y) :
    prod.lift (F.map a) (F.map b) ≫ inv (prodComparison F X Y) =
      F.map (prod.lift a b) := by
  apply (cancel_mono (prodComparison F X Y)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext <;> simp [prodComparison, ← F.map_comp]

private theorem map_from
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    (T : C) : terminal.from (F.obj T) ≫ inv (terminalComparison F) =
      F.map (terminal.from T) := by
  apply (cancel_mono (terminalComparison F)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact terminal.hom_ext _ _

private theorem map_add
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C)
    {T : C} (a b : T ⟶ A.X) :
    prod.lift (e.functor.map a) (e.functor.map b) ≫
      (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) =
      e.functor.map (prod.lift a b ≫ A.add) := by
  rw [← Category.assoc, map_pair, e.functor.map_comp]

private theorem map_zero
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C) (T : C) :
    terminal.from (e.functor.obj T) ≫
      (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) =
      e.functor.map (terminal.from T ≫ A.zero) := by
  rw [← Category.assoc, map_from, e.functor.map_comp]

private noncomputable def transport
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C) :
    InternalModule R D where
  X := e.functor.obj A.X
  add := inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add
  zero := inv (terminalComparison e.functor) ≫ e.functor.map A.zero
  neg := e.functor.map A.neg
  smul a := e.functor.map (A.smul a)
  add_assoc T a b c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    let b' := e.functor.preimage (h ≫ b)
    let c' := e.functor.preimage (h ≫ c)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha, hb, hc]
    simp only [Category.assoc, map_add, A.add_assoc]
  zero_add T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [terminal.comp_from, Category.assoc, map_zero, map_add, A.zero_add]
  add_zero T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [Category.assoc, terminal.comp_from_assoc, map_zero, map_add, A.add_zero]
  neg_add T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [Category.assoc, terminal.comp_from_assoc, map_zero, map_add,
      ← e.functor.map_comp, A.neg_add]
  add_comm T a b := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    let b' := e.functor.preimage (h ≫ b)
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha, hb]
    simp only [Category.assoc, map_add, A.add_comm]
  one_smul := by simpa using congrArg e.functor.map A.one_smul
  mul_smul a b := by simpa using congrArg e.functor.map (A.mul_smul a b)
  smul_add a T b c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let b' := e.functor.preimage (h ≫ b)
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    let c' := e.functor.preimage (h ≫ c)
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, hb, hc]
    simp only [Category.assoc, map_add, ← e.functor.map_comp, A.smul_add]
  add_smul a b T c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let c' := e.functor.preimage (h ≫ c)
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, hc]
    simp only [Category.assoc, map_add, ← e.functor.map_comp, A.add_smul]
  zero_smul := by
    rw [A.zero_smul, e.functor.map_comp, ← map_from, Category.assoc]
  smul_zero a := by
    rw [Category.assoc, ← e.functor.map_comp, A.smul_zero]

private theorem transport_isHom
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A B : InternalModule R C)
    (f : A.X ⟶ B.X) :
    IsHom (transport e A) (transport e B) (e.functor.map f) ↔ IsHom A B f := by
  dsimp only [IsHom, transport]
  constructor
  · rintro ⟨ha, hz, hn, hs⟩
    refine ⟨e.functor.map_injective ?_, e.functor.map_injective ?_,
      e.functor.map_injective ?_, fun a ↦ e.functor.map_injective ?_⟩
    · apply (cancel_epi (inv (prodComparison e.functor A.X A.X))).1
      simpa only [e.functor.map_comp, ← Category.assoc, prodComparison_inv_natural] using ha
    · apply (cancel_epi (inv (terminalComparison e.functor))).1
      simpa only [e.functor.map_comp, Category.assoc] using hz
    · simpa only [e.functor.map_comp] using hn
    · simpa only [e.functor.map_comp] using hs a
  · rintro ⟨ha, hz, hn, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) ≫
        e.functor.map f = _
      rw [Category.assoc, ← e.functor.map_comp, ha, e.functor.map_comp,
        ← Category.assoc, prodComparison_inv_natural, Category.assoc]
    · change (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) ≫
        e.functor.map f = inv (terminalComparison e.functor) ≫ e.functor.map B.zero
      rw [Category.assoc, ← e.functor.map_comp, hz]
    · simpa only [e.functor.map_comp] using congrArg e.functor.map hn
    · intro a
      simpa only [e.functor.map_comp] using congrArg e.functor.map (hs a)

private noncomputable def transportFunctor
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) :
    InternalModule R C ⥤ InternalModule R D where
  obj := transport e
  map f := ⟨e.functor.map f.val, (transport_isHom e _ _ _).2 f.property⟩
  map_id A := Subtype.ext (e.functor.map_id A.X)
  map_comp f g := Subtype.ext (e.functor.map_comp f.val g.val)

private theorem double_prod
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (X Y : D) :
    inv (prodComparison e.functor (e.inverse.obj X) (e.inverse.obj Y)) ≫
      e.functor.map (inv (prodComparison e.inverse X Y)) ≫
        e.counitIso.hom.app (X ⨯ Y) =
      prod.map (e.counitIso.hom.app X) (e.counitIso.hom.app Y) := by
  apply prod.hom_ext
  · have hn := e.counitIso.hom.naturality (prod.fst : X ⨯ Y ⟶ X)
    change e.functor.map (e.inverse.map prod.fst) ≫ _ = _ ≫ prod.fst at hn
    simp only [Category.assoc]
    erw [← hn]
    simp only [← Category.assoc, ← e.functor.map_comp,
      inv_prodComparison_map_fst]
    exact (prod.map_fst _ _).symm
  · have hn := e.counitIso.hom.naturality (prod.snd : X ⨯ Y ⟶ Y)
    change e.functor.map (e.inverse.map prod.snd) ≫ _ = _ ≫ prod.snd at hn
    simp only [Category.assoc]
    erw [← hn]
    simp only [← Category.assoc, ← e.functor.map_comp,
      inv_prodComparison_map_snd]
    exact (prod.map_snd _ _).symm

private theorem counit_isHom
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (B : InternalModule R D) :
    IsHom (transport e (transport e.symm B)) B (e.counitIso.hom.app B.X) := by
  change (_ ≫ _) ≫ _ = _ ≫ B.add ∧ (_ ≫ _) ≫ _ = B.zero ∧
    e.functor.map (e.inverse.map B.neg) ≫ _ = _ ≫ B.neg ∧
    ∀ a, e.functor.map (e.inverse.map (B.smul a)) ≫ _ = _ ≫ B.smul a
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (inv (prodComparison e.functor (e.inverse.obj B.X) (e.inverse.obj B.X)) ≫
        e.functor.map (inv (prodComparison e.inverse B.X B.X) ≫ e.inverse.map B.add)) ≫
        e.counitIso.hom.app B.X =
          prod.map (e.counitIso.hom.app B.X) (e.counitIso.hom.app B.X) ≫ B.add
    simp only [e.functor.map_comp, Category.assoc]
    have hn := e.counitIso.hom.naturality B.add
    change e.functor.map (e.inverse.map B.add) ≫ _ = _ ≫ B.add at hn
    rw [hn]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ B.add) (double_prod e B.X B.X)
  · change (inv (terminalComparison e.functor) ≫
        e.functor.map (inv (terminalComparison e.inverse) ≫ e.inverse.map B.zero)) ≫
        e.counitIso.hom.app B.X = B.zero
    simp only [e.functor.map_comp, Category.assoc]
    have hn := e.counitIso.hom.naturality B.zero
    change e.functor.map (e.inverse.map B.zero) ≫ _ = _ ≫ B.zero at hn
    rw [hn]
    have h : inv (terminalComparison e.functor) ≫
        e.functor.map (inv (terminalComparison e.inverse)) ≫
          e.counitIso.hom.app (⊤_ D) = 𝟙 (⊤_ D) := terminal.hom_ext _ _
    simpa only [Category.assoc, Category.id_comp] using congrArg (fun f ↦ f ≫ B.zero) h
  · exact e.counitIso.hom.naturality B.neg
  · intro a
    exact e.counitIso.hom.naturality (B.smul a)

private theorem isHom_inv
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    (A B : InternalModule R C) (i : A.X ≅ B.X)
    (hi : IsHom A B i.hom) : IsHom B A i.inv := by
  rcases hi with ⟨ha, hz, hn, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (cancel_mono i.hom).1
    simp only [Category.assoc, i.inv_hom_id, Category.comp_id]
    rw [ha, ← Category.assoc, prod.map_map]
    simp
  · apply (cancel_mono i.hom).1
    simpa using hz.symm
  · apply (cancel_epi i.hom).1
    simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    rw [← hn, Category.assoc, i.hom_inv_id, Category.comp_id]
  · intro a
    apply (cancel_epi i.hom).1
    simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    rw [← hs a, Category.assoc, i.hom_inv_id, Category.comp_id]

private noncomputable def counitIso
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (B : InternalModule R D) :
    (transportFunctor (R := R) e).obj (transport e.symm B) ≅ B where
  hom := ⟨e.counitIso.hom.app B.X, counit_isHom e B⟩
  inv := ⟨e.counitIso.inv.app B.X, by
    change IsHom B (transport e (transport e.symm B)) (e.counitIso.inv.app B.X)
    exact isHom_inv (transport e (transport e.symm B)) B
      (e.counitIso.app B.X) (counit_isHom e B)⟩
  hom_inv_id := Subtype.ext (e.counitIso.hom_inv_id_app B.X)
  inv_hom_id := Subtype.ext (e.counitIso.inv_hom_id_app B.X)

end InternalModule

section FiniteActions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace InternalModule
variable {R : Type r} [Ring R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private abbrev ev {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y) :
    X.obj.V → Y.obj.V := f.hom.hom

omit [IsTopologicalGroup G] in
omit [IsTopologicalGroup G] in
omit [IsTopologicalGroup G] in
private def caHom {X Y : ContAction FintypeCat.{u} G} (f : X.obj.V → Y.obj.V)
    (hf : ∀ (g : G) x, f ((X.obj.ρ g).asHom.hom x) = (Y.obj.ρ g).asHom.hom (f x)) : X ⟶ Y :=
  ⟨⟨FintypeCat.homMk f, fun g ↦ FintypeCat.hom_ext _ _ (hf g)⟩⟩

-- Concrete products let us evaluate categorical diagrams at arbitrary carrier points.
private def pointProd (X Y : ContAction FintypeCat.{u} G) :
    ContAction FintypeCat.{u} G where
  obj :=
    { V := FintypeCat.of (X.obj.V × Y.obj.V)
      ρ :=
        { toFun g := .of <| FintypeCat.homMk
            (fun p ↦ ((X.obj.ρ g).asHom.hom p.1, (Y.obj.ρ g).asHom.hom p.2))
          map_one' := by
            apply End.ext
            apply FintypeCat.hom_ext
            intro p
            change ((X.obj.ρ 1).asHom.hom p.1, (Y.obj.ρ 1).asHom.hom p.2) = p
            simp only [map_one]
            rfl
          map_mul' g h := by
            apply End.ext
            apply FintypeCat.hom_ext
            intro p
            change ((X.obj.ρ (g*h)).asHom.hom p.1, (Y.obj.ρ (g*h)).asHom.hom p.2) = _
            simp only [map_mul]
            rfl } }
  property := by
    apply (@continuousSMul_iff_stabilizer_isOpen _ _ _ _ _ _ _ ⟨rfl⟩).mpr
    intro x
    have hx : Continuous (fun g : G ↦ (X.obj.ρ g).asHom.hom x.1) :=
      X.property.1.comp (continuous_id.prodMk continuous_const)
    have hy : Continuous (fun g : G ↦ (Y.obj.ρ g).asHom.hom x.2) :=
      Y.property.1.comp (continuous_id.prodMk continuous_const)
    change IsOpen {g : G | ((X.obj.ρ g).asHom.hom x.1, (Y.obj.ρ g).asHom.hom x.2) = x}
    convert (hx.isOpen_preimage {x.1} (isOpen_discrete _)).inter
      (hy.isOpen_preimage {x.2} (isOpen_discrete _)) using 1
    ext g
    exact Prod.ext_iff

private def pointFst (X Y : ContAction FintypeCat.{u} G) : pointProd X Y ⟶ X :=
  caHom (fun p ↦ p.1) (fun _ _ ↦ rfl)
private def pointSnd (X Y : ContAction FintypeCat.{u} G) : pointProd X Y ⟶ Y :=
  caHom (fun p ↦ p.2) (fun _ _ ↦ rfl)

private def pointUnit : ContAction FintypeCat.{u} G where
  obj := Action.trivial G (FintypeCat.of PUnit)
  property := ⟨continuous_snd⟩

end InternalModule
end FiniteActions

end CategoryTheory

end
