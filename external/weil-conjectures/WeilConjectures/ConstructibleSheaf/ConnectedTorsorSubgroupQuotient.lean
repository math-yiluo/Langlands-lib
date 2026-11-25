/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-!
# Subgroup quotients of connected finite etale torsors

Source: Stacks Project, proof of Tag 0A3R, and Tag 0BND.
(blueprint: lemma-covers-degree-prime-to-ell--1)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

private theorem torsor_action_injective
    {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}}
    (c : Scheme.GaloisCover G Y) {Ω : Type u} [Field Ω]
    (a : Spec (.of Ω) ⟶ c.P) : Function.Injective (fun g ↦ a ≫ c.smul g) := by
  have := c.isIso_sigmaDesc
  intro g h he
  have hι : a ≫ Sigma.ι (fun _ : G ↦ c.P) g =
      a ≫ Sigma.ι (fun _ : G ↦ c.P) h := by
    rw [← cancel_mono (Sigma.desc fun g : G ↦
      pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
        (by simp [c.smul_π]))]
    apply pullback.hom_ext <;> simp [Category.assoc, he]
  have hp := congrArg (fun k : Spec (.of Ω) ⟶ ∐ (fun _ : G ↦ c.P) ↦ k default) hι
  simp only [Scheme.Hom.comp_apply] at hp
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hp)

private theorem singleObj_orbit_eqvGen
    {G : Type u} [Group G] {C : Type*} [Category C]
    (D : SingleObj G ⥤ C) (F : C ⥤ FintypeCat.{u})
    {x y : F.obj (D.obj (SingleObj.star G))}
    (h : Relation.EqvGen (fun x y ↦ ∃ g : G, F.map (D.map g) x = y) x y) :
    ∃ g : G, F.map (D.map g) x = y := by
  induction h with
  | rel _ _ h => exact h
  | refl x =>
    refine ⟨1, ?_⟩
    change F.map (D.map (𝟙 (SingleObj.star G))) x = x
    simp
  | symm x y _ ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, ← FintypeCat.comp_apply, ← F.map_comp, ← D.map_comp]
    have hgg : (g : SingleObj.star G ⟶ SingleObj.star G) ≫
        (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G) = 𝟙 (SingleObj.star G) := by
      change g⁻¹ * g = 1
      exact inv_mul_cancel g
    rw [hgg, D.map_id, F.map_id]
    rfl
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨g, hg⟩ := ih₁
    obtain ⟨k, hk⟩ := ih₂
    refine ⟨k * g, ?_⟩
    rw [← hk, ← hg, ← FintypeCat.comp_apply, ← F.map_comp, ← D.map_comp]
    rfl

private theorem torsor_card_geometricFiber
    {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}}
    (t : Scheme.GaloisCover G Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) : Nat.card (t.π.GeometricFiber s) = Nat.card G := by
  classical
  have := t.isFinite
  have := t.etale
  have := t.surjective
  have := t.isIso_sigmaDesc
  obtain ⟨a, ha⟩ := t.π.exists_lift_of_isSepClosed s
    ⟨default, t.π.surjective (s default)⟩
  let f : G → t.π.GeometricFiber s := fun g ↦ ⟨a ≫ t.smul g, by
    rw [Category.assoc, t.smul_π, ha]⟩
  have hinj : Function.Injective f := fun g h he ↦
    torsor_action_injective t a (congrArg Subtype.val he)
  have hsurj : Function.Surjective f := by
    intro b
    let D := Sigma.desc fun g : G ↦
      pullback.lift (f := t.π) (g := t.π) (t.smul g) (𝟙 t.P)
        (by simp [t.smul_π])
    let z : Spec (.of Ω) ⟶ pullback t.π t.π :=
      pullback.lift b.val a (b.property.trans ha.symm)
    obtain ⟨g, l, hl⟩ := exists_comp_sigmaι_eq_of_subsingleton (z ≫ inv D)
    have h : l ≫ pullback.lift (f := t.π) (g := t.π) (t.smul g) (𝟙 t.P)
        (by simp [t.smul_π]) = z := by
      rw [← Sigma.ι_comp_desc (fun g : G ↦
        pullback.lift (f := t.π) (g := t.π) (t.smul g) (𝟙 t.P)
          (by simp [t.smul_π])) g, ← Category.assoc, hl]
      simp [D]
    have h₁ := congrArg (· ≫ pullback.fst t.π t.π) h
    have h₂ := congrArg (· ≫ pullback.snd t.π t.π) h
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      Category.comp_id, z] at h₁ h₂
    rw [h₂] at h₁
    exact ⟨g, Subtype.ext h₁⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

private theorem card_geometricFiber_comp
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) [IsFinite p] [IsFinite v]
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ Z) (d : ℕ)
    (h : ∀ b : v.GeometricFiber s, Nat.card (p.GeometricFiber b.val) = d) :
    Nat.card ((p ≫ v).GeometricFiber s) = Nat.card (v.GeometricFiber s) * d := by
  classical
  let e : (p ≫ v).GeometricFiber s ≃
      (b : v.GeometricFiber s) × p.GeometricFiber b.val :=
    { toFun a := ⟨⟨a.val ≫ p, by rw [Category.assoc]; exact a.property⟩, ⟨a.val, rfl⟩⟩
      invFun a := ⟨a.2.val, by rw [← Category.assoc, a.2.property]; exact a.1.property⟩
      left_inv a := rfl
      right_inv a := by
        rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
        dsimp at ha
        subst b
        rfl }
  let := Fintype.ofFinite (v.GeometricFiber s)
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- The quotient of a connected finite Q-torsor by H is connected, of geometric
fibre cardinality [Q:H], and has the same total space as an H-torsor.
Source: Stacks Project, Tag 0A3R, proof at T = Y/H; Tag 0BND (1), (3).
(blueprint: lemma-covers-degree-prime-to-ell--1)

Proof:
1. Choose a geometric point of U and a lift to c.P. The fibre is the regular
Q-set, with the fundamental group acting through a surjection onto Q because
c.P is connected. The quotient of the regular fibre by the deck action of H is the coset set
H\Q (identified by inversion with Q/H). The commuting monodromy action remains
transitive. This finite continuous fundamental-group set corresponds under the finite etale
Galois equivalence to a connected finite etale map v : V -> U.
2. The quotient map c.P -> V is induced by the equivariant projection from the
regular fibre to its H-orbits.
The H action on c.P gives an H-torsor over V: on the chosen geometric fibre
the map H times Q -> Q times_(H\Q) Q is a bijection. The fibre functor reflects
isomorphisms, so the corresponding scheme map is an isomorphism. The quotient
is surjective because its image on the fibre is surjective. Use the same total
space for cH; e can then be the identity, and the displayed square commutes.
3. Every geometric fibre of v has the cardinality of H\Q: fibre functors at
any two geometric points of connected U are isomorphic. This applies also to
separably closed fields, since finite etale algebras split over such fields.
Its cardinality is the subgroup index. The construction works for H = 1,
H = Q, and Q = 1 without a nonzero-rank hypothesis. -/
theorem Scheme.GaloisCover.exists_connected_subgroup_quotient
    {U : Scheme.{u}} [ConnectedSpace U]
    (Q : Type u) [Group Q] [Finite Q]
    (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) [ConnectedSpace c.P]
    (H : Subgroup Q) :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v)
      (_ : ConnectedSpace V),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = H.index) ∧
      ∃ (cH : Scheme.GaloisCover (ULift.{u + 1} H) V) (_ : ConnectedSpace cH.P)
        (e : cH.P ≅ c.P), e.hom ≫ c.π = cH.π ≫ v := by
  classical
  have := c.etale
  have := c.isFinite
  let P : U.FiniteEtale := ⟨Etale.mk c.π, c.isFinite⟩
  let τ : H →* End P :=
    { toFun h := End.of (ObjectProperty.homMk
        (MorphismProperty.Over.homMk (c.smul ⟨h.val⟩) (c.smul_π ⟨h.val⟩)))
      map_one' := End.ext (Scheme.FiniteEtale.hom_ext c.one_smul)
      map_mul' h k := End.ext (Scheme.FiniteEtale.hom_ext (c.mul_smul ⟨h.val⟩ ⟨k.val⟩)) }
  let D := SingleObj.functor τ
  let T := (Scheme.FiniteEtale.quotientCocone D).pt
  let φ : P ⟶ T := (Scheme.FiniteEtale.quotientCocone D).ι.app (SingleObj.star H)
  let V := T.obj.left
  let v : V ⟶ U := T.obj.hom
  let p : c.P ⟶ V := φ.hom.left
  have hvf : IsFinite v := T.property
  have hve : Etale v := T.obj.prop
  have hpf : IsFinite p := Scheme.FiniteEtale.isFinite_hom_left φ
  have hpe : Etale p := Scheme.FiniteEtale.etale_hom_left φ
  have hpv : p ≫ v = c.π := Scheme.FiniteEtale.hom_left_comp φ
  have hsp (h : H) : c.smul ⟨h.val⟩ ≫ p = p := by
    have hn := (Scheme.FiniteEtale.quotientCocone D).ι.naturality
      (X := SingleObj.star H) (Y := SingleObj.star H) h
    change (τ h).asHom ≫ φ = φ ≫ 𝟙 T at hn
    rw [Category.comp_id] at hn
    exact congrArg (fun f ↦ f.hom.left) hn
  obtain ⟨a⟩ := (inferInstance : Nonempty U)
  let s := Spec.map (CommRingCat.ofHom (algebraMap (U.residueField a)
    (AlgebraicClosure (U.residueField a)))) ≫ U.fromSpecResidueField a
  have hps : Function.Surjective p :=
    Scheme.FiniteEtale.surjective_of_surjective_fiber s φ
      (Scheme.FiniteEtale.fiber_quotientCocone D s).1
  have : Surjective p := ⟨hps⟩
  have : ConnectedSpace V := hps.connectedSpace p.continuous
  let PV : V.FiniteEtale := ⟨Etale.mk p, hpf⟩
  let α (h : ULift.{u + 1} H) : PV ⟶ PV := ObjectProperty.homMk
    (MorphismProperty.Over.homMk (c.smul ⟨h.down.val⟩) (hsp h.down))
  obtain ⟨b⟩ := (inferInstance : Nonempty V)
  let t := Spec.map (CommRingCat.ofHom (algebraMap (V.residueField b)
    (AlgebraicClosure (V.residueField b)))) ≫ V.fromSpecResidueField b
  have huniq : ∀ x y : (Scheme.FiniteEtale.fiber t).obj PV,
      ∃! h, (Scheme.FiniteEtale.fiber t).map (α h) x = y := by
    intro x y
    have hx : x.left ≫ p = t := Scheme.FiniteEtale.fiber_left_comp t x
    have hy : y.left ≫ p = t := Scheme.FiniteEtale.fiber_left_comp t y
    let xU : (Scheme.FiniteEtale.fiber (t ≫ v)).obj P :=
      Over.homMk x.left (by
        change x.left ≫ c.π = t ≫ v
        rw [← hpv, ← Category.assoc, hx])
    let yU : (Scheme.FiniteEtale.fiber (t ≫ v)).obj P :=
      Over.homMk y.left (by
        change y.left ≫ c.π = t ≫ v
        rw [← hpv, ← Category.assoc, hy])
    have he : (Scheme.FiniteEtale.fiber (t ≫ v)).map φ xU =
        (Scheme.FiniteEtale.fiber (t ≫ v)).map φ yU := by
      apply Scheme.FiniteEtale.fiber_ext
      change x.left ≫ p = y.left ≫ p
      rw [hx, hy]
    obtain ⟨h, hh⟩ := singleObj_orbit_eqvGen D (Scheme.FiniteEtale.fiber (t ≫ v))
      (((Scheme.FiniteEtale.fiber_quotientCocone D (t ≫ v)).2 xU yU).mp he)
    have hh' : x.left ≫ c.smul ⟨h.val⟩ = y.left :=
      congrArg (fun q ↦ q.left) hh
    refine ⟨⟨h⟩, Scheme.FiniteEtale.fiber_ext t hh', ?_⟩
    intro k hk
    have hk' : x.left ≫ c.smul ⟨k.down.val⟩ = y.left :=
      congrArg (fun q ↦ q.left) hk
    exact ULift.ext (Subtype.ext (congrArg ULift.down
      (torsor_action_injective c x.left (hk'.trans hh'.symm))))
  have hiso := Scheme.FiniteEtale.isIso_sigmaDesc_of_existsUnique t PV α huniq
  let cH : Scheme.GaloisCover (ULift.{u + 1} H) V :=
    { P := c.P
      π := p
      isFinite := hpf
      etale := hpe
      surjective := ⟨hps⟩
      smul h := c.smul ⟨h.down.val⟩
      smul_π h := hsp h.down
      one_smul := c.one_smul
      mul_smul h k := c.mul_smul ⟨h.down.val⟩ ⟨k.down.val⟩
      isIso_sigmaDesc := hiso }
  refine ⟨V, v, hvf, hve, inferInstance, ?_, cH, inferInstance, Iso.refl _, ?_⟩
  · intro Ω _ _ z
    have hcard := card_geometricFiber_comp p v z (Nat.card H) (fun q ↦ by
      simpa only [Nat.card_ulift] using torsor_card_geometricFiber cH q.val)
    rw [hpv, torsor_card_geometricFiber c z, Nat.card_ulift, ← H.index_mul_card] at hcard
    exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) hcard).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using hpv.symm

end AlgebraicGeometry
