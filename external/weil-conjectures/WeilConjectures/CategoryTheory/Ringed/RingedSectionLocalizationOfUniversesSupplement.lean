/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationRing
import Mathlib.Algebra.Category.Ring.Adjunctions
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses

/-!
# Section localization with independent site universes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
The construction is the same sectionwise localization followed by sheafification.
This interface allows a site with different object and morphism universes. Sheafification
is parameterized by its existing instances in the chosen coefficient universe. The previous
small-category interface is retained by the public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

set_option linter.unusedSectionVars false in
/-- The sectionwise units form a section of the localization presheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: the restriction maps are ring homomorphisms and therefore preserve one. -/
theorem ringedSectionLocalizationPresheaf_one_naturalOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (ringedSectionLocalizationPresheafOfUniverses O s).map a
      (1 : ringedSectionLocalizationCarrierOfUniverses O s X) =
        (1 : ringedSectionLocalizationCarrierOfUniverses O s Y) := by
  exact (ringedSectionLocalizationMapOfUniverses O s a).map_one

/-- The canonical map from the ring sheaf to its localization as a module sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationUnitOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    ((ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun X ↦ (1 : ringedSectionLocalizationCarrierOfUniverses O s X))
        (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_naturalOfUniverses O s a)) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses O s))

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

/-- The localization restrictions preserve identities as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both maps extend the identity of R(U); uniqueness of localization lifts applies. -/
theorem ringedLocalizationRing_map_idOfUniverses (U : Cᵒᵖ) :
    ringedSectionLocalizationMapOfUniverses R s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMapOfUniverses]

/-- The localization restrictions preserve composites as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both composites extend the same restriction of R, by naturality of s;
uniqueness of localization lifts gives equality. -/
theorem ringedLocalizationRing_map_compOfUniverses {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ringedSectionLocalizationMapOfUniverses R s (f ≫ g) =
      (ringedSectionLocalizationMapOfUniverses R s g).comp
        (ringedSectionLocalizationMapOfUniverses R s f) := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMapOfUniverses, Functor.map_comp]

/-- The actual presheaf of commutative rings U ↦ R(U)[1/s(U)].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafOfUniverses : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (ringedSectionLocalizationCarrierOfUniverses R s U)
  map f := CommRingCat.ofHom (ringedSectionLocalizationMapOfUniverses R s f)
  map_id U := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_idOfUniverses R s U)
  map_comp f g := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_compOfUniverses R s f g)

/-- The section localization algebra maps commute with restrictions.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: each localization lift extends exactly the specified restriction map. -/
theorem ringedLocalizationRing_unit_naturalityOfUniverses {U V : Cᵒᵖ} (f : U ⟶ V) :
    R.obj.map f ≫
        CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s V)) =
      CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) ≫
        (ringedLocalizationRingPresheafOfUniverses R s).map f := by
  ext r
  simp [ringedLocalizationRingPresheafOfUniverses, ringedSectionLocalizationMapOfUniverses]

/-- The sectionwise algebra map into localization.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafUnitOfUniverses :
    R.obj ⟶ ringedLocalizationRingPresheafOfUniverses R s where
  app U := CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U))
  naturality _ _ f := ringedLocalizationRing_unit_naturalityOfUniverses R s f

/-- Sheafified section localization as a sheaf of commutative rings.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingOfUniverses : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (ringedLocalizationRingPresheafOfUniverses R s)

/-- The canonical map of ring sheaves from R to R[1/s].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingUnitOfUniverses : R ⟶ ringedLocalizationRingOfUniverses R s :=
  ⟨ringedLocalizationRingPresheafUnitOfUniverses R s ≫
    toSheafify J (ringedLocalizationRingPresheafOfUniverses R s)⟩

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

/- The additive sheafification has a canonical multiplication: multiply local representatives
and glue. Local injectivity makes the product independent of the representatives. The ring laws
and the compatibility of lifts are checked on covering sieves. This realizes the sheafification
argument in the comparison theorem below without identifying the site and coefficient universes. -/
namespace RingedLocalizationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {P : Cᵒᵖ ⥤ CommRingCat.{u}} {A : Sheaf J AddCommGrpCat.{u}}
variable (η : (P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ A.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

private lemma natural {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : P.obj X) :
    η.app Y (P.map f p) = A.obj.map f (η.app X p) :=
  NatTrans.naturality_apply η f p

private lemma ext {X : Cᵒᵖ} {x y : A.obj.obj X} (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop), S g → A.obj.map g.op x = A.obj.map g.op y) :
    x = y :=
  A.isSeparated _ _ hS x y (fun _ g hg ↦ h g hg)

private lemma image_ext {X : Cᵒᵖ} (a b c : A.obj.obj X) {x y : A.obj.obj X}
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop) (p q r : P.obj (op Y)),
      η.app _ p = A.obj.map g.op a → η.app _ q = A.obj.map g.op b →
      η.app _ r = A.obj.map g.op c → A.obj.map g.op x = A.obj.map g.op y) : x = y := by
  refine ext (Presheaf.imageSieve η a ⊓ Presheaf.imageSieve η b ⊓
    Presheaf.imageSieve η c) (J.intersection_covering (J.intersection_covering
      (Presheaf.imageSieve_mem J η a) (Presheaf.imageSieve_mem J η b))
      (Presheaf.imageSieve_mem J η c)) ?_
  rintro Y g ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, ⟨r, hr⟩⟩
  exact h g p q r hp hq hr

private lemma mul_eq {X : Cᵒᵖ} {p p' q q' : P.obj X}
    (hp : η.app X p = η.app X p') (hq : η.app X q = η.app X q') :
    η.app X (p * q) = η.app X (p' * q') := by
  refine ext _ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J η p p' hp)
    (Presheaf.equalizerSieve_mem J η q q' hq)) ?_
  rintro Y g ⟨hg, hg'⟩
  rw [← natural η, ← natural η]
  rw [(P.map g.op).hom.map_mul, (P.map g.op).hom.map_mul]
  have hg : P.map g.op p = P.map g.op p' := hg
  have hg' : P.map g.op q = P.map g.op q' := hg'
  rw [hg, hg']

private def mulFamily {X : Cᵒᵖ} (a b : A.obj.obj X) :
    Presieve.FamilyOfElements (A.obj ⋙ forget AddCommGrpCat.{u})
      (Presheaf.imageSieve η a ⊓ Presheaf.imageSieve η b).arrows :=
  fun Y _ h ↦ η.app _ ((show P.obj (op Y) from h.1.choose) *
    (show P.obj (op Y) from h.2.choose))

private lemma mulFamily_compatible {X : Cᵒᵖ} (a b : A.obj.obj X) :
    (mulFamily η a b).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  dsimp only [mulFamily]
  erw [← natural η, ← natural η]
  change η.app _ ((P.map g₁.op) (_ * _)) = η.app _ ((P.map g₂.op) (_ * _))
  rw [(P.map g₁.op).hom.map_mul, (P.map g₂.op).hom.map_mul]
  apply mul_eq η
  · rw [natural η, natural η,
      h₁.1.choose_spec, h₂.1.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  · rw [natural η, natural η,
      h₁.2.choose_spec, h₂.2.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]

private def mul {X : Cᵒᵖ} (a b : A.obj.obj X) : A.obj.obj X :=
  ((show Presieve.IsSheaf J (A.obj ⋙ forget AddCommGrpCat.{u}) from
    (isSheaf_iff_isSheaf_of_type J _).1
      ((sheafCompose J (forget AddCommGrpCat.{u})).obj A).property) _
      (J.intersection_covering (Presheaf.imageSieve_mem J η a)
        (Presheaf.imageSieve_mem J η b))).amalgamate
    (mulFamily η a b) (mulFamily_compatible η a b)

private lemma map_mul' {X : Cᵒᵖ} {Y : C} (a b : A.obj.obj X) (g : Y ⟶ X.unop)
    (p q : P.obj (op Y))
    (hp : η.app _ p = A.obj.map g.op a) (hq : η.app _ q = A.obj.map g.op b) :
    A.obj.map g.op (mul η a b) = η.app _ (p * q) := by
  have hS := J.intersection_covering (Presheaf.imageSieve_mem J η a)
    (Presheaf.imageSieve_mem J η b)
  refine ext _ (J.pullback_stable g hS) ?_
  intro Z h hh
  rw [← Functor.map_comp_apply, ← op_comp, mul]
  have hv := Presieve.IsSheafFor.valid_glue
    ((show Presieve.IsSheaf J (A.obj ⋙ forget AddCommGrpCat.{u}) from
      (isSheaf_iff_isSheaf_of_type J _).1
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj A).property) _ hS)
      (mulFamily_compatible η a b) (h ≫ g) hh
  change A.obj.map (h ≫ g).op _ = _ at hv
  rw [hv]
  rw [← natural η]
  change η.app _ (_ * _) = η.app _ ((P.map h.op) (p * q))
  rw [(P.map h.op).hom.map_mul]
  apply mul_eq η
  · rw [hh.1.choose_spec, natural η, hp,
      ← Functor.map_comp_apply, ← op_comp]
  · rw [hh.2.choose_spec, natural η, hq,
      ← Functor.map_comp_apply, ← op_comp]

private lemma mul_app {X : Cᵒᵖ} (p q : P.obj X) :
    mul η (η.app X p) (η.app X q) = η.app X (p * q) := by
  simpa using map_mul' η (η.app X p) (η.app X q) (𝟙 X.unop) p q (by simp) (by simp)

private lemma mul_natural {X Y : Cᵒᵖ} (f : X ⟶ Y) (a b : A.obj.obj X) :
    A.obj.map f (mul η a b) = mul η (A.obj.map f a) (A.obj.map f b) := by
  apply image_ext η (A.obj.map f a) (A.obj.map f b) 0
  intro Z g p q r hp hq hr
  rw [← Functor.map_comp_apply, ← f.op_unop, ← op_comp]
  rw [map_mul' η a b (g ≫ f.unop) p q (by simpa using hp) (by simpa using hq)]
  simpa using (map_mul' η (A.obj.map f a) (A.obj.map f b) g p q hp hq).symm

private lemma mul_comm' {X : Cᵒᵖ} (a b : A.obj.obj X) : mul η a b = mul η b a := by
  apply image_ext η a b 0
  intro Y g p q r hp hq hr
  rw [map_mul' η a b g p q hp hq, map_mul' η b a g q p hq hp, mul_comm]

private lemma mul_assoc' {X : Cᵒᵖ} (a b c : A.obj.obj X) :
    mul η (mul η a b) c = mul η a (mul η b c) := by
  apply image_ext η a b c
  intro Y g p q r hp hq hr
  rw [map_mul' η (mul η a b) c g (p * q) r (map_mul' η a b g p q hp hq).symm hr,
    map_mul' η a (mul η b c) g p (q * r) hp (map_mul' η b c g q r hq hr).symm,
    mul_assoc]

private lemma one_mul' {X : Cᵒᵖ} (a : A.obj.obj X) : mul η (η.app X (1 : P.obj X)) a = a := by
  apply image_ext η a 0 0
  intro Y g p q r hp hq hr
  rw [map_mul' η (η.app X (1 : P.obj X)) a g 1 p (by rw [← natural η]; simp) hp, one_mul, hp]

private lemma mul_add' {X : Cᵒᵖ} (a b c : A.obj.obj X) :
    mul η a (b + c) = mul η a b + mul η a c := by
  apply image_ext η a b c
  intro Y g p q r hp hq hr
  rw [(A.obj.map g.op).hom.map_add,
    map_mul' η a b g p q hp hq, map_mul' η a c g p r hp hr,
    map_mul' η a (b + c) g p (q + r) hp
      (by rw [(η.app _).hom.map_add, (A.obj.map g.op).hom.map_add, hq, hr]),
    mul_add, (η.app _).hom.map_add]

private lemma zero_mul' {X : Cᵒᵖ} (a : A.obj.obj X) : mul η 0 a = 0 := by
  apply image_ext η a 0 0
  intro Y g p q r hp hq hr
  rw [map_mul' η 0 a g 0 p (by simp) hp, zero_mul,
    (η.app _).hom.map_zero, (A.obj.map g.op).hom.map_zero]

@[instance_reducible]
private def ring (X : Cᵒᵖ) : CommRing (A.obj.obj X) where
  toAddCommGroup := inferInstance
  one := η.app X (1 : P.obj X)
  mul := mul η
  mul_assoc := mul_assoc' η
  mul_comm := mul_comm' η
  one_mul := one_mul' η
  mul_one a := (mul_comm' η a _).trans (one_mul' η a)
  right_distrib a b c := (mul_comm' η _ c).trans
    ((mul_add' η c a b).trans (congrArg₂ (· + ·) (mul_comm' η c a) (mul_comm' η c b)))
  left_distrib := mul_add' η
  zero_mul := zero_mul' η
  mul_zero a := (mul_comm' η a _).trans (zero_mul' η a)

private def ringPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} := by
  letI (X : Cᵒᵖ) := ring η X
  exact
    { obj X := CommRingCat.of (A.obj.obj X)
      map {X Y} f := CommRingCat.ofHom
        { toFun := A.obj.map f
          map_zero' := (A.obj.map f).hom.map_zero
          map_add' := (A.obj.map f).hom.map_add
          map_one' := by
            change A.obj.map f (η.app X (1 : P.obj X)) = η.app Y (1 : P.obj Y)
            rw [← natural η]
            exact congrArg (η.app Y) (P.map f).hom.map_one
          map_mul' := mul_natural η f }
      map_id X := by ext x; exact ConcreteCategory.congr_hom (A.obj.map_id X) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (A.obj.map_comp f g) x }

private lemma ring_isSheaf (F : Cᵒᵖ ⥤ CommRingCat.{u})
    (hF : Presheaf.IsSheaf J
      (F ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) :
    Presheaf.IsSheaf J F := by
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}
  let B : Sheaf J AddCommGrpCat.{u} := ⟨F ⋙ U, hF⟩
  intro E X S hS fs hfs
  let as : Presieve.FamilyOfElements
      (B.obj ⋙ coyoneda.obj (op (AddCommGrpCat.of E))) S.arrows :=
    fun Y f hf ↦ AddCommGrpCat.ofHom (fs f hf).hom.toAddMonoidHom
  have has : as.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc
    exact congrArg (fun (k : E ⟶ F.obj (op Z)) ↦ AddCommGrpCat.ofHom k.hom.toAddMonoidHom)
      (hfs g₁ g₂ h₁ h₂ hc)
  obtain ⟨a, ha, hau⟩ := hF (AddCommGrpCat.of E) S hS as has
  change AddCommGrpCat.of E ⟶ B.obj.obj (op X) at a
  have hap (Y : C) (f : Y ⟶ X) (hf : S f) (x : E) :
      F.map f.op (a x) = (show E ⟶ F.obj (op Y) from fs f hf) x :=
    ConcreteCategory.congr_hom (ha f hf) x
  have hsep := B.isSeparated X S hS
  let r : E ⟶ F.obj (op X) := CommRingCat.ofHom
    { a.hom with
      map_one' := by
        apply hsep
        intro Y f hf
        change F.map f.op (a 1) = F.map f.op 1
        rw [hap Y f hf, (F.map f.op).hom.map_one, (fs f hf).hom.map_one]
      map_mul' := by
        intro x y
        apply hsep
        intro Y f hf
        change F.map f.op (a (x * y)) = F.map f.op
          ((show F.obj (op X) from a x) * (show F.obj (op X) from a y))
        rw [(F.map f.op).hom.map_mul, hap Y f hf,
          hap Y f hf, hap Y f hf, (fs f hf).hom.map_mul] }
  refine ⟨r, ?_, ?_⟩
  · intro Y f hf
    change r ≫ F.map f.op = fs f hf
    ext x
    exact hap Y f hf x
  · intro r' hr'
    change E ⟶ F.obj (op X) at r'
    apply CommRingCat.hom_ext
    apply RingHom.toAddMonoidHom_injective
    change (AddCommGrpCat.ofHom r'.hom.toAddMonoidHom).hom = a.hom
    congr 1
    apply hau
    intro Y f hf
    exact congrArg (fun (k : E ⟶ F.obj (op Y)) ↦
      AddCommGrpCat.ofHom k.hom.toAddMonoidHom) (hr' f hf)

private def ringSheaf : Sheaf J CommRingCat.{u} :=
  ⟨ringPresheaf η, ring_isSheaf _ A.property⟩

private def ringUnit : P ⟶ (ringSheaf η).obj := by
  letI (X : Cᵒᵖ) := ring η X
  exact
    { app X := CommRingCat.ofHom
        { toFun := η.app X
          map_zero' := (η.app X).hom.map_zero
          map_add' := (η.app X).hom.map_add
          map_one' := rfl
          map_mul' := fun p q ↦ (mul_app η p q).symm }
      naturality X Y f := by ext x; exact natural η f x }

private lemma lift_mul {B : Sheaf J CommRingCat.{u}}
    (t : P ⟶ B.obj) (k : A.obj ⟶ B.obj ⋙
      forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (hk : η ≫ k = Functor.whiskerRight t
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    {X : Cᵒᵖ} (a b : A.obj.obj X) :
    k.app X (mul η a b) =
      (show B.obj.obj X from k.app X a) * (show B.obj.obj X from k.app X b) := by
  have hk' (U : Cᵒᵖ) (p : P.obj U) : k.app U (η.app U p) = t.app U p :=
    ConcreteCategory.congr_hom (congr_app hk U) p
  apply ((sheafCompose J (forget CommRingCat)).obj B).isSeparated _ _
    (J.intersection_covering
    (Presheaf.imageSieve_mem J η a) (Presheaf.imageSieve_mem J η b))
  rintro Y g ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  change B.obj.map g.op (k.app X (mul η a b)) =
    B.obj.map g.op ((show B.obj.obj X from k.app X a) *
      (show B.obj.obj X from k.app X b))
  have hn (z : A.obj.obj X) :
      B.obj.map g.op (k.app X z) = k.app _ (A.obj.map g.op z) :=
    (NatTrans.naturality_apply k g.op z).symm
  rw [hn, map_mul' η a b g p q hp hq, hk', (B.obj.map g.op).hom.map_mul,
    hn, hn, ← hp, ← hq, hk', hk', (t.app _).hom.map_mul]

private lemma sheafifyRingUnit_locallyBijective
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (Q : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight (toSheafify J Q)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) ∧
    Presheaf.IsLocallySurjective J (Functor.whiskerRight (toSheafify J Q)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) := by
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}
  let A := (presheafToSheaf J AddCommGrpCat.{u}).obj (Q ⋙ U)
  let η : Q ⋙ U ⟶ A.obj := toSheafify J (Q ⋙ U)
  have : Presheaf.IsLocallyInjective J η := inferInstance
  have : Presheaf.IsLocallySurjective J η := inferInstance
  let T := ringSheaf η
  let t : Q ⟶ T.obj := ringUnit η
  let B := (presheafToSheaf J CommRingCat.{u}).obj Q
  let ι : Q ⟶ B.obj := toSheafify J Q
  have hB : Presheaf.IsSheaf J (B.obj ⋙ U) :=
    ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)).property
  let k : A.obj ⟶ B.obj ⋙ U := sheafifyLift J (Functor.whiskerRight ι U) hB
  have hk : η ≫ k = Functor.whiskerRight ι U := toSheafify_sheafifyLift _ _ _
  let kR : T.obj ⟶ B.obj :=
    { app X := @CommRingCat.ofHom (T.obj.obj X) (B.obj.obj X)
        (T.obj.obj X).commRing (B.obj.obj X).commRing
        { toFun := k.app X
          map_zero' := (k.app X).hom.map_zero
          map_add' := (k.app X).hom.map_add
          map_one' := by
            change k.app X (η.app X (1 : Q.obj X)) = (1 : B.obj.obj X)
            exact (ConcreteCategory.congr_hom (congr_app hk X) (1 : Q.obj X)).trans
              ((ι.app X).hom.map_one)
          map_mul' := lift_mul η ι k hk }
      naturality X Y f := by ext x; exact NatTrans.naturality_apply k f x }
  have htk : t ≫ kR = ι := by
    ext X x
    exact ConcreteCategory.congr_hom (congr_app hk X) x
  let h : B.obj ⟶ T.obj := sheafifyLift J t T.property
  have hh : ι ≫ h = t := toSheafify_sheafifyLift _ _ _
  have hhk : h ≫ kR = 𝟙 B.obj := by
    apply sheafify_hom_ext J _ _ B.property
    change ι ≫ (h ≫ kR) = ι ≫ 𝟙 _
    rw [← Category.assoc, hh, htk, Category.comp_id]
  let hA : B.obj ⋙ U ⟶ A.obj := Functor.whiskerRight h U
  have hhA : Functor.whiskerRight ι U ≫ hA = η := by
    exact congrArg (fun a ↦ Functor.whiskerRight a U) hh
  have hkhA : k ≫ hA = 𝟙 A.obj := by
    apply sheafify_hom_ext J _ _ A.property
    change η ≫ (k ≫ hA) = η ≫ 𝟙 _
    rw [← Category.assoc, hk, hhA, Category.comp_id]
  have hhAk : hA ≫ k = 𝟙 (B.obj ⋙ U) := by
    exact congrArg (fun a ↦ Functor.whiskerRight a U) hhk
  have : IsIso k := ⟨⟨hA, hkhA, hhAk⟩⟩
  rw [← hk]
  constructor <;> infer_instance

variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private lemma comparison {B : Sheaf J RingCat.{u}}
    (P : PresheafOfModules.{u} B.obj) (A : SheafOfModules.{u} B)
    (φ : P ⟶ A.val)
    [PresheafOfModules.IsLocallyInjective J φ]
    [PresheafOfModules.IsLocallySurjective J φ] :
    ∃ e : A ≅ (PresheafOfModules.sheafification (𝟙 B.obj)).obj P,
      φ ≫ e.hom.val = (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P := by
  let S := (PresheafOfModules.sheafification (𝟙 B.obj)).obj P
  let η : P ⟶ S.val := (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P
  let g : S ⟶ A := (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).symm φ
  have hg : η ≫ g.val = φ := by
    exact (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).apply_symm_apply φ
  let f : A ⟶ S := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (f := φ) S.isSheaf).symm η⟩
  have hf : φ ≫ f.val = η := by
    exact (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) S.isSheaf).apply_symm_apply η
  have hfg : f ≫ g = 𝟙 A := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
    change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 S := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).injective
    change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 S.val
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end RingedLocalizationComparison

end

/-- The ring-sheaf construction is the original module sheafification, with the
canonical identification on every local fraction.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both underlying module sheaves represent restriction-compatible linear
maps out of the section-localization presheaf. Ring sheafification carries the
sectionwise scalar action, since multiplication and its identities sheafify.
The two sheafification universal properties give mutually inverse module maps;
they agree on every section of the presheaf, giving the displayed normalization. -/
theorem ringedLocalizationRing_moduleComparisonOfUniverses :
    ∃ e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          (ringedLocalizationRingUnitOfUniverses R s))).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R s))) ≅ ringedSectionLocalizationOfUniverses R s,
      ∀ (U : Cᵒᵖ) (x : ringedSectionLocalizationCarrierOfUniverses R s U),
        e.hom.val.app U ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R s)).app U x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              (ringedSectionLocalizationPresheafOfUniverses R s)).app U) x := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  classical
  obtain ⟨hinj, hsurj⟩ :=
    RingedLocalizationComparison.sheafifyRingUnit_locallyBijective (J := J)
      (ringedLocalizationRingPresheafOfUniverses R s)
  have := hinj
  have := hsurj
  let P := ringedSectionLocalizationPresheafOfUniverses R s
  let A := (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (ringedLocalizationRingUnitOfUniverses R s))).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R s)))
  let ι := toSheafify J (ringedLocalizationRingPresheafOfUniverses R s)
  let φ : P ⟶ A.val := PresheafOfModules.homMk
    (Functor.whiskerRight (toSheafify J (ringedLocalizationRingPresheafOfUniverses R s))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
        intro U r x
        change R.obj.obj U at r
        change ringedSectionLocalizationCarrierOfUniverses R s U at x
        change (ι.app U).hom (r • x) = _
        rw [Algebra.smul_def, (ι.app U).hom.map_mul]
        rfl)
  have : PresheafOfModules.IsLocallyInjective J φ := by assumption
  have : PresheafOfModules.IsLocallySurjective J φ := by assumption
  obtain ⟨e, he⟩ := RingedLocalizationComparison.comparison P A φ
  refine ⟨e, ?_⟩
  intro U x
  exact DFunLike.congr_fun (congrArg (fun k ↦ (k.app U).hom) he) x

end CategoryTheory
