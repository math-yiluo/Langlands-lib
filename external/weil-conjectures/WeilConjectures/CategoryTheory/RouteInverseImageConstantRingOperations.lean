/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RouteInverseImageConstantSetComparison
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Ring operations of the comparison on a single constant ring. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Ring-operation part of an inverse-image lift.

Source: Stacks Project, `sites.tex`, Tag 00YV
(auxiliary; not a blueprint node). -/
structure RingInverseImage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (R : Sheaf JC CommRingCat.{u})
    (RI : Sheaf JD CommRingCat.{u}) where
  ringUnderlying : L.obj ((sheafCompose JC (forget CommRingCat)).obj R) ≅
    (sheafCompose JD (forget CommRingCat)).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1

private abbrev ringSets {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget CommRingCat)).obj R

private noncomputable def constantMap
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u})
    (X : Type u) (f : X → A) :
    (constantSheaf J (Type u)).obj X ⟶ ringSets ((constantSheaf J CommRingCat).obj A) :=
  (constantSheaf J (Type u)).map (TypeCat.ofHom f) ≫
    (constantCommuteCompose J (forget CommRingCat)).inv.app A

private theorem coeff_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u}) (U : Cᵒᵖ) (a : A) :
    ((constantCommuteCompose J (forget CommRingCat)).inv.app A).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := by
  have h := sheafComposeIso_hom_fac J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv) ≫
    (sheafifyComposeIso J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)).hom).app U) a = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

private theorem constantMap_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u})
    (X : Type u) (f : X → A) (U : Cᵒᵖ) (x : X) :
    (constantMap J A X f).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U (f x) := by
  have h : ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app U (f x) :=
    (congrArg (fun g ↦ g.app U x)
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm
  exact (congrArg
    (((constantCommuteCompose J (forget CommRingCat)).inv.app A).hom.app U) h).trans
      (coeff_unit J A U (f x))

private noncomputable def addMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {T : Sheaf J (Type u)}
    (a b : T ⟶ ringSets R) : T ⟶ ringSets R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦
        @id (R.obj.obj U) (a.hom.app U x) + @id (R.obj.obj U) (b.hom.app U x))
     naturality := by
       intro U V f
       ext x
       have ha := congrArg (fun h ↦ h x) (a.hom.naturality f)
       have hb := congrArg (fun h ↦ h x) (b.hom.naturality f)
       change _ = (R.obj.map f).hom (_ + _)
       rw [map_add]
       exact congrArg₂ (fun x y : R.obj.obj V ↦ x + y) ha hb }⟩

private noncomputable def mulMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {T : Sheaf J (Type u)}
    (a b : T ⟶ ringSets R) : T ⟶ ringSets R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦
        @id (R.obj.obj U) (a.hom.app U x) * @id (R.obj.obj U) (b.hom.app U x))
     naturality := by
       intro U V f
       ext x
       have ha := congrArg (fun h ↦ h x) (a.hom.naturality f)
       have hb := congrArg (fun h ↦ h x) (b.hom.naturality f)
       change _ = (R.obj.map f).hom (_ * _)
       rw [map_mul]
       exact congrArg₂ (fun x y : R.obj.obj V ↦ x * y) ha hb }⟩

private theorem constantMap_add
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u})
    (X : Type u) (f g : X → A) :
    constantMap J A X (fun x ↦ f x + g x) =
      addMap ((constantSheaf J CommRingCat).obj A)
        (constantMap J A X f) (constantMap J A X g) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (ringSets ((constantSheaf J CommRingCat).obj A)).property
  ext U x
  change (constantMap J A X (fun x ↦ f x + g x)).hom.app U _ =
    @id (((constantSheaf J CommRingCat).obj A).obj.obj U)
      ((constantMap J A X f).hom.app U _) +
    @id (((constantSheaf J CommRingCat).obj A).obj.obj U)
      ((constantMap J A X g).hom.app U _)
  erw [constantMap_unit, constantMap_unit, constantMap_unit]
  exact map_add ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U).hom _ _

private theorem constantMap_mul
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u})
    (X : Type u) (f g : X → A) :
    constantMap J A X (fun x ↦ f x * g x) =
      mulMap ((constantSheaf J CommRingCat).obj A)
        (constantMap J A X f) (constantMap J A X g) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (ringSets ((constantSheaf J CommRingCat).obj A)).property
  ext U x
  change (constantMap J A X (fun x ↦ f x * g x)).hom.app U _ =
    @id (((constantSheaf J CommRingCat).obj A).obj.obj U)
      ((constantMap J A X f).hom.app U _) *
    @id (((constantSheaf J CommRingCat).obj A).obj.obj U)
      ((constantMap J A X g).hom.app U _)
  erw [constantMap_unit, constantMap_unit, constantMap_unit]
  exact map_mul ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U).hom _ _

private noncomputable def coeffPair
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u}) :=
  prod.lift (constantMap J A (A × A) _root_.Prod.fst) (constantMap J A (A × A) _root_.Prod.snd)

private instance coeffPair_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u}) :
    IsIso (coeffPair J A) := by
  have h : coeffPair J A =
      (constantSheaf J (Type u)).map (Types.binaryProductIso (A : Type u) A).inv ≫
      prodComparison (constantSheaf J (Type u)) (A : Type u) A ≫
      prod.map ((constantCommuteCompose J (forget CommRingCat)).inv.app A)
        ((constantCommuteCompose J (forget CommRingCat)).inv.app A) := by
    apply prod.hom_ext
    · simp only [coeffPair, constantMap, Category.assoc, prod.lift_fst]
      erw [prod.map_fst, prodComparison_fst_assoc, ← Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_fst]
    · simp only [coeffPair, constantMap, Category.assoc, prod.lift_snd]
      erw [prod.map_snd, prodComparison_snd_assoc, ← Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_snd]
  rw [h]
  have : PreservesFiniteLimits (constantSheaf J (Type u)) :=
    comp_preservesFiniteLimits _ _
  infer_instance

private theorem constantMap_comparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u))
    (A : CommRingCat.{u}) (X : Type u) (f : X → A) :
    L.map (constantMap JC A X f) ≫
      (constantRingSetComparison JC JD L kappa).hom.app A =
        kappa.hom.app X ≫ constantMap JD A X f := by
  change L.map ((constantSheaf JC (Type u)).map (TypeCat.ofHom f) ≫
    (constantCommuteCompose JC (forget CommRingCat)).inv.app A) ≫
      (L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
        kappa.hom.app A ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc
    ((constantCommuteCompose JC (forget CommRingCat)).inv.app A)
    ((constantCommuteCompose JC (forget CommRingCat)).hom.app A),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have h := kappa.hom.naturality (TypeCat.ofHom f)
  change L.map ((constantSheaf JC (Type u)).map (TypeCat.ofHom f)) ≫
    kappa.hom.app A = kappa.hom.app X ≫
      (constantSheaf JD (Type u)).map (TypeCat.ofHom f) at h
  simpa only [Category.assoc, constantMap] using congrArg
    (fun g ↦ g ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) h

private noncomputable def sectionPair
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type u)) (U : Cᵒᵖ) (x : X.obj.obj U) (y : Y.obj.obj U) :
    (X ⨯ Y).obj.obj U :=
  (prod.lift (CartesianMonoidalCategory.fst X Y)
    (CartesianMonoidalCategory.snd X Y)).hom.app U (x, y)

private theorem sectionPair_fst
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type u)) (U : Cᵒᵖ) (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod.fst : X ⨯ Y ⟶ X).hom.app U (sectionPair X Y U x y) = x :=
  congrArg (fun f ↦ f.hom.app U (x, y))
    (prod.lift_fst (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem sectionPair_snd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type u)) (U : Cᵒᵖ) (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod.snd : X ⨯ Y ⟶ Y).hom.app U (sectionPair X Y U x y) = y :=
  congrArg (fun f ↦ f.hom.app U (x, y))
    (prod.lift_snd (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem lift_constant_pair
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)) [PreservesFiniteLimits L]
    (A : CommRingCat.{u}) (RI : Sheaf JD CommRingCat.{u})
    (e : RingInverseImage L ((constantSheaf JC CommRingCat).obj A) RI)
    (U : Dᵒᵖ) (x y : RI.obj.obj U) :
    ∃ p : (L.obj ((constantSheaf JC (Type u)).obj (A × A))).obj.obj U,
      (L.map (constantMap JC A (A × A) _root_.Prod.fst) ≫ e.ringUnderlying.hom).hom.app U p = x ∧
      (L.map (constantMap JC A (A × A) _root_.Prod.snd) ≫
        e.ringUnderlying.hom).hom.app U p = y := by
  let q := L.map (coeffPair JC A) ≫
    prodComparison L (ringSets ((constantSheaf JC CommRingCat).obj A))
      (ringSets ((constantSheaf JC CommRingCat).obj A)) ≫
    prod.map e.ringUnderlying.hom e.ringUnderlying.hom
  have : IsIso q := by dsimp [q]; infer_instance
  let z := sectionPair (ringSets RI) (ringSets RI) U x y
  let p := (inv q).hom.app U z
  have hp : q.hom.app U p = z :=
    congrArg (fun h ↦ h.hom.app U z) (IsIso.inv_hom_id q)
  have hfst : q ≫ prod.fst =
      L.map (constantMap JC A (A × A) _root_.Prod.fst) ≫ e.ringUnderlying.hom := by
    simp only [q, Category.assoc, prod.map_fst, prodComparison_fst_assoc,
      ← L.map_comp_assoc, coeffPair, prod.lift_fst]
  have hsnd : q ≫ prod.snd =
      L.map (constantMap JC A (A × A) _root_.Prod.snd) ≫ e.ringUnderlying.hom := by
    simp only [q, Category.assoc, prod.map_snd, prodComparison_snd_assoc,
      ← L.map_comp_assoc, coeffPair, prod.lift_snd]
  refine ⟨p, ?_, ?_⟩
  · rw [← hfst]
    change (prod.fst : ringSets RI ⨯ ringSets RI ⟶ ringSets RI).hom.app U
      (q.hom.app U p) = x
    rw [hp]
    exact sectionPair_fst (ringSets RI) (ringSets RI) U x y
  · rw [← hsnd]
    change (prod.snd : ringSets RI ⨯ ringSets RI ⟶ ringSets RI).hom.app U
      (q.hom.app U p) = y
    rw [hp]
    exact sectionPair_snd (ringSets RI) (ringSets RI) U x y

private theorem comparison_binary
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)) [PreservesFiniteLimits L]
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u))
    (A : CommRingCat.{u}) (RI : Sheaf JD CommRingCat.{u})
    (e : RingInverseImage L ((constantSheaf JC CommRingCat).obj A) RI)
    (op : A × A → A)
    (opD : ∀ U : Dᵒᵖ, ((constantSheaf JD CommRingCat).obj A).obj.obj U →
      ((constantSheaf JD CommRingCat).obj A).obj.obj U →
      ((constantSheaf JD CommRingCat).obj A).obj.obj U)
    (opI : ∀ U : Dᵒᵖ, RI.obj.obj U → RI.obj.obj U → RI.obj.obj U)
    (hD : ∀ U p, (constantMap JD A (A × A) op).hom.app U p =
      opD U ((constantMap JD A (A × A) _root_.Prod.fst).hom.app U p)
        ((constantMap JD A (A × A) _root_.Prod.snd).hom.app U p))
    (hI : ∀ U p,
      (L.map (constantMap JC A (A × A) op) ≫ e.ringUnderlying.hom).hom.app U p =
        opI U
          ((L.map (constantMap JC A (A × A) _root_.Prod.fst) ≫
            e.ringUnderlying.hom).hom.app U p)
          ((L.map (constantMap JC A (A × A) _root_.Prod.snd) ≫
            e.ringUnderlying.hom).hom.app U p)) :
    let f := e.ringUnderlying.inv ≫ (constantRingSetComparison JC JD L kappa).hom.app A
    ∀ U x y, f.hom.app U (opI U x y) = opD U (f.hom.app U x) (f.hom.app U y) := by
  let k := (constantRingSetComparison JC JD L kappa).hom.app A
  let f := e.ringUnderlying.inv ≫ k
  have hcancel : e.ringUnderlying.hom ≫ f = k := by
    simp only [f, Iso.hom_inv_id_assoc]
  have hn (g : A × A → A) U p :
      f.hom.app U ((L.map (constantMap JC A (A × A) g) ≫
        e.ringUnderlying.hom).hom.app U p) =
      (constantMap JD A (A × A) g).hom.app U (kappa.hom.app (A × A) |>.hom.app U p) := by
    have h := constantMap_comparison JC JD L kappa A (A × A) g
    change L.map (constantMap JC A (A × A) g) ≫ k = _ at h
    rw [← hcancel] at h
    exact congrArg (fun h ↦ h.hom.app U p) h
  change ∀ U x y, f.hom.app U (opI U x y) = opD U (f.hom.app U x) (f.hom.app U y)
  intro U x y
  obtain ⟨p, hx, hy⟩ := lift_constant_pair JC JD L A RI e U x y
  rw [← hx, ← hy, ← hI U p, hn op U p, hD,
    ← hn _root_.Prod.fst U p, ← hn _root_.Prod.snd U p]

/-- The underlying comparison with a single constant ring preserves its four operations.

Source: Stacks Project, Sites, Tag 00YV (rings as algebraic objects), and Tag 0H7J
(constant sheaves); original constant-comparison node, proof step 3.
(auxiliary; not a blueprint node).

Proof: write the underlying sheaf of the constant ring as the constant set sheaf,
using `constantCommuteCompose`. The constant sheaf of `A × A` maps isomorphically
to the product of two copies of the constant sheaf of `A`, because set sheafification
preserves finite products. Its projections are the constant maps of the two
projections. Addition and multiplication composed with this isomorphism are the
constant maps of addition and multiplication: check this after precomposing with
the sheafification unit, where it is the ring-homomorphism property of that unit.
Naturality of `kappa` for the two projections and the two operations therefore
shows that the comparison transports addition and multiplication. Apply the
`ringAdd` and `ringMul` graph equations of `e` to this pair object. The pair
comparison and its image under `L` are isomorphisms (use finite-limit preservation),
so this checks every pair of target sections. For zero and one use the constant
singleton sheaf and the constant maps selecting zero and one. Naturality of
`kappa`, terminality, and `ringZero`/`ringOne` give the two nullary identities.
Finally conjugate these identities by `e.ringUnderlying`, which is invertible,
to obtain the displayed identities for its inverse followed by the comparison.
This argument works for the zero ring and for sites with empty covering sieves;
it never assumes injectivity of a sheafification unit or a final object of a site.
-/
theorem constantComparison_ring_operations
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (hL : PreservesFiniteLimits L)
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u))
    (A : CommRingCat.{u}) (RI : Sheaf JD CommRingCat.{u})
    (e : RingInverseImage L ((constantSheaf JC CommRingCat.{u}).obj A) RI) :
    let f : ∀ U : Dᵒᵖ, RI.obj.obj U → ((constantSheaf JD CommRingCat.{u}).obj A).obj.obj U :=
      fun U x ↦ (e.ringUnderlying.inv ≫
        (constantRingSetComparison JC JD L kappa).hom.app A).hom.app U x
    ∀ U : Dᵒᵖ,
      f U 0 = 0 ∧ f U 1 = 1 ∧
      (∀ x y : RI.obj.obj U, f U (x + y) = f U x + f U y) ∧
      (∀ x y : RI.obj.obj U, f U (x * y) = f U x * f U y) := by
  dsimp only
  let : PreservesFiniteLimits L := hL
  let R := (constantSheaf JC CommRingCat.{u}).obj A
  let S := (constantSheaf JD CommRingCat.{u}).obj A
  let f := e.ringUnderlying.inv ≫ (constantRingSetComparison JC JD L kappa).hom.app A
  have addC U p : (constantMap JC A (A × A) (fun p ↦ p.1 + p.2)).hom.app U p =
      @id (R.obj.obj U) ((constantMap JC A (A × A) _root_.Prod.fst).hom.app U p) +
      @id (R.obj.obj U) ((constantMap JC A (A × A) _root_.Prod.snd).hom.app U p) :=
    congrArg (fun h ↦ h.hom.app U p)
      (constantMap_add JC A (A × A) _root_.Prod.fst _root_.Prod.snd)
  have addD U p : (constantMap JD A (A × A) (fun p ↦ p.1 + p.2)).hom.app U p =
      @id (S.obj.obj U) ((constantMap JD A (A × A) _root_.Prod.fst).hom.app U p) +
      @id (S.obj.obj U) ((constantMap JD A (A × A) _root_.Prod.snd).hom.app U p) :=
    congrArg (fun h ↦ h.hom.app U p)
      (constantMap_add JD A (A × A) _root_.Prod.fst _root_.Prod.snd)
  have mulC U p : (constantMap JC A (A × A) (fun p ↦ p.1 * p.2)).hom.app U p =
      @id (R.obj.obj U) ((constantMap JC A (A × A) _root_.Prod.fst).hom.app U p) *
      @id (R.obj.obj U) ((constantMap JC A (A × A) _root_.Prod.snd).hom.app U p) :=
    congrArg (fun h ↦ h.hom.app U p)
      (constantMap_mul JC A (A × A) _root_.Prod.fst _root_.Prod.snd)
  have mulD U p : (constantMap JD A (A × A) (fun p ↦ p.1 * p.2)).hom.app U p =
      @id (S.obj.obj U) ((constantMap JD A (A × A) _root_.Prod.fst).hom.app U p) *
      @id (S.obj.obj U) ((constantMap JD A (A × A) _root_.Prod.snd).hom.app U p) :=
    congrArg (fun h ↦ h.hom.app U p)
      (constantMap_mul JD A (A × A) _root_.Prod.fst _root_.Prod.snd)
  have hAdd : ∀ U (x y : RI.obj.obj U), f.hom.app U (x + y) =
      @id (S.obj.obj U) (f.hom.app U x) + @id (S.obj.obj U) (f.hom.app U y) :=
    comparison_binary JC JD L kappa A RI e (fun p ↦ p.1 + p.2)
      (fun _ x y ↦ x + y) (fun _ x y ↦ x + y) addD
      (e.ringAdd _ _ _ _ addC)
  have hMul : ∀ U (x y : RI.obj.obj U), f.hom.app U (x * y) =
      @id (S.obj.obj U) (f.hom.app U x) * @id (S.obj.obj U) (f.hom.app U y) :=
    comparison_binary JC JD L kappa A RI e (fun p ↦ p.1 * p.2)
      (fun _ x y ↦ x * y) (fun _ x y ↦ x * y) mulD
      (e.ringMul _ _ _ _ mulC)
  have hZero (U : Dᵒᵖ) : f.hom.app U (0 : RI.obj.obj U) = (0 : S.obj.obj U) := by
    have h := hAdd U 0 0
    apply (@add_eq_left (S.obj.obj U) inferInstance inferInstance _ _).mp
    simpa only [zero_add, id_eq] using h.symm
  let z : ringSets R ⟶ ringSets R :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : R.obj.obj U))
       naturality := by
         intro U V g
         ext x
         exact (R.obj.map g).hom.map_one.symm }⟩
  have hOne (U : Dᵒᵖ) : f.hom.app U (1 : RI.obj.obj U) = (1 : S.obj.obj U) := by
    let p := e.ringUnderlying.inv.hom.app U (1 : RI.obj.obj U)
    have hi := e.ringOne (ringSets R) z (fun _ _ ↦ rfl) U p
    have hs : ∀ (V : Cᵒᵖ) (x : (ringSets R).obj.obj V),
        @id (R.obj.obj V) (z.hom.app V x) =
          (toSheafify JC ((Functor.const Cᵒᵖ).obj A)).app V (1 : A) := by
      intro V x
      exact ((toSheafify JC ((Functor.const Cᵒᵖ).obj A)).app V).hom.map_one.symm
    have hk := canonicalConstantSectionComparison JC JD L kappa A 1 (ringSets R) z hs U p
    have hp : (L.map z).hom.app U p = p := by
      apply (ConcreteCategory.bijective_of_isIso (e.ringUnderlying.hom.hom.app U)).injective
      exact hi.trans
        (congrArg (fun h ↦ h.hom.app U (1 : RI.obj.obj U))
          e.ringUnderlying.inv_hom_id).symm
    change ((constantRingSetComparison JC JD L kappa).hom.app A).hom.app U p = _
    rw [hp] at hk
    exact hk.trans (((toSheafify JD ((Functor.const Dᵒᵖ).obj A)).app U).hom.map_one)
  intro U
  exact ⟨hZero U, hOne U, hAdd U, hMul U⟩

end CategoryTheory
