/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Pasting a derived base-change square with an upper-left morphism

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-derived-base-change-pasting).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem homEquiv_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (M : C) (N : D) (b : L₁.obj M ⟶ N) :
    a₁.homEquiv M N b ≫ (conjugateEquiv a₁ a₂ α).app N =
      a₂.homEquiv M N (α.app M ≫ b) := by
  rw [Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv a₁ a₂ α).naturality b, ← Category.assoc,
    unit_conjugateEquiv, Category.assoc, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit]

-- Keep the chosen derived comparison families folded during mate rewriting.
/-- The mate pasting law before cancellation of the upper-left adjunction unit.
It applies to any morphism `t`, without an invertibility or cartesian assumption.
Source: Stacks Project, Remark 20.28.3 (Tag 08HY), and Lemma 20.27.2 (Tag 0D5S).
(blueprint: lem-pc-derived-base-change-pasting).

Proof: Transpose both sides under the composite adjunction `a q` followed by `a t`.
By definition, the conjugate comparison `k` changes transposition under `a (t ≫ q)`
into transposition under this composite, using the pullback comparison `c t q`.
The transpose of the right side is obtained by applying `derivedPullback t` to
that under `a q`: the inserted unit of `a t` cancels by the triangle identity.
Substitute the counit formula defining both base-change maps. Naturality moves
`c t p` past the counit of `a f`. The associativity laws for `c`, first for `t, q, g`
and then for `t, p, f`, identify the two composites into the pullback of `t ≫ p ≫ f`.
The commutativity proof `h` identifies the middle morphisms; proof irrelevance
identifies the resulting equality transports. Thus the transposes coincide, and
injectivity of the composite adjunction Hom equivalence gives the displayed law.
For identity `t` it reduces to the unit law; zero objects and empty schemes need
no exclusion, because the proof consists of natural transformation identities. -/
theorem schemeDerivedBaseChange_pasting
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S P S' T : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (p : P ⟶ X) (q : P ⟶ S') (h : p ≫ f = q ≫ g) (t : T ⟶ P) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    let k := conjugateIsoEquiv (a (t ≫ q)) ((a q).comp (a t)) (c t q)
    ∀ E : schemeDerivedCategory X,
      schemeDerivedBaseChangeMap f (t ≫ q) g (t ≫ p)
          (by rw [Category.assoc, h, Category.assoc]) E ≫
        k.hom.app ((derivedPullback (t ≫ p)).obj E) ≫
        (schemeDerivedDirectImage q).map
          ((schemeDerivedDirectImage t).map ((c t p).inv.app E)) =
      schemeDerivedBaseChangeMap f q g p h E ≫
        (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E)) := by
  classical
  intro c a k E
  let b : (derivedPullback q).obj
      ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ⟶
      (derivedPullback p).obj E := (c q g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
    eqToHom (congrArg (fun s ↦
      (derivedPullback s).obj ((schemeDerivedDirectImage f).obj E)) h.symm) ≫
    (c p f).inv.app ((schemeDerivedDirectImage f).obj E) ≫
    (derivedPullback p).map ((a f).counit.app E)
  let ht : (t ≫ p) ≫ f = (t ≫ q) ≫ g := by
    rw [Category.assoc, h, Category.assoc]
  let bt : (derivedPullback (t ≫ q)).obj
      ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ⟶
      (derivedPullback (t ≫ p)).obj E :=
    (c (t ≫ q) g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
    eqToHom (congrArg (fun s ↦
      (derivedPullback s).obj ((schemeDerivedDirectImage f).obj E)) ht.symm) ≫
    (c (t ≫ p) f).inv.app ((schemeDerivedDirectImage f).obj E) ≫
    (derivedPullback (t ≫ p)).map ((a f).counit.app E)
  change (a (t ≫ q)).homEquiv _ _ bt ≫
    (conjugateEquiv (a (t ≫ q)) ((a q).comp (a t)) (c t q).hom).app _ ≫
    (schemeDerivedDirectImage q).map
      ((schemeDerivedDirectImage t).map ((c t p).inv.app E)) =
    (a q).homEquiv _ _ b ≫
      (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E))
  rw [← Category.assoc, homEquiv_conjugate]
  rw [Adjunction.comp_homEquiv]
  change (a q).homEquiv _ _ ((a t).homEquiv _ _
      ((c t q).hom.app ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≫
        bt)) ≫
      (schemeDerivedDirectImage q).map
        ((schemeDerivedDirectImage t).map ((c t p).inv.app E)) = _
  rw [← (a q).homEquiv_naturality_right, ← (a q).homEquiv_naturality_right]
  apply congrArg ((a q).homEquiv
    ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E))
    ((schemeDerivedDirectImage t).obj ((derivedPullback t).obj
      ((derivedPullback p).obj E))))
  rw [← (a t).homEquiv_naturality_right]
  have unitb : b ≫ (a t).unit.app ((derivedPullback p).obj E) =
      (a t).homEquiv _ _ ((derivedPullback t).map b) := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      ((a t).homEquiv_naturality_left b (𝟙 _)).symm
  rw [unitb]
  apply congrArg ((a t).homEquiv
    ((derivedPullback q).obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)))
    ((derivedPullback t).obj ((derivedPullback p).obj E)))
  have assoc := fun {A B C D : Scheme.{u}}
      (r : A ⟶ B) (s : B ⟶ C) (v : C ⟶ D) ↦
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 r s v
  let M := (schemeDerivedDirectImage f).obj E
  have hg := congrArg (fun z ↦ z.hom.app M) (assoc t q g)
  have hf := congrArg (fun z ↦ z.hom.app M) (assoc t p f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app,
    Functor.comp_obj, Category.id_comp] at hg hf
  change (derivedPullback t).map ((c q g).hom.app M) ≫
      (c t (q ≫ g)).hom.app M =
    (c t q).hom.app ((derivedPullback g).obj M) ≫ (c (t ≫ q) g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) (Category.assoc t q g)) at hg
  change (derivedPullback t).map ((c p f).hom.app M) ≫
      (c t (p ≫ f)).hom.app M =
    (c t p).hom.app ((derivedPullback f).obj M) ≫ (c (t ≫ p) f).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) (Category.assoc t p f)) at hf
  have mid : (c t (q ≫ g)).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (t ≫ s)).obj M) h.symm) =
      (derivedPullback t).map
        (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) h.symm)) ≫
        (c t (p ≫ f)).hom.app M := by
    simpa only [Iso.app_hom, eqToHom_map] using
      eqToHom_iso_hom_naturality (fun s : P ⟶ S ↦ (c t s).app M) h.symm
  have compare :
      (c t q).hom.app ((derivedPullback g).obj M) ≫ (c (t ≫ q) g).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) ht.symm) ≫
        (c (t ≫ p) f).inv.app M ≫ (c t p).inv.app ((derivedPullback f).obj M) =
      (derivedPullback t).map ((c q g).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) h.symm) ≫
        (c p f).inv.app M) := by
    apply (cancel_mono ((derivedPullback t).map ((c p f).hom.app M) ≫
      (c t (p ≫ f)).hom.app M)).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (derivedPullback t)
      ((c p f).inv.app M) ((c p f).hom.app M),
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp]
    rw [hf]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← mid]
    simpa only [Category.assoc, eqToHom_trans] using
      congrArg (fun z ↦ z ≫ eqToHom (congrArg
        (fun s ↦ (derivedPullback (t ≫ s)).obj M) h.symm)) hg.symm
  dsimp only [b, bt]
  simp only [Category.assoc, Functor.map_comp]
  erw [(c t p).inv.naturality ((a f).counit.app E)]
  simp only [Functor.comp_map]
  simpa only [M, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ z ≫ (derivedPullback t).map
      ((derivedPullback p).map ((a f).counit.app E))) compare


end AlgebraicGeometry
