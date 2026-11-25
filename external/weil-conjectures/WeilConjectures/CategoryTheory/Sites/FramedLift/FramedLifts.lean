/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection

/-!
# Lifting torsors with a prescribed section

Source: Stacks Project, Tag 03AJ, relative refinement: the lifting-torsor construction
with its chosen lift over an object of the site.
(blueprint: lem-amb-framed-lifts-classification).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {G E Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ E} {d : E ⟶ Q} {w₀ : ι ≫ d = 0}
  {T : C} (hT : IsTerminal T) (hS : (ShortComplex.mk ι d w₀).ShortExact) (U : C)

/-- A global quotient section together with its lift over U.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift :=
  (s : Q.obj.obj (op T)) × (lifts hT hS s).sheaf.obj.obj (op U)

/-- The lifting torsor with its specified local lift.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.toPair (z : FramedLift hT hS U) : WithSection G U :=
  ⟨lifts hT hS z.1, z.2⟩

/-- Every pointed torsor has a pointed lifting presentation when E is injective.
Source: Stacks Project, Tag 03AJ, relative refinement, step 5.
(blueprint: lem-amb-framed-lifts-classification).
Proof: present the underlying torsor as a lifting torsor using injectivity, and transport
its specified section along that isomorphism. -/
theorem FramedLift.surjective [Injective E] :
    Function.Surjective (fun z : FramedLift hT hS U ↦
      (_root_.Quotient.mk _ z.toPair : WithSection.Classes G U)) := by
  intro p
  induction p using _root_.Quotient.inductionOn with
  | h p =>
    obtain ⟨s, ⟨e⟩⟩ := exists_equiv_lifts hT hS p.1
    refine ⟨⟨s, e.iso.hom.hom.app (op U) p.2⟩, _root_.Quotient.sound ?_⟩
    exact ⟨e.symm, by
      change e.iso.inv.hom.app (op U) (e.iso.hom.hom.app (op U) p.2) = p.2
      exact congrArg (fun f ↦ f.hom.app (op U) p.2) e.iso.hom_inv_id⟩

/-- An isomorphism of pointed lifting torsors is translation by a global section of E.
Source: Stacks Project, Tag 03AJ, relative refinement, step 4.
(blueprint: lem-amb-framed-lifts-classification).
Proof: the difference between an equivariant isomorphism and the inclusion into E is
invariant under G, hence glues to a global section x of E. Applying d computes its image
as the difference of the quotient sections; evaluating on the specified lift gives the
second equality. Conversely translate every local lift by the restriction of x. -/
theorem FramedLift.isIsomorphic_iff (z z' : FramedLift hT hS U) :
    WithSection.IsIsomorphic z.toPair z'.toPair ↔
      ∃ x : E.obj.obj (op T),
        d.hom.app (op T) x = z'.1 - z.1 ∧
        E.obj.map (hT.from U).op x = z'.2.1 - z.2.1 := by
  constructor
  · rintro ⟨e, he⟩
    dsimp only [FramedLift.toPair] at e he
    have hn {A B : Cᵒᵖ} (f : A ⟶ B)
        (y : (lifts hT hS z.1).sheaf.obj.obj A) :
        (e.iso.hom.hom.app B ((lifts hT hS z.1).sheaf.obj.map f y)).1 =
          E.obj.map f (e.iso.hom.hom.app A y).1 := by
      rw [← ConcreteCategory.comp_apply, e.iso.hom.hom.naturality]
      rfl
    obtain ⟨x, hx⟩ := exists_section_of_invariant (lifts hT hS z.1)
      ((sheafCompose J (forget _)).obj E) hT
      (fun A y ↦ (show E.obj.obj A from (e.iso.hom.hom.app A y).1) -
        (show E.obj.obj A from y.1))
      (fun A B f y ↦ by
        change E.obj.map f (_ - _) = _
        rw [map_sub, hn]
        rfl)
      (fun A g y ↦ by
        rw [e.map_vadd]
        change (show E.obj.obj A from (e.iso.hom.hom.app A y).1) + ι.hom.app A g -
          ((show E.obj.obj A from y.1) + ι.hom.app A g) = _
        abel)
    refine ⟨x, ?_, ?_⟩
    · apply ext_of_nonempty (lifts hT hS z.1) ((sheafCompose J (forget _)).obj Q)
      intro A f hy
      obtain ⟨y⟩ := hy
      have hf : f = hT.from A := hT.hom_ext _ _
      subst hf
      change Q.obj.map _ (d.hom.app (op T) x) = Q.obj.map _ (z'.1 - z.1)
      erw [← ConcreteCategory.comp_apply, ← d.hom.naturality, ConcreteCategory.comp_apply]
      change d.hom.app (op A) (E.obj.map _ x) = _
      have hxy := hx (op A) y
      change (show E.obj.obj (op A) from (e.iso.hom.hom.app (op A) y).1) -
        (show E.obj.obj (op A) from y.1) =
        E.obj.map (hT.from A).op x at hxy
      rw [← hxy, map_sub, map_sub, lifts_val, lifts_val]
    · have hh := hx (op U) z.2
      change (show E.obj.obj (op U) from (e.iso.hom.hom.app (op U) z.2).1) -
        (show E.obj.obj (op U) from z.2.1) =
        E.obj.map (hT.from U).op x at hh
      rw [he] at hh
      exact hh.symm
  · rintro ⟨x, hx, hU⟩
    let f : (lifts hT hS z.1).sheaf ⟶ (lifts hT hS z'.1).sheaf :=
      ObjectProperty.homMk
        { app A := TypeCat.ofHom fun y ↦
            ⟨(show E.obj.obj A from y.1) + E.obj.map (hT.from A.unop).op x, by
              change d.hom.app A (_ + _) = Q.obj.map _ z'.1
              rw [map_add, lifts_val, ← ConcreteCategory.comp_apply, d.hom.naturality,
                ConcreteCategory.comp_apply, hx, ← map_add, add_sub_cancel]⟩
          naturality A B f := by
            ext y
            apply Subtype.ext
            change E.obj.map f y.1 + E.obj.map (hT.from B.unop).op x =
              E.obj.map f ((show E.obj.obj A from y.1) +
                E.obj.map (hT.from A.unop).op x)
            rw [map_add, ← ConcreteCategory.comp_apply, ← E.obj.map_comp]
            have hh : (hT.from B.unop).op = (hT.from A.unop).op ≫ f := by
              exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
            rw [hh] }
    refine ⟨Iso.ofHom f (fun A g y ↦ ?_), ?_⟩
    · apply Subtype.ext
      change (show E.obj.obj A from y.1) + ι.hom.app A g + _ =
        (show E.obj.obj A from y.1) + _ + ι.hom.app A g
      abel
    · apply Subtype.ext
      change (show E.obj.obj (op U) from z.2.1) + E.obj.map (hT.from U).op x = z'.2.1
      rw [hU, add_sub_cancel]

/-- The zero quotient section with its zero lift.
Source: Stacks Project, Tag 03AJ, relative refinement, step 6.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.zero : FramedLift hT hS U :=
  ⟨0, ⟨0, by change d.hom.app (op U) 0 = Q.obj.map _ 0; simp⟩⟩

/-- Zero lifts give the trivial torsor with its zero section.
Source: Stacks Project, Tag 03AJ, relative refinement, step 6.
(blueprint: lem-amb-framed-lifts-classification).
Proof: send g to its image under the inclusion G into E. Exactness makes this an
isomorphism onto the lifts of zero, and it carries zero to zero. -/
theorem FramedLift.zero_isIsomorphic :
    WithSection.IsIsomorphic
      (⟨trivial G, @id (G.obj.obj (op U)) 0⟩ : WithSection G U)
      (FramedLift.zero hT hS U).toPair := by
  let f : (trivial G).sheaf ⟶ (lifts hT hS 0).sheaf :=
    ObjectProperty.homMk
      { app A := TypeCat.ofHom fun g ↦ ⟨ι.hom.app A g, by
          change d.hom.app A (ι.hom.app A g) = Q.obj.map _ 0
          rw [hom_app_hom_app_of_comp_eq_zero w₀, map_zero]⟩
        naturality A B f := by
          ext g
          apply Subtype.ext
          change ι.hom.app B (G.obj.map f g) = E.obj.map f (ι.hom.app A g)
          exact congrArg (fun f ↦ f g) (ι.hom.naturality f) }
  refine ⟨Iso.ofHom f (fun A g x ↦ ?_), ?_⟩
  · apply Subtype.ext
    change ι.hom.app A (g + (show G.obj.obj A from x)) =
      ι.hom.app A x + ι.hom.app A g
    rw [map_add, add_comm]
  · apply Subtype.ext
    exact (ι.hom.app (op U)).hom.map_zero

/-- Classes of framed lifts, identifying precisely global translations.
Source: Stacks Project, Tag 03AJ, relative refinement, steps 3 and 4.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.setoid : Setoid (FramedLift hT hS U) :=
  Setoid.comap (FramedLift.toPair hT hS U) (WithSection.setoid G U)

/-- Framed lifting presentations modulo global translation.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.Classes := _root_.Quotient (FramedLift.setoid hT hS U)

/-- The canonical identification of framed lifting classes with pointed torsor classes.
Source: Stacks Project, Tag 03AJ, relative refinement, steps 3 through 5.
(blueprint: lem-amb-framed-lifts-classification). -/
noncomputable def FramedLift.classEquiv [Injective E] :
    FramedLift.Classes hT hS U ≃ WithSection.Classes G U :=
  Equiv.ofBijective
    (_root_.Quotient.map (FramedLift.toPair hT hS U) (fun _ _ h ↦ h)) (by
      constructor
      · intro a b h
        induction a using _root_.Quotient.inductionOn with | h a =>
          induction b using _root_.Quotient.inductionOn with | h b =>
            exact _root_.Quotient.sound (show
              WithSection.IsIsomorphic a.toPair b.toPair from _root_.Quotient.exact h)
      · intro p
        obtain ⟨z, hz⟩ := FramedLift.surjective hT hS U p
        exact ⟨_root_.Quotient.mk _ z, hz⟩)

/-- The inclusion of a lifting torsor into its ambient abelian sheaf.
Source: Stacks Project, Tag 03AJ, lifting-torsor construction.
(blueprint: lem-amb-framed-lifts-classification). -/
def liftsEmbedding (s : Q.obj.obj (op T)) :
    (lifts hT hS s).sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{w} where
  app _A := TypeCat.ofHom (fun y => y.1)
  naturality _ _ _ := rfl

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Two equivariant lifting maps differ by one global section.
Source: Stacks Project, Tag 03AJ, relative refinement, steps 4 and 8.
(blueprint: lem-amb-framed-lifts-classification).
Proof: their difference is invariant under the torsor action and natural in the site
object, hence glues to a global section. Compute its image under d after restriction
to any object carrying a torsor section; these objects cover the terminal object. -/
theorem difference_of_equivariant_lifts (P : Torsor G)
    (F H : Sheaf J AddCommGrpCat.{w}) (δ : F ⟶ H) (φ : G ⟶ F)
    (μ ν : P.sheaf.obj ⟶ F.obj ⋙ forget AddCommGrpCat.{w})
    (hμ : ∀ A g t, μ.app A (P.vadd A g t) = (show F.obj.obj A from μ.app A t) + φ.hom.app A g)
    (hν : ∀ A g t, ν.app A (P.vadd A g t) = (show F.obj.obj A from ν.app A t) + φ.hom.app A g)
    (s t : H.obj.obj (op T))
    (hs : ∀ A x, δ.hom.app A (μ.app A x) = H.obj.map (hT.from A.unop).op s)
    (ht : ∀ A x, δ.hom.app A (ν.app A x) = H.obj.map (hT.from A.unop).op t) :
    ∃ x : F.obj.obj (op T), δ.hom.app (op T) x = t - s ∧
      ∀ A y, F.obj.map (hT.from A.unop).op x = ν.app A y - μ.app A y := by
  obtain ⟨x, hx⟩ := exists_section_of_invariant P
    ((sheafCompose J (forget _)).obj F) hT
    (fun A y => (show F.obj.obj A from ν.app A y) -
      (show F.obj.obj A from μ.app A y))
    (fun A B f y => by
      change F.obj.map f (_ - _) = _
      rw [map_sub]
      have hνn := ConcreteCategory.congr_hom (ν.naturality f) y
      have hμn := ConcreteCategory.congr_hom (μ.naturality f) y
      exact congrArg₂ (fun a b : F.obj.obj B => a - b) hνn.symm hμn.symm)
    (fun A g y => by
      rw [hν, hμ]
      change ((show F.obj.obj A from ν.app A y) + φ.hom.app A g) -
          ((show F.obj.obj A from μ.app A y) + φ.hom.app A g) =
        (show F.obj.obj A from ν.app A y) - (show F.obj.obj A from μ.app A y)
      exact add_sub_add_right_eq_sub _ _ _)
  refine ⟨x, ?_, fun A y => (hx A y).symm⟩
  apply ext_of_nonempty P ((sheafCompose J (forget _)).obj H)
  intro A f hy
  obtain ⟨y⟩ := hy
  have hf : f = hT.from A := hT.hom_ext _ _
  subst hf
  change H.obj.map _ (δ.hom.app (op T) x) = H.obj.map _ (t - s)
  erw [← ConcreteCategory.comp_apply, ← δ.hom.naturality, ConcreteCategory.comp_apply]
  change δ.hom.app (op A) (F.obj.map _ x) = _
  have hh := hx (op A) y
  change ν.app (op A) y - μ.app (op A) y = F.obj.map (hT.from A).op x at hh
  rw [← hh, map_sub, ht, hs, map_sub]

end CategoryTheory.Sheaf.Torsor

-- Check the axioms of the completed construction.
