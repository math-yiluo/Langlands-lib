/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits

/-! # The Hom cone of a sequential colimit

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local irreducible] homComplexFunctor homComplexπ homComplexIsLimit
set_option allowUnsafeReducibility true in
attribute [local reducible] homComplex Functor.comp Functor.op Functor.flip
  HomologicalComplex.eval Functor.mapCone Functor.mapCocone

private abbrev homColimitCone {A : Type*} [Category A] [HasZeroMorphisms A]
    (H : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ)
    (F : ℕ ⥤ CochainComplex A ℤ) [HasColimit F] : Cone (F.op ⋙ H) where
  pt := H.obj (op (colimit F))
  π :=
    { app := fun m ↦ H.map (colimit.ι F m.unop).op
      naturality := fun {m k} f ↦ by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp, ← op_comp, colimit.w] }

private def homColimitConeIsLimit {A : Type*} [Category A] [HasZeroMorphisms A]
    (H : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ)
    (F : ℕ ⥤ CochainComplex A ℤ) [HasColimit F]
    (G : ℤ → ℤ → Aᵒᵖ ⥤ A)
    [∀ n p, PreservesLimit (F ⋙ HomologicalComplex.eval A (.up ℤ) p).op (G n p)]
    [∀ p, PreservesColimit F (HomologicalComplex.eval A (.up ℤ) p)]
    (π : ∀ (L : CochainComplex A ℤ) (n p : ℤ),
      (H.obj (op L)).X n ⟶ (G n p).obj (op (L.X p)))
    (hprod : ∀ L n, IsLimit (Fan.mk ((H.obj (op L)).X n) (π L n)))
    (hpre : ∀ {L L' : CochainComplex A ℤ} (f : L' ⟶ L) (n p : ℤ),
      (H.map f.op).f n ≫ π L' n p = π L n p ≫ (G n p).map (f.f p).op) :
    IsLimit (homColimitCone H F) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  let ht (p : ℤ) : IsLimit ((G n p).mapCone
      ((HomologicalComplex.eval A (.up ℤ) p).mapCocone (colimit.cocone F)).op) :=
    isLimitOfPreserves (G n p)
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) p)
        (colimit.isColimit F)).op
  apply IsLimit.ofExistsUnique
  intro s
  let t (p : ℤ) : Cone ((F ⋙ HomologicalComplex.eval A (.up ℤ) p).op ⋙ G n p) :=
    { pt := s.pt
      π :=
        { app := fun m ↦ s.π.app m ≫ π (F.obj m.unop) n p
          naturality := fun {m k} f ↦ by
            change 𝟙 _ ≫ (s.π.app k ≫ _) = (s.π.app m ≫ _) ≫ _
            rw [Category.id_comp, Category.assoc, ← hpre, ← Category.assoc]
            have hs := s.w f
            change s.π.app m ≫ (H.map (F.map f.unop).op).f n = s.π.app k at hs
            rw [hs] } }
  let l := (hprod (colimit F) n).lift
    (Fan.mk s.pt (fun p ↦ (ht p).lift (t p)))
  have hl (p : ℤ) : l ≫ π (colimit F) n p = (ht p).lift (t p) :=
    (hprod (colimit F) n).fac _ ⟨p⟩
  refine ⟨l, ?_, ?_⟩
  · intro m
    apply (hprod (F.obj m.unop) n).hom_ext
    rintro ⟨p⟩
    change (l ≫ (H.map (colimit.ι F m.unop).op).f n) ≫ π (F.obj m.unop) n p = _
    rw [Category.assoc, hpre, ← Category.assoc, hl]
    exact (ht p).fac (t p) m
  · intro g hg
    apply (hprod (colimit F) n).hom_ext
    rintro ⟨p⟩
    change g ≫ π (colimit F) n p = l ≫ π (colimit F) n p
    rw [hl]
    apply (ht p).uniq (t p)
    intro m
    change (g ≫ π (colimit F) n p) ≫ (G n p).map ((colimit.ι F m.unop).f p).op = _
    rw [Category.assoc, ← hpre, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ π (F.obj m.unop) n p) (hg m)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] Functor.comp Functor.op Functor.flip
  HomologicalComplex.eval Functor.mapCone Functor.mapCocone

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- Precomposition with colimit inclusions gives the canonical Hom cone.
Source: Stacks Project, sites-cohomology.tex, Tag 0A0A
(auxiliary; not a blueprint node). -/
abbrev ringedHomComplexColimitCone (F : ℕ ⥤ ringedSiteComplex O) (N : ringedSiteComplex O) :
    Cone (F.op ⋙ (homComplexFunctor.{u, u, u, u} (R := O)).flip.obj N) where
  pt := ((homComplexFunctor.{u, u, u, u} (R := O)).obj (op (colimit F))).obj N
  π :=
    { app := fun m ↦ ((homComplexFunctor.{u, u, u, u} (R := O)).map (colimit.ι F m.unop).op).app N
      naturality := fun {m k} f ↦ by
        dsimp
        rw [Category.id_comp, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
        rw [colimit.w] }

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap

private def sheafHomAdjunction :
    MonoidalCategory.curriedTensor
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⊣₂
        SheafOfModules.homFunctor.{u, u, u, u} O :=
  ParametrizedAdjunction.mk' (SheafOfModules.tensorHomAdjunction O)
    (fun {_ _} f {_ _} g ↦ by
      simp only [SheafOfModules.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
      exact SheafOfModules.tensorHomEquiv_whiskerRight_comp f g)

attribute [local irreducible] sheafHomAdjunction homColimitConeIsLimit

/-- Internal Hom converts any sequential colimit of complexes into a limit.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals (the Hom-of-colimit step);
Section 0A8X (the product Hom complex).
(auxiliary; not a blueprint node).

Proof: evaluation in each source degree preserves the colimit of complexes.
Internal sheaf Hom from that colimit is the inverse limit of internal Homs:
tensor with a test sheaf preserves colimits by the tensor--Hom adjunction,
and maps out of a colimit are compatible families of maps. In Hom degree n,
commute this inverse limit with the product over source degrees p. Both orders
represent exactly the compatible families of maps into Hom(F_m^p,N^(p+n)),
so their canonical cones have the same universal property. These degreewise
universal properties prove that the displayed cone of complexes is limiting,
since evaluation in every degree jointly creates limits. This argument uses
neither finite freeness nor Koszul generators. -/
theorem ringedHomComplexColimitCone_isLimit
    (F : ℕ ⥤ ringedSiteComplex O) (N : ringedSiteComplex O) :
    Nonempty (IsLimit (ringedHomComplexColimitCone O F N)) := by
  let : ∀ n p : ℤ,
      PreservesLimit (F ⋙ HomologicalComplex.eval _ (.up ℤ) p).op
        ((SheafOfModules.homFunctor.{u, u, u, u} O).flip.obj (N.X (p + n))) := fun n p ↦ by
      let : ∀ A : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O),
        PreservesColimitsOfShape (ℕᵒᵖ)ᵒᵖ
          ((MonoidalCategory.curriedTensor _).flip.obj A) := fun A ↦ inferInstance
      let : PreservesLimitsOfShape ℕᵒᵖ
          ((SheafOfModules.homFunctor.{u, u, u, u} O).flip.obj (N.X (p + n))) :=
        (sheafHomAdjunction O).preservesLimitsOfShape_flip_obj ℕᵒᵖ _
      infer_instance
  let : ∀ p : ℤ, PreservesColimit F (HomologicalComplex.eval _ (.up ℤ) p) :=
    fun p ↦ inferInstance
  refine ⟨homColimitConeIsLimit ((homComplexFunctor.{u, u, u, u} (R := O)).flip.obj N) F
    (fun n p ↦ (SheafOfModules.homFunctor.{u, u, u, u} O).flip.obj (N.X (p + n)))
    (fun L n p ↦ homComplexπ.{u, u, u, u} L N n p (p + n) rfl)
    (fun L n ↦ homComplexIsLimit.{u, u, u, u} L N n) ?_⟩
  intro L L' f n p
  change (((homComplexFunctor.{u, u, u, u} (R := O)).map f.op).app N).f n ≫
    homComplexπ.{u, u, u, u} L' N n p (p + n) rfl =
      homComplexπ.{u, u, u, u} L N n p (p + n) rfl ≫
        SheafOfModules.homObjMap.{u, u, u, u} (f.f p) (𝟙 (N.X (p + n)))
  have h := homComplexFunctor_map_f_π.{u, u, u, u} f (𝟙 N) n p (p + n) rfl
  rw [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at h
  exact h

end CategoryTheory
