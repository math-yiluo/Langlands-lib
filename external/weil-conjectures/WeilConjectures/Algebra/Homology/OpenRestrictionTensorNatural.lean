/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.OpenRestrictionSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Natural tensor comparison on an open localized site

Source: Stacks Project, Tags 01CD and 03DH.
(blueprint: lem-pc-open-localized-tensor-natural).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SheafOfModules

private theorem compose_four_squares {D : Type*} [Category* D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (f₃ : A₃ ⟶ B₃) (f₄ : A₄ ⟶ B₄)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) (h₃ : f₃ ≫ b₃ = a₃ ≫ f₄) :
    f₀ ≫ (b₀ ≫ b₁ ≫ b₂ ≫ b₃) = (a₀ ≫ a₁ ≫ a₂ ≫ a₃) ≫ f₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem inverse_square {D : Type*} [Category* D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

private noncomputable def presheafRestrictionTensorIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).obj (M ⊗ N) ≅
      (PresheafOfModules.pushforward₀OfCommRingCat F R).obj M ⊗
        (PresheafOfModules.pushforward₀OfCommRingCat F R).obj N :=
  (Functor.Monoidal.μIso (PresheafOfModules.pushforward₀OfCommRingCat F R) M N).symm

private theorem presheafRestrictionTensorIso_natural
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    {M M' N N' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).map (f ⊗ₘ g) ≫
        (presheafRestrictionTensorIso F R M' N').hom =
      (presheafRestrictionTensorIso F R M N).hom ≫
        ((PresheafOfModules.pushforward₀OfCommRingCat F R).map f ⊗ₘ
          (PresheafOfModules.pushforward₀OfCommRingCat F R).map g) :=
  (Functor.OplaxMonoidal.δ_natural _ f g).symm

private theorem tensorObjIsoSheafification_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification (R := R) M' N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  rw [tensorHom_def, Category.assoc, whiskerLeft_tensorObjIsoSheafification_hom,
    ← Category.assoc, whiskerRight_tensorObjIsoSheafification_hom,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

private noncomputable def restrictionUnderlyingIso
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : TopologicalSpace.Opens X) (M : SheafOfModules.{u} A) :
    (PresheafOfModules.pushforward₀.{u} (Over.forget U) A.obj).obj M.val ≅
      ((overFunctor.{u} A U).obj M).val :=
  PresheafOfModules.isoMk (fun W ↦
    (ModuleCat.restrictScalarsId'App
      (RingHom.id (A.obj.obj ((Over.forget U).op.obj W)))
      (by rfl) (M.val.obj ((Over.forget U).op.obj W))).symm)
    (by intros; ext x; rfl)

private theorem restrictionUnderlyingIso_natural
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : TopologicalSpace.Opens X) {M N : SheafOfModules.{u} A} (f : M ⟶ N) :
    (PresheafOfModules.pushforward₀.{u} (Over.forget U) A.obj).map f.val ≫
        (restrictionUnderlyingIso A U N).hom =
      (restrictionUnderlyingIso A U M).hom ≫ ((overFunctor.{u} A U).map f).val := by
  ext W x
  rfl

private theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {M N M' N' P Q P' Q' : D} (f : M ⟶ M') (g : N ⟶ N')
    (f' : P ⟶ P') (g' : Q ⟶ Q')
    (a : M ≅ P) (b : N ≅ Q) (a' : M' ≅ P') (b' : N' ≅ Q')
    (ha : f ≫ a'.hom = a.hom ≫ f') (hb : g ≫ b'.hom = b.hom ≫ g') :
    (f ⊗ₘ g) ≫ (a' ⊗ᵢ b').hom = (a ⊗ᵢ b).hom ≫ (f' ⊗ₘ g') := by
  simp only [tensorIso_hom, tensorHom_comp_tensorHom, ha, hb]

/-- Tensor product commutes naturally with restriction to the localized open site.
Source: Stacks Project, Tag 01CD (`modules-lemma-tensor-product-pullback`) and Tag 03DH.

Proof: before sheafification both sides have sections M(V) tensor_(R(V)) N(V) at
an object V -> U. Their restrictions are the tensor of the two module restrictions.
A covering sieve on V in the slice consists of exactly a covering sieve on V with
its forced maps to U. Thus sheafification commutes with this restriction: the local
representatives, local equality relation and gluing maps defining sheafification
are identical on both sites. Sheafifying the identity of presheaf tensors produces
the comparison and its inverse. The two composites are identities by the universal
property of sheafification. A pair of module maps acts by f tensor g before
sheafification, so these identities commute with both module maps after sheafification.
This proves the displayed naturality square. The empty open, zero modules and zero
coefficient rings use the same construction without any nonzero assumption.
(blueprint: lem-pc-open-localized-tensor-natural). -/
theorem exists_open_localized_tensor_natural
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X) :
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let V := overFunctor.{u} A U
    letI := monoidalCategory R
    letI : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
      monoidalCategory (R.over U)
    ∃ e : ∀ (M N : SheafOfModules.{u} A), V.obj (M ⊗ N) ≅ V.obj M ⊗ V.obj N,
      ∀ (M M' N N' : SheafOfModules.{u} A) (f : M ⟶ M') (g : N ⟶ N'),
        V.map (f ⊗ₘ g) ≫ (e M' N').hom = (e M N).hom ≫ (V.map f ⊗ₘ V.map g) :=
  by
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)
  let V : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B := overFunctor.{u} A U
  let P : PresheafOfModules.{u} A.obj ⥤ PresheafOfModules.{u} B.obj :=
    PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) R.obj
  let S := PresheafOfModules.sheafification.{u} (R := A) (𝟙 A.obj)
  let T := PresheafOfModules.sheafification.{u} (R := B) (𝟙 B.obj)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  obtain ⟨i₀⟩ := exists_open_localized_sheafification A U
  let i : S ⋙ V ≅ P ⋙ T := i₀
  let j (M : SheafOfModules.{u} A) : P.obj M.val ≅ (V.obj M).val :=
    restrictionUnderlyingIso A U M
  let e (M N : SheafOfModules.{u} A) :=
    V.mapIso (tensorObjIsoSheafification (R := R) M N) ≪≫
      i.app (M.val ⊗ N.val) ≪≫
      T.mapIso (presheafRestrictionTensorIso (Over.forget U) R.obj M.val N.val) ≪≫
      T.mapIso (j M ⊗ᵢ j N) ≪≫
      (tensorObjIsoSheafification (R := R.over U) (V.obj M) (V.obj N)).symm
  refine ⟨e, ?_⟩
  intro M M' N N' f g
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  apply compose_four_squares
    (V.map (tensorObjIsoSheafification (R := R) M N).hom)
    (i.hom.app (M.val ⊗ N.val))
    (T.map (presheafRestrictionTensorIso (Over.forget U) R.obj M.val N.val).hom)
    (T.map (j M ⊗ᵢ j N).hom ≫
      (tensorObjIsoSheafification (R := R.over U) (V.obj M) (V.obj N)).inv)
    (V.map (tensorObjIsoSheafification (R := R) M' N').hom)
    (i.hom.app (M'.val ⊗ N'.val))
    (T.map (presheafRestrictionTensorIso (Over.forget U) R.obj M'.val N'.val).hom)
    (T.map (j M' ⊗ᵢ j N').hom ≫
      (tensorObjIsoSheafification (R := R.over U) (V.obj M') (V.obj N')).inv)
    (V.map (f ⊗ₘ g)) (V.map (S.map (f.val ⊗ₘ g.val)))
    (T.map (P.map (f.val ⊗ₘ g.val))) (T.map (P.map f.val ⊗ₘ P.map g.val))
    (V.map f ⊗ₘ V.map g)
  · simpa only [Functor.map_comp] using
      congrArg V.map (tensorObjIsoSheafification_natural R f g)
  · exact i.hom.naturality (f.val ⊗ₘ g.val)
  · simpa only [Functor.map_comp] using congrArg T.map
      (presheafRestrictionTensorIso_natural (Over.forget U) R.obj f.val g.val)
  · have ht := tensor_square (P.map f.val) (P.map g.val)
      (V.map f).val (V.map g).val
      (j M) (j N)
      (j M') (j N')
      (restrictionUnderlyingIso_natural A U f) (restrictionUnderlyingIso_natural A U g)
    have hi := inverse_square
      (tensorObjIsoSheafification (R := R.over U) (V.obj M) (V.obj N))
      (tensorObjIsoSheafification (R := R.over U) (V.obj M') (V.obj N'))
      (V.map f ⊗ₘ V.map g) (T.map ((V.map f).val ⊗ₘ (V.map g).val))
      (tensorObjIsoSheafification_natural (R.over U) (V.map f) (V.map g))
    rw [← T.map_comp_assoc, ht, T.map_comp_assoc, hi, Category.assoc]

end SheafOfModules
