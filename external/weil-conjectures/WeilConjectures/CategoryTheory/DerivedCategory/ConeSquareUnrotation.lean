/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Unrotating a strict cone square -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open CochainComplex

private def qHomotopyEquivIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : CochainComplex C ℤ} (h : HomotopyEquiv A B) :
    DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B where
  hom := DerivedCategory.Q.map h.hom
  inv := DerivedCategory.Q.map h.inv
  hom_inv_id := by
    rw [← Functor.map_comp, DerivedCategory.Q_map_eq_of_homotopy C h.homotopyHomInvId,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, DerivedCategory.Q_map_eq_of_homotopy C h.homotopyInvHomId,
      CategoryTheory.Functor.map_id]

private def derivedRotateIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g)).rotate ≅
      DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (mappingCone.inr g)) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).symm.app K ≪≫
      qHomotopyEquivIso (mappingCone.rotateHomotopyEquiv g)) ?_ ?_ ?_
  · change DerivedCategory.Q.map (mappingCone.inr g) ≫ 𝟙 _ =
      𝟙 _ ≫ DerivedCategory.Q.map (mappingCone.inr g)
    simp
  · simp only [Iso.refl_hom, Category.id_comp]
    change (DerivedCategory.Q.map (mappingCone.triangle g).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app K ≫
        DerivedCategory.Q.map (mappingCone.rotateHomotopyEquiv g).hom) =
        DerivedCategory.Q.map (mappingCone.inr (mappingCone.inr g))
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    simpa only [← Functor.map_comp] using
      DerivedCategory.Q_map_eq_of_homotopy C (mappingCone.rotateHomotopyEquivComm₂Homotopy g)
  · simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    change -(DerivedCategory.Q.map g)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app K ≫
        DerivedCategory.Q.map (mappingCone.rotateHomotopyEquiv g).hom) ≫
        (DerivedCategory.Q.map (mappingCone.triangle (mappingCone.inr g)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app L)
    rw [Category.assoc, ← Functor.map_comp_assoc, mappingCone.rotateHomotopyEquiv_comm₃,
      Functor.map_neg, Preadditive.neg_comp,
      Functor.commShiftIso_hom_naturality, Preadditive.comp_neg,
      Iso.inv_hom_id_app_assoc]

private def shiftedRotationIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    DerivedCategory.Q.mapTriangle.obj
      (mappingCone.triangle ((mappingCone.inr g)⟦(-1 : ℤ)⟧')) ≅
      (Triangle.shiftFunctor (DerivedCategory C) (-1)).obj
        (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g)).rotate :=
  DerivedCategory.Q.mapTriangle.mapIso
      (mappingCone.shiftTriangleIso (mappingCone.inr g) (-1)).symm ≪≫
    (DerivedCategory.Q.mapTriangleCommShiftIso (-1)).app _ ≪≫
    (Triangle.shiftFunctor (DerivedCategory C) (-1)).mapIso (derivedRotateIso g).symm

private def comparisonIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (T : Triangle (DerivedCategory C))
    (e : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g) ≅ T.rotate.rotate) :
    DerivedCategory.Q.mapTriangle.obj
      (mappingCone.triangle ((mappingCone.inr g)⟦(-1 : ℤ)⟧')) ≅ T :=
  shiftedRotationIso g ≪≫
    (Triangle.shiftFunctor (DerivedCategory C) (-1)).mapIso
      ((rotate (DerivedCategory C)).mapIso e ≪≫
        (rotateRotateRotateIso (DerivedCategory C)).app T) ≪≫
    (shiftFunctorCompIsoId (Triangle (DerivedCategory C)) (1 : ℤ) (-1) (by simp)).app T

@[simp] private lemma triangleUnit_hom₁
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] (T : Triangle D) :
    ((shiftFunctorCompIsoId (Triangle D) (1 : ℤ) (-1) (by simp)).hom.app T).hom₁ =
      (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by simp)).hom.app T.obj₁ := by
  simp [shiftFunctorCompIsoId]

@[simp] private lemma triangleUnit_hom₃
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] (T : Triangle D) :
    ((shiftFunctorCompIsoId (Triangle D) (1 : ℤ) (-1) (by simp)).hom.app T).hom₃ =
      (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by simp)).hom.app T.obj₃ := by
  simp [shiftFunctorCompIsoId]

private lemma comparisonIso_hom₁
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (T : Triangle (DerivedCategory C))
    (e : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g) ≅ T.rotate.rotate) :
    (comparisonIso g T e).hom.hom₁ =
      (DerivedCategory.Q.commShiftIso (-1)).hom.app L ≫
        e.hom.hom₂⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).hom.app T.obj₁ := by
  simp [comparisonIso, shiftedRotationIso, derivedRotateIso,
    mappingCone.shiftTriangleIso, rotateRotateRotateIso]

private lemma shiftConeMap_inv
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f')
    (hc : f⟦(-1 : ℤ)⟧' ≫ b⟦(-1 : ℤ)⟧' = a⟦(-1 : ℤ)⟧' ≫ f'⟦(-1 : ℤ)⟧') :
    mappingCone.map _ _ (a⟦(-1 : ℤ)⟧') (b⟦(-1 : ℤ)⟧') hc ≫
      (mappingCone.shiftIso f' (-1)).inv =
    (mappingCone.shiftIso f (-1)).inv ≫ (mappingCone.map f f' a b h)⟦(-1 : ℤ)⟧' := by
  ext p
  simp [mappingCone.ext_from_iff _ (p + 1) p rfl, mappingCone.shiftIso, mappingCone.map,
    HomComplex.Cochain.shift_v', Category.assoc]

private lemma rotateInverse_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L K' L' : CochainComplex C ℤ}
    (g : K ⟶ L) (g' : K' ⟶ L') (s : K ⟶ K') (r : L ⟶ L')
    (h : g ≫ r = s ≫ g')
    (hc : mappingCone.inr g ≫ mappingCone.map g g' s r h = r ≫ mappingCone.inr g') :
    mappingCone.map _ _ r (mappingCone.map g g' s r h) hc ≫
      (mappingCone.rotateHomotopyEquiv g').inv =
    (mappingCone.rotateHomotopyEquiv g).inv ≫ s⟦(1 : ℤ)⟧' := by
  ext p
  simp [mappingCone.ext_from_iff _ (p + 1) p rfl, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, Category.assoc]

private def coneRetraction
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    DerivedCategory.Q.obj (mappingCone ((mappingCone.inr g)⟦(-1 : ℤ)⟧')) ⟶
      DerivedCategory.Q.obj K :=
  DerivedCategory.Q.map (mappingCone.shiftIso (mappingCone.inr g) (-1)).inv ≫
    (DerivedCategory.Q.commShiftIso (-1)).hom.app (mappingCone (mappingCone.inr g)) ≫
    (DerivedCategory.Q.map (mappingCone.rotateHomotopyEquiv g).inv)⟦(-1 : ℤ)⟧' ≫
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).hom.app _

private lemma comparisonIso_hom₃
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (T : Triangle (DerivedCategory C))
    (e : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g) ≅ T.rotate.rotate) :
    (comparisonIso g T e).hom.hom₃ = coneRetraction g ≫ e.hom.hom₁ := by
  simp [comparisonIso, shiftedRotationIso, derivedRotateIso, qHomotopyEquivIso,
    mappingCone.shiftTriangleIso, rotateRotateRotateIso, coneRetraction,
    Category.assoc, shift_shift_neg']

/-- Double inverse rotation of a strict cone diagram has another strict cone
presentation, naturally on its first and third vertices.

Source: Stacks Project, Derived Categories, Tag 014D (mapping cones and the
canonical double-cone homotopy equivalences), and Tag 05QK (rotation).
(blueprint: lem-pc-derived-cone-square-unrotation).

Proof: Take A = L[-1], B = Cone(g)[-1], t = inr(g)[-1], and the
corresponding primed objects; take the vertical maps r[-1] and Cone(s,r)[-1].
The shifted cone-inclusion naturality square is strictly commutative. The
canonical homotopy equivalence from K[1] to Cone(inr(g)) identifies the rotation
of the cone triangle of g with the cone triangle of inr(g). Shift this
identification by -1 and use the cone-shift comparison to identify the cone
triangle of t with the shifted rotation of the cone triangle of g. The
cone-shift comparison includes the sign on its middle vertex. Compose with the
shifted rotation of e. Three rotations of T identify canonically with T[1];
cancel shifts 1 and -1 to obtain the displayed isomorphism d, and similarly d'.
On first vertices, the comparison is the shift comparison followed by e's
second component and shift cancellation. Shift naturality and coherence give
the first identity. On third vertices, its comparison is the shifted inverse
of the canonical double-cone homotopy equivalence, followed by e's first
component. Cone-shift comparisons are natural in strict squares, as is the
inverse double-cone equivalence: both identities follow degreewise from the
cone matrix formulas. Applying these naturality identities and shift
cancellation gives the second identity. All objects and maps are these explicit
constructions; the argument also applies when any complex is zero. -/
theorem derived_cone_square_unrotation
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L K' L' : CochainComplex C ℤ}
    (g : K ⟶ L) (g' : K' ⟶ L') (s : K ⟶ K') (r : L ⟶ L')
    (hs : g ≫ r = s ≫ g')
    (T T' : Triangle (DerivedCategory C))
    (e : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g) ≅
      T.rotate.rotate)
    (e' : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g') ≅
      T'.rotate.rotate) :
    let t := (CochainComplex.mappingCone.inr g)⟦(-1 : ℤ)⟧'
    let t' := (CochainComplex.mappingCone.inr g')⟦(-1 : ℤ)⟧'
    let α := r⟦(-1 : ℤ)⟧'
    let β := (CochainComplex.mappingCone.map g g' s r hs)⟦(-1 : ℤ)⟧'
    ∀ (hc : t ≫ β = α ≫ t'),
    ∃ (d : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle t) ≅ T)
      (d' : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle t') ≅ T'),
      (DerivedCategory.Q.map α ≫ d'.hom.hom₁)⟦(1 : ℤ)⟧' =
        d.hom.hom₁⟦(1 : ℤ)⟧' ≫ e.inv.hom₂ ≫ DerivedCategory.Q.map r ≫ e'.hom.hom₂ ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ d'.hom.hom₃ =
        d.hom.hom₃ ≫ e.inv.hom₁ ≫ DerivedCategory.Q.map s ≫ e'.hom.hom₁ := by
  dsimp only
  intro hc
  refine ⟨comparisonIso g T e, comparisonIso g' T' e', ?_, ?_⟩
  · rw [comparisonIso_hom₁, comparisonIso_hom₁]
    simp only [Functor.map_comp, Category.assoc,
      Functor.commShiftIso_hom_naturality_assoc,
      shift_shiftFunctorCompIsoId_hom_app, shift_neg_shift',
      Triangle.rotate_obj₂, Triangle.rotate_obj₃,
      Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app]
    simp
  · rw [comparisonIso_hom₃, comparisonIso_hom₃]
    simp only [Category.assoc, Iso.hom_inv_id_triangle_hom₁_assoc]
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (fun k ↦ k ≫ e'.hom.hom₁)
    have hc₀ : mappingCone.inr g ≫ mappingCone.map g g' s r hs =
        r ≫ mappingCone.inr g' := (mappingCone.triangleMap g g' s r hs).comm₂
    have hshift := shiftConeMap_inv (mappingCone.inr g) (mappingCone.inr g') r
      (mappingCone.map g g' s r hs) hc₀ hc
    have hrot := rotateInverse_naturality g g' s r hs hc₀
    dsimp only [coneRetraction]
    rw [← Functor.map_comp_assoc, hshift, Functor.map_comp]
    simp only [Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
    simp only [← Functor.map_comp_assoc]
    rw [hrot]
    simp [Functor.map_comp, Category.assoc, shift_shift_neg']
