/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Coefficient extension and the ordinary triangle boundary

Source: Stacks Project, Tags 05G3 and 06Y6; naturality of the homology shift.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_shift_square
    {E C : Type u} [CommRing E] [CommRing C] (g : E →+* C)
    (K : CochainComplex (ModuleCat.{u} C) ℤ) (i : ℤ) :
    let G := restrictScalars.{u} g
    let H := G.mapHomologicalComplex (.up ℤ)
    HomologicalComplex.homologyMap ((H.commShiftIso (1 : ℤ)).hom.app K) i ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) 0).shiftIso
          1 i (i + 1) (by omega)).hom.app (H.obj K) ≫
        ((K.sc (i + 1)).mapHomologyIso G).hom =
      (((K⟦(1 : ℤ)⟧).sc i).mapHomologyIso G).hom ≫
        G.map (((HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) 0).shiftIso
          1 i (i + 1) (by omega)).hom.app K) := by
  dsimp only
  let G := restrictScalars.{u} g
  let H := G.mapHomologicalComplex (.up ℤ)
  let a := (CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} C)
    1 i (i + 1) (by omega)).hom.app K
  let b := (CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} E)
    1 i (i + 1) (by omega)).hom.app (H.obj K)
  have hab :
      (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map
          ((H.commShiftIso (1 : ℤ)).hom.app K) ≫ b = G.mapShortComplex.map a := by
    apply ShortComplex.Hom.ext <;>
      simp [a, b, H, HomologicalComplex.XIsoOfEq, eqToHom_map,
      CochainComplex.shiftShortComplexFunctorIso,
      CochainComplex.shiftShortComplexFunctor']
  simp only [Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    CochainComplex.ShiftSequence.shiftIso_hom_app]
  change (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map
        ((H.commShiftIso (1 : ℤ)).hom.app K))) ≫ ShortComplex.homologyMap b ≫
        ((K.sc (i + 1)).mapHomologyIso G).hom = _
  rw [← Category.assoc, ← ShortComplex.homologyMap_comp]
  rw [hab]
  exact ShortComplex.mapHomologyIso_hom_naturality a G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_triangle_boundary
    {E C : Type u} [CommRing E] [CommRing C] (g : E →+* C)
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} C) ℤ)) (i : ℤ) :
    let G := restrictScalars.{u} g
    let H := G.mapHomologicalComplex (.up ℤ)
    CochainComplex.homologyδOfTriangle (H.mapTriangle.obj T) i (i + 1) ≫
        ((T.obj₁.sc (i + 1)).mapHomologyIso G).hom =
      ((T.obj₃.sc i).mapHomologyIso G).hom ≫
        G.map (CochainComplex.homologyδOfTriangle T i (i + 1)) := by
  dsimp only
  let G := restrictScalars.{u} g
  let H := G.mapHomologicalComplex (.up ℤ)
  have hn : HomologicalComplex.homologyMap (H.map T.mor₃) i ≫
      (((T.obj₁⟦(1 : ℤ)⟧).sc i).mapHomologyIso G).hom =
      ((T.obj₃.sc i).mapHomologyIso G).hom ≫
        G.map (HomologicalComplex.homologyMap T.mor₃ i) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map T.mor₃) G
  change (HomologicalComplex.homologyMap
      (H.map T.mor₃ ≫ (H.commShiftIso (1 : ℤ)).hom.app T.obj₁) i ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) 0).shiftIso
          1 i (i + 1) (by omega)).hom.app (H.obj T.obj₁)) ≫
        ((T.obj₁.sc (i + 1)).mapHomologyIso G).hom =
      ((T.obj₃.sc i).mapHomologyIso G).hom ≫ G.map
        (HomologicalComplex.homologyMap T.mor₃ i ≫
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) 0).shiftIso
            1 i (i + 1) (by omega)).hom.app T.obj₁)
  rw [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [restriction_shift_square g T.obj₁ i, ← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical coefficient maps commute with the ordinary triangle boundary after
exact restriction on homology. There is no derived model or exactness assumption.

Source: Stacks Project, Tag 05G3, Lemma 10.14.3 (scalar adjunction), and
Tag 06Y6, Lemma 15.61.1 (the scalar functor on triangles).
Proof: transpose the extension-associativity isomorphism along scalar adjunction.
Its component sends e tensor q to g(e) tensor q. Equality on 1 tensor q
and tensor induction show that the prescribed phi maps are these components.
The associativity isomorphism and the adjunction unit commute with shifts:
their degreewise formulas are independent of the degree, and additive scalar
extension preserves the sign in the shifted differential. They therefore give
a morphism from the E-extension of T to the restriction of its C-extension.
Apply ordinary homology-boundary naturality to that triangle morphism.
Exact restriction has a homology isomorphism compatible with the homology
shift isomorphisms, as follows by its cycle and boundary universal properties.
Composing the naturality equation with these restriction isomorphisms gives
the formula below. No distinguishedness, flatness, boundedness, or invertibility
of the boundary is needed; in particular it holds for zero rings and zero maps.
(blueprint: lem-pc-scalar-coefficient-triangle-boundary). -/
theorem scalarCoefficient_triangle_boundary
    {A E C : Type u} [CommRing A] [CommRing E] [CommRing C]
    (f : A →+* E) (g : E →+* C)
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (φ₁ : ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj T.obj₁ ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj T.obj₁))
    (φ₃ : ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj T.obj₃ ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj T.obj₃))
    (hφ₁ : ∀ (j : ℤ) (e : E) (q : T.obj₁.X j),
      φ₁.f j (e ⊗ₜ[A,f] q) = g e ⊗ₜ[A,g.comp f] q)
    (hφ₃ : ∀ (j : ℤ) (e : E) (q : T.obj₃.X j),
      φ₃.f j (e ⊗ₜ[A,f] q) = g e ⊗ₜ[A,g.comp f] q) (i : ℤ) :
    let J := (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)
    let F := (extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex (.up ℤ)
    CochainComplex.homologyδOfTriangle (J.mapTriangle.obj T) i (i + 1) ≫
        HomologicalComplex.homologyMap φ₁ (i + 1) ≫
        (((F.obj T.obj₁).sc (i + 1)).mapHomologyIso (restrictScalars g)).hom =
      HomologicalComplex.homologyMap φ₃ i ≫
        (((F.obj T.obj₃).sc i).mapHomologyIso (restrictScalars g)).hom ≫
        (restrictScalars g).map
          (CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1)) := by
  dsimp only
  let J := (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)
  let F := (extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex (.up ℤ)
  let G := restrictScalars.{u} g
  let H := G.mapHomologicalComplex (.up ℤ)
  let U := J.mapTriangle.obj T
  let V := H.mapTriangle.obj (F.mapTriangle.obj T)
  have h₃ : U.mor₃ ≫ φ₁⟦(1 : ℤ)⟧' = φ₃ ≫ V.mor₃ := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ExtendScalars.hom_ext
    intro q
    change φ₁.f (j + 1)
        ((extendScalars f).map (T.mor₃.f j) ((1 : E) ⊗ₜ[A,f] q)) =
      (extendScalars (g.comp f)).map (T.mor₃.f j)
        (φ₃.f j ((1 : E) ⊗ₜ[A,f] q))
    rw [ExtendScalars.map_tmul, hφ₁, hφ₃, ExtendScalars.map_tmul]
  have hb : CochainComplex.homologyδOfTriangle U i (i + 1) ≫
      HomologicalComplex.homologyMap φ₁ (i + 1) =
      HomologicalComplex.homologyMap φ₃ i ≫
        CochainComplex.homologyδOfTriangle V i (i + 1) := by
    let e := (HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) 0).shiftIso
      1 i (i + 1) (by omega)
    have hn : HomologicalComplex.homologyMap (φ₁⟦(1 : ℤ)⟧') i ≫
        e.hom.app _ = e.hom.app _ ≫ HomologicalComplex.homologyMap φ₁ (i + 1) :=
      e.hom.naturality φ₁
    change HomologicalComplex.homologyMap (φ₁⟦(1 : ℤ)⟧') i ≫
      e.hom.app V.obj₁ = e.hom.app U.obj₁ ≫ HomologicalComplex.homologyMap φ₁ (i + 1) at hn
    change (HomologicalComplex.homologyMap U.mor₃ i ≫ e.hom.app U.obj₁) ≫
        HomologicalComplex.homologyMap φ₁ (i + 1) =
      (HomologicalComplex.homologyMap φ₃ i ≫ HomologicalComplex.homologyMap V.mor₃ i) ≫
        e.hom.app V.obj₁
    rw [Category.assoc, ← hn, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      h₃, HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [← Category.assoc, hb, Category.assoc]
  have hr : CochainComplex.homologyδOfTriangle V i (i + 1) ≫
      (((F.obj T.obj₁).sc (i + 1)).mapHomologyIso G).hom =
      (((F.obj T.obj₃).sc i).mapHomologyIso G).hom ≫
        G.map (CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1)) :=
    restriction_triangle_boundary g (F.mapTriangle.obj T) i
  exact congrArg (fun k ↦ HomologicalComplex.homologyMap φ₃ i ≫ k) hr


end ModuleCat
