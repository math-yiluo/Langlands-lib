/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChange
import all WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Internal Hom exchange with the canonical base-change mate
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-mixed-internal-hom-base-change-exchange).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem tensorPairing_naturality {S T : Scheme.{u}} (h : T ⟶ S)
    {A A' B B' : schemeDerivedCategory T} (a : A ⟶ A') (b : B ⟶ B') :
    ((schemeDerivedDirectImage h).map a ⊗ₘ (schemeDerivedDirectImage h).map b) ≫
      mixedDirectImageTensorPairing h A' B' =
    mixedDirectImageTensorPairing h A B ≫
      (schemeDerivedDirectImage h).map (a ⊗ₘ b) := by
  let adj := schemeHomPullbackAdjunction h
  let τ := mixedHomTensorPullbackIso h
  dsimp only [mixedDirectImageTensorPairing]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  have ht := τ.hom.naturality
    (X := ((schemeDerivedDirectImage h).obj A, (schemeDerivedDirectImage h).obj B))
    (Y := ((schemeDerivedDirectImage h).obj A', (schemeDerivedDirectImage h).obj B'))
    ((schemeDerivedDirectImage h).map a, (schemeDerivedDirectImage h).map b)
  dsimp only [Functor.comp_map, Functor.prod_map, tensor] at ht
  erw [← Category.assoc, ht, Category.assoc,
    tensorHom_comp_tensorHom]
  erw [Category.assoc, tensorHom_comp_tensorHom]
  erw [adj.counit.naturality a, adj.counit.naturality b]
  rfl

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem map_pair_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' : C} (a : A ⟶ B) (b : B ⟶ C') :
    F.map a ≫ F.map b = F.map (a ≫ b) := (F.map_comp a b).symm

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensor_evaluation_interchange
    {D : Type*} [Category D] [MonoidalCategory D] {W A B C V Q : D}
    (k : W ⟶ A ⊗ B) (a : A ⟶ C) (b : B ⟶ V) (v : C ⊗ V ⟶ Q) :
    k ≫ (𝟙 A ⊗ₘ b) ≫ (a ⊗ₘ 𝟙 V) ≫ v = (k ≫ (a ⊗ₘ b)) ≫ v := by
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensorHom_counit_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (F : D ⥤ C) (R : C ⥤ D) (adj : F ⊣ R)
    (τ : tensor D ⋙ F ≅ F.prod F ⋙ tensor C)
    (e : ∀ A P Q : C, (A ⟶ H.obj (op P, Q)) ≃ (A ⊗ P ⟶ Q))
    (he : ∀ (A A' P P' Q Q' : C) (a : A' ⟶ A) (b : P' ⟶ P) (d : Q ⟶ Q')
      (z : A ⟶ H.obj (op P, Q)),
      e A' P' Q' (a ≫ z ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A P Q z ≫ d)
    (P Q : C) :
    adj.homEquiv _ Q
      (τ.hom.app (R.obj (H.obj (op P, Q)), R.obj P) ≫
        (𝟙 _ ⊗ₘ adj.counit.app P) ≫
          e _ P Q ((adj.homEquiv _ _).symm (𝟙 (R.obj (H.obj (op P, Q)))))) =
    adj.homEquiv _ _
      (τ.hom.app (R.obj (H.obj (op P, Q)), R.obj P) ≫
        (adj.counit.app (H.obj (op P, Q)) ⊗ₘ adj.counit.app P)) ≫
      R.map (e _ P Q (𝟙 _)) := by
  have hn := he _ _ P P Q Q (adj.counit.app (H.obj (op P, Q))) (𝟙 P) (𝟙 Q) (𝟙 _)
  have hid : H.map ((𝟙 P).op, 𝟙 Q) = 𝟙 (H.obj (op P, Q)) := H.map_id (op P, Q)
  erw [hid, Category.comp_id, Category.comp_id, Category.comp_id] at hn
  erw [Adjunction.homEquiv_counit, F.map_id, Category.id_comp, hn,
    ← adj.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ Q)
    (tensor_evaluation_interchange
      (τ.hom.app (R.obj (H.obj (op P, Q)), R.obj P))
      (adj.counit.app (H.obj (op P, Q))) (adj.counit.app P) (e _ P Q (𝟙 _)))

-- Evaluation crosses the two definitionally equal presentations of scheme module sheaves.
private theorem directImage_evaluation {S T : Scheme.{u}} (h : T ⟶ S)
    (P Q : schemeDerivedCategory T) :
    schemeDerivedTensorHomEquiv S _ _ _
      ((mixedHomDirectImageComparison h).app (op P, Q)) =
    mixedDirectImageTensorPairing h
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj (op P, Q)) P ≫
      (schemeDerivedDirectImage h).map
        (schemeDerivedTensorHomEquiv T _ P Q (𝟙 _)) := by
  have hc := (Classical.choose_spec (exists_schemeHomDirectImageComparison h))
    P Q ((schemeDerivedDirectImage h).obj
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj (op P, Q))) (𝟙 _)
  simp only [Category.id_comp] at hc
  exact hc.trans (tensorHom_counit_evaluation
    (derivedInternalHom (Opens.grothendieckTopology T) T.sheaf)
    (derivedPullback h) (schemeDerivedDirectImage h) (schemeHomPullbackAdjunction h)
    (mixedHomTensorPullbackIso h) (schemeDerivedTensorHomEquiv T)
    (schemeHomTensorHom_naturality T) P Q)

private theorem evaluation_formula (S : Scheme.{u})
    (A P Q : schemeDerivedCategory S)
    (z : A ⟶ (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)) :
    schemeDerivedTensorHomEquiv S A P Q z =
      (z ⊗ₘ 𝟙 P) ≫ schemeDerivedTensorHomEquiv S _ P Q (𝟙 _) := by
  have hn := schemeHomTensorHom_naturality S
    _ A P P Q Q z (𝟙 P) (𝟙 Q) (𝟙 _)
  have hid : (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).map
      (X := (op P, Q)) (Y := (op P, Q)) ((𝟙 P).op, 𝟙 Q) = 𝟙 _ :=
    (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).map_id (op P, Q)
  erw [hid] at hn
  simpa only [Category.comp_id] using hn

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensorHom_directImage_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D) (R : C ⥤ D)
    (e : ∀ A P Q : D, (A ⟶ H.obj (op P, Q)) ≃ (A ⊗ P ⟶ Q))
    (he : ∀ (A A' P P' Q Q' : D) (a : A' ⟶ A) (b : P' ⟶ P) (d : Q ⟶ Q')
      (z : A ⟶ H.obj (op P, Q)),
      e A' P' Q' (a ≫ z ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A P Q z ≫ d)
    {A P Q E : C} {U V : D} (a : A ⟶ E)
    (c : R.obj E ⟶ H.obj (op (R.obj P), R.obj Q))
    (v : E ⊗ P ⟶ Q) (q : A ⊗ P ⟶ Q)
    (μ : R.obj A ⊗ R.obj P ⟶ R.obj (A ⊗ P))
    (μE : R.obj E ⊗ R.obj P ⟶ R.obj (E ⊗ P))
    (ha : (a ⊗ₘ 𝟙 P) ≫ v = q)
    (hc : e _ _ _ c = μE ≫ R.map v)
    (hμ : (R.map a ⊗ₘ 𝟙 (R.obj P)) ≫ μE = μ ≫ R.map (a ⊗ₘ 𝟙 P))
    (b : U ⟶ R.obj A) (d : V ⟶ R.obj P) :
    e U V (R.obj Q) (b ≫ R.map a ≫ c ≫ H.map (d.op, 𝟙 _)) =
      (b ⊗ₘ d) ≫ μ ≫ R.map q := by
  have hn := he _ _ _ _ _ _ (b ≫ R.map a) d (𝟙 _) c
  simp only [Category.comp_id, Category.assoc] at hn
  rw [hn, hc]
  have hs : ((b ≫ R.map a) ⊗ₘ d) = (b ⊗ₘ d) ≫ (R.map a ⊗ₘ 𝟙 _) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hs]
  simp only [Category.assoc]
  rw [reassoc_of% hμ, ← R.map_comp, ha]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensorHom_pullback_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D) (F : C ⥤ D)
    (τ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (e : ∀ A P Q : D, (A ⟶ H.obj (op P, Q)) ≃ (A ⊗ P ⟶ Q))
    (he : ∀ (A A' P P' Q Q' : D) (a : A' ⟶ A) (b : P' ⟶ P) (d : Q ⟶ Q')
      (z : A ⟶ H.obj (op P, Q)),
      e A' P' Q' (a ≫ z ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A P Q z ≫ d)
    {A P Q E : C} {V : D} (t : A ⟶ E)
    (b : F.obj E ⟶ H.obj (op (F.obj P), F.obj Q))
    (v : E ⊗ P ⟶ Q) (q : A ⊗ P ⟶ Q)
    (hb : e _ _ _ b = τ.inv.app (E, P) ≫ F.map v)
    (ht : (t ⊗ₘ 𝟙 P) ≫ v = q) (d : F.obj Q ⟶ V) :
    e _ _ _ (F.map t ≫ b ≫ H.map ((𝟙 (F.obj P)).op, d)) =
      τ.inv.app (A, P) ≫ F.map q ≫ d := by
  rw [he, hb]
  have hn := τ.inv.naturality (X := (A, P)) (Y := (E, P)) (t, 𝟙 P)
  dsimp only [Functor.comp_map, Functor.prod_map, tensor] at hn
  rw [F.map_id] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% (map_pair_comp F (t ⊗ₘ 𝟙 P) v), ht]

-- Tensor-Hom naturality crosses scheme and ringed-space presentations.
/-- The exchange identity before applying global sections.
Here `p` is the pullback of evaluation transposed by the fixed tensor-Hom bijection.
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-mixed-internal-hom-base-change-exchange).

Proof: transpose both sides by the tensor-Hom bijection on Y'. Naturality in the
first Hom input replaces precomposition by beta_M with tensoring by beta_M;
naturality in the second input replaces postcomposition by beta_N with beta_N.
Use the evaluation-mate equation for the direct-image comparisons, and the
construction of p as pulled-back evaluation. Transpose beta under the f'
adjunction: it is the pullback-composition comparison followed by the pullback
of the f counit. Naturality of that counit and the f' triangle identity cancel
the unit-counit pairs. The remaining tensor comparisons agree: on K-flat
representatives both are the ordinary tensor-pullback comparison along the
commutative square, and uniqueness of the left-derived comparison extends
this equality to all objects. Thus both transposed composites agree, and
injectivity of the tensor-Hom bijection gives the equation. -/
theorem mixedInternalHom_baseChange_exchange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) :
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((mixedHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let H := fun Z : Scheme.{u} ↦ derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    mixedHomDirectImageComparison h
  schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((H X).obj (op M, N)) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map (p (pullback.fst f g) M N) ≫
    (c (pullback.snd f g)).app
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj N) ≫
    (H Y').map
      (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition M).op, 𝟙 _) =
    (derivedPullback g).map ((c f).app (op M, N)) ≫
      p g ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫
      (H Y').map
        ((𝟙 _).op, schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition N) := by
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((mixedHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let H (Z : Scheme.{u}) : (schemeDerivedCategory Z)ᵒᵖ × schemeDerivedCategory Z ⥤
      schemeDerivedCategory Z := derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    mixedHomDirectImageComparison h
  let R := schemeDerivedDirectImage f
  let R' := schemeDerivedDirectImage (pullback.snd f g)
  let L := derivedPullback g
  let L' := derivedPullback (pullback.fst f g)
  let E : schemeDerivedCategory X := (H X).obj (op M, N)
  let E' : schemeDerivedCategory (pullback f g) := (H (pullback f g)).obj (op (L'.obj M), L'.obj N)
  let β := fun Z ↦ schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition Z
  let a : L'.obj E ⟶ E' := p (pullback.fst f g) M N
  let b : L.obj ((H Y).obj (op (R.obj M), R.obj N)) ⟶
      (H Y').obj (op (L.obj (R.obj M)), L.obj (R.obj N)) := p g (R.obj M) (R.obj N)
  let z : L.obj (R.obj E) ⟶ (H Y').obj
      (op (R'.obj (L'.obj M)), R'.obj (L'.obj N)) :=
    β E ≫ R'.map a ≫ (c (pullback.snd f g)).app (op (L'.obj M), L'.obj N)
  let t : R.obj E ⟶ (H Y).obj (op (R.obj M), R.obj N) := (c f).app (op M, N)
  suffices hex : z ≫ (H Y').map (X := (op (R'.obj (L'.obj M)), R'.obj (L'.obj N)))
      (Y := (op (L.obj (R.obj M)), R'.obj (L'.obj N))) ((β M).op, 𝟙 _) =
    L.map t ≫ b ≫ (H Y').map ((𝟙 _).op, β N) by
      simpa only [z, t, a, b, R, R', L, L', E, β, Category.assoc] using hex
  apply (schemeDerivedTensorHomEquiv Y' _ _ _).injective
  have ha : schemeDerivedTensorHomEquiv (pullback f g) _ _ _ a =
      (mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (E, M) ≫
        L'.map (schemeDerivedTensorHomEquiv X E M N (𝟙 E)) :=
    (schemeDerivedTensorHomEquiv (pullback f g) _ _ _).apply_symm_apply _
  have hb : schemeDerivedTensorHomEquiv Y' _ _ _ b =
      (mixedHomTensorPullbackIso g).inv.app
        ((H Y).obj (op (R.obj M), R.obj N), R.obj M) ≫
        L.map (schemeDerivedTensorHomEquiv Y _ _ _ (𝟙 _)) :=
    (schemeDerivedTensorHomEquiv Y' _ _ _).apply_symm_apply _
  have hq := tensorPairing_naturality (pullback.snd f g) a (𝟙 (L'.obj M))
  erw [CategoryTheory.Functor.map_id] at hq
  have hl := tensorHom_directImage_evaluation (H Y') R'
    (schemeDerivedTensorHomEquiv Y') (schemeHomTensorHom_naturality Y') a
    ((c (pullback.snd f g)).app (op (L'.obj M), L'.obj N))
    (schemeDerivedTensorHomEquiv (pullback f g) E' (L'.obj M) (L'.obj N) (𝟙 E'))
    ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (E, M) ≫
      L'.map (schemeDerivedTensorHomEquiv X E M N (𝟙 E)))
    (mixedDirectImageTensorPairing (pullback.snd f g) (L'.obj E) (L'.obj M))
    (mixedDirectImageTensorPairing (pullback.snd f g) E' (L'.obj M))
    ((evaluation_formula (pullback f g) _ _ _ a).symm.trans ha)
    (directImage_evaluation (pullback.snd f g) (L'.obj M) (L'.obj N)) hq (β E) (β M)
  have hr := tensorHom_pullback_evaluation (H Y') L (mixedHomTensorPullbackIso g)
    (schemeDerivedTensorHomEquiv Y') (schemeHomTensorHom_naturality Y') t b
    (schemeDerivedTensorHomEquiv Y ((H Y).obj (op (R.obj M), R.obj N))
      (R.obj M) (R.obj N) (𝟙 _))
    (mixedDirectImageTensorPairing f E M ≫
      R.map (schemeDerivedTensorHomEquiv X E M N (𝟙 E))) hb
    ((evaluation_formula Y _ _ _ t).symm.trans (directImage_evaluation f M N)) (β N)
  simpa only [z, Category.assoc] using
    hl.trans ((mixedTensorPairing_baseChange f g E M N
      (schemeDerivedTensorHomEquiv X E M N (𝟙 E))).trans hr.symm)

end AlgebraicGeometry
