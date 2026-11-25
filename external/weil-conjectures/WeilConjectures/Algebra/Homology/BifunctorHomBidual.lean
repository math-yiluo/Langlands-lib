/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomComplex

/-!
# The double-dual morphism of hom complexes

Let `H : Cᵒᵖ ⥤ C ⥤ C` be a bifunctor, additive in each variable, with a family of morphisms
`ev a b : a ⟶ H(H(a, b), b)` which is natural in `a` and dinatural in `b` (for an internal hom,
`a ⟶ Hom(Hom(a, b), b)`, `x ↦ (φ ↦ φ(x))`). For cochain complexes `K` and `Y` this file
constructs the double-dual morphism of hom complexes
(`CochainComplex.bifunctorHomBidual`)

`K ⟶ bifunctorHomObj H (bifunctorHomObj H K Y) Y`,

whose component `Kᵐ ⟶ H((bifunctorHomObj H K Y)ⁿ, Yⁿ⁺ᵐ)` is `(-1)^(m n)` times `ev` followed by
the projection `(bifunctorHomObj H K Y)ⁿ ⟶ H(Kᵐ, Yⁿ⁺ᵐ)`. It is natural in `K`
(`CochainComplex.bifunctorHomBidual_naturality`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [∀ X, (H.obj X).Additive] [H.Additive]

/-- A family of evaluation morphisms `a ⟶ H(H(a, b), b)` for a bifunctor `H`, natural in `a`
and dinatural in `b`. -/
structure BifunctorEvaluation where
  /-- The evaluation morphism `a ⟶ H(H(a, b), b)`. -/
  ev (a b : C) : a ⟶ (H.obj (op ((H.obj (op a)).obj b))).obj b
  naturality {a a' : C} (f : a ⟶ a') (b : C) :
    f ≫ ev a' b = ev a b ≫ (H.map ((H.map f.op).app b).op).app b
  dinaturality (a : C) {b b' : C} (g : b ⟶ b') :
    ev a b ≫ (H.obj (op ((H.obj (op a)).obj b))).map g =
      ev a b' ≫ (H.map ((H.obj (op a)).map g).op).app b'

variable {H} (E : BifunctorEvaluation H) (K Y : CochainComplex C ℤ)

/-- The component `Kᵐ ⟶ H((bifunctorHomObj H K Y)ⁿ, Yʳ)`, `n + m = r`, of the double-dual
morphism. -/
noncomputable def bifunctorHomBidualComponent (m n r : ℤ) (h : n + m = r) :
    K.X m ⟶ (H.obj (op ((bifunctorHomObj H K Y).X n))).obj (Y.X r) :=
  (m * n).negOnePow • (E.ev (K.X m) (Y.X r) ≫
    (H.map (bifunctorHomπ H K Y n m r (by omega)).op).app (Y.X r))

/-- The double-dual morphism `K ⟶ bifunctorHomObj H (bifunctorHomObj H K Y) Y`. -/
noncomputable def bifunctorHomBidual : K ⟶ bifunctorHomObj H (bifunctorHomObj H K Y) Y where
  f m := bifunctorHomLift H (bifunctorHomObj H K Y) Y m fun n r h ↦
    bifunctorHomBidualComponent E K Y m n r h
  comm' m m' hmm' := by
    simp only [ComplexShape.up_Rel] at hmm'
    subst hmm'
    ext n r hnr
    let L := bifunctorHomObj H K Y
    have eA : E.ev (K.X m) (Y.X (n + m)) ≫
        (H.map (bifunctorHomπ H K Y n m (n + m) (by omega)).op).app (Y.X (n + m)) ≫
          (H.obj (op (L.X n))).map (Y.d (n + m) r) =
        E.ev (K.X m) (Y.X r) ≫ (H.map (bifunctorHomπ H K Y n m (n + m) (by omega) ≫
          (H.obj (op (K.X m))).map (Y.d (n + m) r)).op).app (Y.X r) := by
      rw [← (H.map _).naturality, reassoc_of% (E.dinaturality (K.X m) (Y.d (n + m) r)),
        op_comp, Functor.map_comp, NatTrans.comp_app]
    have eB := bifunctorHomObj_d_π H K Y n (n + 1) m r (by omega) (n + m) (m + 1) (by omega)
      (by omega)
    have eC : E.ev (K.X m) (Y.X r) ≫ (H.map (bifunctorHomπ H K Y n (m + 1) r (by omega) ≫
          (H.map (K.d m (m + 1)).op).app (Y.X r)).op).app (Y.X r) =
        K.d m (m + 1) ≫ E.ev (K.X (m + 1)) (Y.X r) ≫
          (H.map (bifunctorHomπ H K Y n (m + 1) r (by omega)).op).app (Y.X r) := by
      rw [op_comp, Functor.map_comp, NatTrans.comp_app, reassoc_of% (E.naturality _ _)]
    have eD : E.ev (K.X m) (Y.X r) ≫
        (H.map (bifunctorHomπ H K Y (n + 1) m r (by omega)).op).app (Y.X r) ≫
          (H.map (L.d n (n + 1)).op).app (Y.X r) =
        m.negOnePow • (E.ev (K.X m) (Y.X r) ≫ (H.map (bifunctorHomπ H K Y n m (n + m)
          (by omega) ≫ (H.obj (op (K.X m))).map (Y.d (n + m) r)).op).app (Y.X r) -
          E.ev (K.X m) (Y.X r) ≫ (H.map (bifunctorHomπ H K Y n (m + 1) r (by omega) ≫
            (H.map (K.d m (m + 1)).op).app (Y.X r)).op).app (Y.X r)) := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
      change E.ev (K.X m) (Y.X r) ≫ (H.map ((bifunctorHomObj H K Y).d n (n + 1) ≫
        bifunctorHomπ H K Y (n + 1) m r _).op).app (Y.X r) = _
      rw [eB]
      simp only [Units.smul_def, op_zsmul, op_sub, Functor.map_zsmul, Functor.map_sub,
        NatTrans.app_zsmul, NatTrans.app_sub, Preadditive.comp_zsmul, Preadditive.comp_sub]
    rw [assoc, bifunctorHomObj_d_π H L Y m (m + 1) n r hnr (n + m) (n + 1) rfl (by omega),
      Linear.comp_units_smul, Preadditive.comp_sub, bifunctorHomLift_π_assoc,
      bifunctorHomLift_π_assoc, assoc, bifunctorHomLift_π]
    simp only [bifunctorHomBidualComponent, Linear.comp_units_smul, Linear.units_smul_comp,
      assoc]
    rw [eA, eD, eC]
    have h₁ : (m * (n + 1)).negOnePow * m.negOnePow = (m * n).negOnePow := by
      rw [← Int.negOnePow_add]
      exact (Int.negOnePow_eq_iff _ _).2 ⟨m, by ring⟩
    have h₂ : n.negOnePow * (m * n).negOnePow = ((m + 1) * n).negOnePow := by
      rw [← Int.negOnePow_add]
      exact (Int.negOnePow_eq_iff _ _).2 ⟨0, by ring⟩
    rw [smul_smul, h₁, ← smul_sub, sub_sub_cancel, smul_smul, h₂]

@[reassoc (attr := simp)]
lemma bifunctorHomBidual_f_π (m n r : ℤ) (h : n + m = r) :
    (bifunctorHomBidual E K Y).f m ≫ bifunctorHomπ H (bifunctorHomObj H K Y) Y m n r h =
      bifunctorHomBidualComponent E K Y m n r h :=
  bifunctorHomLift_π _ _ _ _ _ _ _ _

instance {K' : CochainComplex C ℤ} (f : K' ⟶ K) [IsIso f] :
    IsIso (bifunctorHomMapLeft (H := H) (Y := Y) f) :=
  ⟨bifunctorHomMapLeft (inv f), by
    rw [← bifunctorHomMapLeft_comp, IsIso.inv_hom_id, bifunctorHomMapLeft_id], by
    rw [← bifunctorHomMapLeft_comp, IsIso.hom_inv_id, bifunctorHomMapLeft_id]⟩

variable {K} in
/-- The double-dual morphism is natural in `K`. -/
@[reassoc]
lemma bifunctorHomBidual_naturality {K' : CochainComplex C ℤ} (f : K' ⟶ K) :
    f ≫ bifunctorHomBidual E K Y = bifunctorHomBidual E K' Y ≫
      bifunctorHomMapLeft (H := H) (Y := Y) (bifunctorHomMapLeft (H := H) (Y := Y) f) := by
  ext m n r h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, assoc, assoc,
    bifunctorHomBidual_f_π, bifunctorHomMapLeft_f_π, bifunctorHomBidual_f_π_assoc]
  simp only [bifunctorHomBidualComponent, Linear.comp_units_smul, Linear.units_smul_comp, assoc]
  congr 1
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, bifunctorHomMapLeft_f_π, op_comp,
    Functor.map_comp, NatTrans.comp_app, reassoc_of% (E.naturality (f.f m) (Y.X r))]

section Map

variable {C' : Type*} [Category* C'] [Preadditive C'] [HasCountableProducts C']
  {H' : C'ᵒᵖ ⥤ C' ⥤ C'} [∀ X, (H'.obj X).Additive] [H'.Additive]
  (U : C ⥤ C') [U.Additive] [∀ n : ℤ, PreservesLimitsOfShape (Discrete (HomComplex.Triplet n)) U]

variable (H H') in
/-- A natural identification `U (H(a, b)) ≅ H'(U a, U b)`. -/
structure BifunctorMapIso where
  /-- The identification `U (H(a, b)) ≅ H'(U a, U b)`. -/
  iso (a b : C) : U.obj ((H.obj (op a)).obj b) ≅ (H'.obj (op (U.obj a))).obj (U.obj b)
  naturality_left {a a' : C} (f : a ⟶ a') (b : C) :
    U.map ((H.map f.op).app b) ≫ (iso a b).hom = (iso a' b).hom ≫ (H'.map (U.map f).op).app _
  naturality_right (a : C) {b b' : C} (g : b ⟶ b') :
    U.map ((H.obj (op a)).map g) ≫ (iso a b').hom = (iso a b).hom ≫ (H'.obj _).map (U.map g)

variable {U} (φ : BifunctorMapIso H H' U)

/-- The identification `U ((bifunctorHomObj H K Y)ⁿ) ≅ (bifunctorHomObj H' (U K) (U Y))ⁿ` in
each degree. Use `bifunctorHomXMapIso_hom_π` instead of unfolding it. -/
noncomputable def bifunctorHomXMapIso (n : ℤ) :
    U.obj ((bifunctorHomObj H K Y).X n) ≅ (bifunctorHomObj H' ((U.mapHomologicalComplex _).obj K)
      ((U.mapHomologicalComplex _).obj Y)).X n :=
  PreservesProduct.iso U _ ≪≫ Pi.mapIso fun T ↦ φ.iso (K.X T.p) (Y.X T.q)

@[reassoc (attr := simp)]
lemma bifunctorHomXMapIso_hom_π (n p q : ℤ) (h : p + n = q) :
    (bifunctorHomXMapIso K Y φ n).hom ≫ bifunctorHomπ H' _ _ n p q h =
      U.map (bifunctorHomπ H K Y n p q h) ≫ (φ.iso (K.X p) (Y.X q)).hom := by
  simp [bifunctorHomXMapIso, bifunctorHomπ]

/-- The identification `U (bifunctorHomObj H K Y) ≅ bifunctorHomObj H' (U K) (U Y)` of hom
complexes, for a functor `U` commuting with `H` and with countable products. -/
noncomputable def bifunctorHomObjMapIso :
    (U.mapHomologicalComplex _).obj (bifunctorHomObj H K Y) ≅
      bifunctorHomObj H' ((U.mapHomologicalComplex _).obj K) ((U.mapHomologicalComplex _).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (bifunctorHomXMapIso K Y φ) (by
    rintro n m (rfl : n + 1 = m)
    ext p q hpq
    rw [assoc, assoc, bifunctorHomXMapIso_hom_π, Functor.mapHomologicalComplex_obj_d,
      ← U.map_comp_assoc, bifunctorHomObj_d_π H K Y n (n + 1) p q hpq (q - 1) (p + 1) (by lia)
      (by lia), bifunctorHomObj_d_π _ _ _ n (n + 1) p q hpq (q - 1) (p + 1) (by lia) (by lia)]
    simp only [Functor.map_units_smul, Functor.map_sub, Functor.map_comp,
      Linear.units_smul_comp, Linear.comp_units_smul, Preadditive.sub_comp,
      Preadditive.comp_sub, assoc, φ.naturality_left, φ.naturality_right,
      bifunctorHomXMapIso_hom_π_assoc, Functor.mapHomologicalComplex_obj_d]
    rfl)

@[reassoc (attr := simp)]
lemma bifunctorHomObjMapIso_hom_f_π (n p q : ℤ) (h : p + n = q) :
    (bifunctorHomObjMapIso K Y φ).hom.f n ≫ bifunctorHomπ H' _ _ n p q h =
      U.map (bifunctorHomπ H K Y n p q h) ≫ (φ.iso (K.X p) (Y.X q)).hom :=
  bifunctorHomXMapIso_hom_π K Y φ n p q h

@[reassoc]
lemma bifunctorHomObjMapIso_inv_f_map_π (n p q : ℤ) (h : p + n = q) :
    (bifunctorHomObjMapIso K Y φ).inv.f n ≫ U.map (bifunctorHomπ H K Y n p q h) =
      bifunctorHomπ H' _ _ n p q h ≫ (φ.iso (K.X p) (Y.X q)).inv := by
  rw [Iso.eq_comp_inv, assoc, ← bifunctorHomObjMapIso_hom_f_π,
    ← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id, HomologicalComplex.id_f, id_comp]

/-- An evaluation for `H'` is compatible with an evaluation for `H` through `φ`. -/
def BifunctorEvaluation.MapCompatible (E' : BifunctorEvaluation H') : Prop :=
  ∀ a b : C, U.map (E.ev a b) ≫ (φ.iso _ b).hom ≫ (H'.map (φ.iso a b).inv.op).app (U.obj b) =
    E'.ev (U.obj a) (U.obj b)

/-- A functor commuting with the bifunctors and the evaluations carries the double-dual
morphism of `K` to the double-dual morphism of `U K`. -/
lemma map_bifunctorHomBidual (E' : BifunctorEvaluation H') (hE : E.MapCompatible φ E') :
    (U.mapHomologicalComplex _).map (bifunctorHomBidual E K Y) ≫
        (bifunctorHomObjMapIso (bifunctorHomObj H K Y) Y φ).hom ≫
          bifunctorHomMapLeft (H := H') (bifunctorHomObjMapIso K Y φ).inv =
      bifunctorHomBidual E' ((U.mapHomologicalComplex _).obj K)
        ((U.mapHomologicalComplex _).obj Y) := by
  ext m n r h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, assoc, assoc,
    bifunctorHomMapLeft_f_π, bifunctorHomObjMapIso_hom_f_π_assoc,
    Functor.mapHomologicalComplex_map_f, ← U.map_comp_assoc, bifunctorHomBidual_f_π,
    bifunctorHomBidual_f_π]
  simp only [bifunctorHomBidualComponent, Functor.map_units_smul, Linear.units_smul_comp]
  congr 1
  refine Eq.trans ?_ (hE (K.X m) (Y.X r) =≫ _)
  rw [U.map_comp, assoc, reassoc_of% (φ.naturality_left _ _), assoc, assoc]
  refine U.map _ ≫= _ ≫= (NatTrans.comp_app _ _ _).symm.trans ?_
  rw [← Functor.map_comp, ← op_comp, bifunctorHomObjMapIso_inv_f_map_π, op_comp,
    Functor.map_comp, NatTrans.comp_app]
  rfl

end Map

end CochainComplex
