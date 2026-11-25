/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.Basic

/-! # Product-total Hom complexes under an additive functor

Source: Stacks Project, Section 0A8X; the component calculation in steps 4–5 of
lem-sf-ringed-forget-two-injective-hom.
(blueprint: lem-sf-ringed-hom-complex-comparison).

The complex functors and their projection equations are parameters, so the argument never
unfolds a chosen construction of a Hom complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe b vb a va

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {B : Type b} [Category.{vb} B] [Preadditive B]
  {A : Type a} [Category.{va} A] [Preadditive A]
  (U : B ⥤ A) [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  (HB : Bᵒᵖ ⥤ B ⥤ B) (HA : Aᵒᵖ ⥤ A ⥤ A)
  (FB : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ)
  (FA : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex A ℤ)
  (πB : ∀ (K I : CochainComplex B ℤ) (n p q : ℤ) (_hpq : p + n = q),
    (FB.obj (op K, I)).X n ⟶ (HB.obj (op (K.X p))).obj (I.X q))
  (πA : ∀ (K I : CochainComplex A ℤ) (n p q : ℤ) (_hpq : p + n = q),
    (FA.obj (op K, I)).X n ⟶ (HA.obj (op (K.X p))).obj (I.X q))
  (limitB : ∀ (K I : CochainComplex B ℤ) (n : ℤ),
    IsLimit (Fan.mk ((FB.obj (op K, I)).X n) (fun p ↦ πB K I n p (p + n) rfl)))
  (limitA : ∀ (K I : CochainComplex A ℤ) (n : ℤ),
    IsLimit (Fan.mk ((FA.obj (op K, I)).X n) (fun p ↦ πA K I n p (p + n) rfl)))
  (dB : ∀ (K I : CochainComplex B ℤ) (n m p q q' p' : ℤ)
    (_hnm : n + 1 = m) (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
    (FB.obj (op K, I)).d n m ≫ πB K I m p q hpq =
      πB K I n p q' hq' ≫ (HB.obj (op (K.X p))).map (I.d q' q) -
        n.negOnePow • (πB K I n p' q hp' ≫ (HB.map (K.d p p').op).app (I.X q)))
  (dA : ∀ (K I : CochainComplex A ℤ) (n m p q q' p' : ℤ)
    (_hnm : n + 1 = m) (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
    (FA.obj (op K, I)).d n m ≫ πA K I m p q hpq =
      πA K I n p q' hq' ≫ (HA.obj (op (K.X p))).map (I.d q' q) -
        n.negOnePow • (πA K I n p' q hp' ≫ (HA.map (K.d p p').op).app (I.X q)))
  (mB : ∀ (K K' I I' : CochainComplex B ℤ) (f : K' ⟶ K) (g : I ⟶ I')
    (n p q : ℤ) (hpq : p + n = q),
    (FB.map (f.op, g)).f n ≫ πB K' I' n p q hpq =
      πB K I n p q hpq ≫ (HB.map (f.f p).op).app (I.X q) ≫
        (HB.obj (op (K'.X p))).map (g.f q))
  (mA : ∀ (K K' I I' : CochainComplex A ℤ) (f : K' ⟶ K) (g : I ⟶ I')
    (n p q : ℤ) (hpq : p + n = q),
    (FA.map (f.op, g)).f n ≫ πA K' I' n p q hpq =
      πA K I n p q hpq ≫ (HA.map (f.f p).op).app (I.X q) ≫
        (HA.obj (op (K'.X p))).map (g.f q))
  (h : Functor.uncurry.obj HB ⋙ U ≅ (U.op.prod U) ⋙ Functor.uncurry.obj HA)

omit [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  [Preadditive B] [Preadditive A] in
private lemma comparison_naturality {M M' N N' : B} (f : M' ⟶ M) (g : N ⟶ N') :
    U.map ((HB.map f.op).app N ≫ (HB.obj (op M')).map g) ≫ h.hom.app (op M', N') =
      h.hom.app (op M, N) ≫ (HA.map (U.map f).op).app (U.obj N) ≫
        (HA.obj (op (U.obj M'))).map (U.map g) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.op_map, Functor.uncurry_obj_map,
    Quiver.Hom.unop_op, Functor.prod_obj, Functor.op_obj, Functor.comp_obj,
    Functor.uncurry_obj_obj, Category.assoc] using
    h.hom.naturality (X := (op M, N)) (Y := (op M', N')) (f.op, g)

omit [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  [Preadditive B] [Preadditive A] in
private lemma comparison_post {M N N' : B} (g : N ⟶ N') :
    U.map ((HB.obj (op M)).map g) ≫ h.hom.app (op M, N') =
      h.hom.app (op M, N) ≫ (HA.obj (op (U.obj M))).map (U.map g) := by
  have hn := comparison_naturality U HB HA h (𝟙 M) g
  dsimp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj,
    Functor.op_obj] at hn
  simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hn

omit [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  [Preadditive B] [Preadditive A] in
private lemma comparison_pre {M M' N : B} (f : M' ⟶ M) :
    U.map ((HB.map f.op).app N) ≫ h.hom.app (op M', N) =
      h.hom.app (op M, N) ≫ (HA.map (U.map f).op).app (U.obj N) := by
  simpa only [Functor.map_id, Category.comp_id] using
    comparison_naturality U HB HA h f (𝟙 N)

omit [PreservesLimitsOfShape (Discrete ℤ) U] in
private lemma map_sign {M N : B} (n : ℤ) (f : M ⟶ N) :
    U.map (n.negOnePow • f) = n.negOnePow • U.map f := by
  change U.map ((n.negOnePow : ℤ) • f) = (n.negOnePow : ℤ) • U.map f
  exact U.map_zsmul

private def termIso (K I : CochainComplex B ℤ) (n : ℤ) :
    U.obj ((FB.obj (op K, I)).X n) ≅
      (FA.obj (op ((U.mapHomologicalComplex (.up ℤ)).obj K),
        (U.mapHomologicalComplex (.up ℤ)).obj I)).X n := by
  let F : ℤ → B := fun p ↦ (HB.obj (op (K.X p))).obj (I.X (p + n))
  let c : Fan F := Fan.mk _ (fun p ↦ πB K I n p (p + n) rfl)
  let e : Discrete.functor (fun p ↦ U.obj (F p)) ≅
      Discrete.functor (fun p ↦ (HA.obj (op (U.obj (K.X p)))).obj (U.obj (I.X (p + n)))) :=
    Discrete.natIso (fun p ↦ h.app (op (K.X p.as), I.X (p.as + n)))
  let hc := (Fan.isLimitMapConeEquiv U F c) (isLimitOfPreserves U (limitB K I n))
  let hc' := (IsLimit.postcomposeHomEquiv e _).symm hc
  exact hc'.conePointUniqueUpToIso
    (limitA ((U.mapHomologicalComplex (.up ℤ)).obj K)
      ((U.mapHomologicalComplex (.up ℤ)).obj I) n)

@[reassoc] private lemma termIso_projection (K I : CochainComplex B ℤ) (n p q : ℤ)
    (hpq : p + n = q) :
    (termIso U HB HA FB FA πB πA limitB limitA h K I n).hom ≫
        πA ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
      U.map (πB K I n p q hpq) ≫ h.hom.app (op (K.X p), I.X q) := by
  subst q
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk p)

include limitB limitA dB dA mB mA in
/-- The projection-normalized natural comparison of product-total Hom complexes.
Source: Stacks Project, Section 0A8X; steps 4–5 of the ringed-forgetting comparison
(blueprint: lem-sf-ringed-hom-complex-comparison).
Proof: apply U to each product cone and transport the factors through h. Product-cone
uniqueness gives term isomorphisms with the required projection equation. On every projection,
the two differential formulas agree by naturality of h, additivity, and preservation of the
integer signs. The map-projection formulas give the naturality square in the same way.
Assemble the term isomorphisms into chain isomorphisms and then a natural isomorphism. -/
theorem ringedHomComplexComparison :
    ∃ chain : FB ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙ FA,
      ∀ (K I : CochainComplex B ℤ) (n p q : ℤ) (hpq : p + n = q),
        (chain.hom.app (op K, I)).f n ≫
            πA ((U.mapHomologicalComplex (.up ℤ)).obj K)
              ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
          U.map (πB K I n p q hpq) ≫ h.hom.app (op (K.X p), I.X q) := by
  let e := termIso U HB HA FB FA πB πA limitB limitA h
  have ep (K I : CochainComplex B ℤ) (n p q : ℤ) (hpq : p + n = q) :
      (e K I n).hom ≫ πA ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
        U.map (πB K I n p q hpq) ≫ h.hom.app (op (K.X p), I.X q) :=
    termIso_projection U HB HA FB FA πB πA limitB limitA h K I n p q hpq
  have comm (K I : CochainComplex B ℤ) (n m : ℤ) (hnm : n + 1 = m) :
      (e K I n).hom ≫ (FA.obj (op ((U.mapHomologicalComplex (.up ℤ)).obj K),
          (U.mapHomologicalComplex (.up ℤ)).obj I)).d n m =
        U.map ((FB.obj (op K, I)).d n m) ≫ (e K I m).hom := by
    apply (limitA ((U.mapHomologicalComplex (.up ℤ)).obj K)
      ((U.mapHomologicalComplex (.up ℤ)).obj I) m).hom_ext
    intro ⟨p⟩
    change ((e K I n).hom ≫ _) ≫ πA _ _ m p (p + m) rfl =
      (U.map ((FB.obj (op K, I)).d n m) ≫ _) ≫ πA _ _ m p (p + m) rfl
    simp only [Category.assoc]
    rw [dA _ _ n m p (p + m) (p + n) (p + 1) hnm rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul]
    rw [← Category.assoc, ep, ← Category.assoc, ep]
    simp only [Category.assoc]
    rw [ep, ← U.map_comp_assoc,
      dB K I n m p (p + m) (p + n) (p + 1) hnm rfl rfl (by omega),
      U.map_sub, map_sign, Preadditive.sub_comp, Linear.units_smul_comp,
      U.map_comp, U.map_comp]
    dsimp only [Functor.mapHomologicalComplex]
    simp only [Category.assoc, comparison_post U HB HA h, comparison_pre U HB HA h]
  let ec (K I : CochainComplex B ℤ) :
      (U.mapHomologicalComplex (.up ℤ)).obj (FB.obj (op K, I)) ≅
        FA.obj (op ((U.mapHomologicalComplex (.up ℤ)).obj K),
          (U.mapHomologicalComplex (.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (e K I) (fun n m hnm ↦ comm K I n m hnm)
  have naturality (K K' I I' : CochainComplex B ℤ) (f : K' ⟶ K) (g : I ⟶ I') :
      (U.mapHomologicalComplex (.up ℤ)).map (FB.map (f.op, g)) ≫ (ec K' I').hom =
        (ec K I).hom ≫ FA.map
          (((U.mapHomologicalComplex (.up ℤ)).map f).op,
            (U.mapHomologicalComplex (.up ℤ)).map g) := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply (limitA ((U.mapHomologicalComplex (.up ℤ)).obj K')
      ((U.mapHomologicalComplex (.up ℤ)).obj I') n).hom_ext
    intro ⟨p⟩
    change (U.map ((FB.map (f.op, g)).f n) ≫ (e K' I' n).hom) ≫
        πA _ _ n p (p + n) rfl =
      ((e K I n).hom ≫ (FA.map _).f n) ≫ πA _ _ n p (p + n) rfl
    simp only [Category.assoc]
    rw [ep, ← U.map_comp_assoc, mB _ _ _ _ f g, U.map_comp, U.map_comp]
    rw [mA, ← Category.assoc, ← Category.assoc, ep]
    dsimp only [Functor.mapHomologicalComplex]
    simpa only [Category.assoc, U.map_comp] using
      congrArg (fun z ↦ U.map (πB K I n p (p + n) rfl) ≫ z)
        (comparison_naturality U HB HA h (f.f p) (g.f (p + n)))
  refine ⟨NatIso.ofComponents (fun P ↦ ec P.1.unop P.2)
    (fun f ↦ naturality _ _ _ _ f.1.unop f.2), ?_⟩
  intro K I n p q hpq
  exact ep K I n p q hpq

end CategoryTheory
