/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.NormalizedTensorHomCochains
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The pure-tensor component calculation for ordinary cochains

Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochain-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry

attribute [local irreducible] SheafOfModules.tensorHomEquiv homTensorCurrySectionMap
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  homComplex homTensorDegreewiseMap normalizedHomGlobalCochains
  normalizedHomFactorEquiv normalizedHomProjection homTensorCurryProjection

section TensorHelpers

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} 𝓡

-- Keep the sheafification and tensor comparison types explicit during elaboration.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_braiding_comparison (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (β_ A B).hom ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) B A).hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map
          (β_ A.val B.val).hom := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.sheafificationMonoidal R
  let := SheafOfModules.sheafificationBraided R
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc]
  congr 1
  exact (Functor.LaxBraided.braided
    (F := PresheafOfModules.sheafification (𝟙 (𝓡).obj))
    A.val B.val).symm

-- Keep the sheafification and tensor comparison types explicit during elaboration.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_section_braiding (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    homTensorSectionMap R A B ≫ (β_ A B).hom.val =
      (β_ A.val B.val).hom ≫ homTensorSectionMap R B A := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have hb := tensor_braiding_comparison R A B
  have hb' : (β_ A B).hom ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) B A).hom ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R) B A).inv =
      (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map
          (β_ A.val B.val).hom ≫
            (SheafOfModules.tensorObjIsoSheafification (R := R) B A).inv :=
    congrArg (fun f ↦ f ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) B A).inv) hb
  simp only [Iso.hom_inv_id, Category.comp_id] at hb'
  have hb'' : (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv ≫ (β_ A B).hom =
      (PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map
        (β_ A.val B.val).hom ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) B A).inv := by
    erw [hb', Iso.inv_hom_id_assoc]
  have hv := congrArg SheafOfModules.Hom.val hb''
  change (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val ≫
      (β_ A B).hom.val =
    ((PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map
      (β_ A.val B.val).hom).val ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) B A).inv.val at hv
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)
  have hn := adj.unit.naturality (β_ A.val B.val).hom
  change (β_ A.val B.val).hom ≫ adj.unit.app (B.val ⊗ A.val) =
    adj.unit.app (A.val ⊗ B.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map
        (β_ A.val B.val).hom).val at hn
  unfold homTensorSectionMap homTensorCurrySectionMap
  erw [Category.assoc, hv, ← Category.assoc, ← hn]
  rfl

-- Keep the sheafification and tensor comparison types explicit during elaboration.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_section_uncurry (A B D : Mod)
    (f : B ⟶ SheafOfModules.homObj (R := R) A D) :
    letI := SheafOfModules.monoidalCategory R
    homTensorSectionMap R A B ≫
        ((SheafOfModules.tensorHomEquiv (R := R) A B D).symm f).val =
      (PresheafOfModules.homObjEquiv (R := R.obj) A.val B.val D.val).symm f.val := by
  let := SheafOfModules.monoidalCategory R
  let e := SheafOfModules.tensorHomEquiv (R := R) A B D
  let e' := PresheafOfModules.homObjEquiv (R := R.obj) A.val B.val D.val
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)
  have he := congrArg SheafOfModules.Hom.val (e.apply_symm_apply f)
  rw [SheafOfModules.tensorHomEquiv_val] at he
  change e' (adj.homEquiv _ D
    ((SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv ≫ e.symm f)) = f.val at he
  have he' := e'.eq_symm_apply.mpr he
  rw [Adjunction.homEquiv_unit] at he'
  change _ ≫ ((SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv ≫ e.symm f).val =
    e'.symm f.val at he'
  rw [SheafOfModules.comp_val] at he'
  unfold homTensorSectionMap homTensorCurrySectionMap
  change (_ ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val) ≫
    (e.symm f).val = e'.symm f.val
  exact (Category.assoc _ _ _).trans he'

-- Keep the sheafification and tensor comparison types explicit during elaboration.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_section_braiding_uncurry (A B D : Mod)
    (f : A ⟶ SheafOfModules.homObj (R := R) B D) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    homTensorSectionMap R A B ≫
        ((β_ A B).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) B A D).symm f).val =
      (β_ A.val B.val).hom ≫
        (PresheafOfModules.homObjEquiv (R := R.obj) B.val A.val D.val).symm f.val := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  rw [SheafOfModules.comp_val, ← Category.assoc (homTensorSectionMap R A B),
    tensor_section_braiding R A B, Category.assoc, tensor_section_uncurry R B A D f]

-- Keep the sheafification and tensor comparison types explicit during elaboration.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_section_ext (A B D : Mod) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (f g : A ⊗ B ⟶ D),
      homTensorSectionMap R A B ≫ f.val = homTensorSectionMap R A B ≫ g.val → f = g := by
  let := SheafOfModules.monoidalCategory R
  intro f g h
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)).homEquiv _ D).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change _ ≫ ((SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv ≫ f).val =
    _ ≫ ((SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv ≫ g).val
  unfold homTensorSectionMap homTensorCurrySectionMap at h
  rw [SheafOfModules.comp_val, SheafOfModules.comp_val]
  exact ((Category.assoc _ _ f.val).symm.trans h).trans (Category.assoc _ _ g.val)

-- Identify the two APIs before specializing the complex arguments.
set_option backward.isDefEq.respectTransparency true in
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
private theorem normalized_projection_eq (A B : CochainComplex Mod ℤ)
    (d p q : ℤ) (h : p + d = q) :
    normalizedHomProjection (R := R) A B d p q h =
      homTensorCurryProjection R A B d p q h := by
  with_unfolding_all exact Eq.refl (homTensorCurryProjection R A B d p q h)

-- Expose section evaluation with abstract module arguments, without reducing complexes.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
private theorem normalized_factor_app (A B : Mod)
    (s : SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) A B)
    (U : Cᵒᵖ) (x : A.val.obj U) :
    ((normalizedHomFactorEquiv A B s).val.app U).hom x =
      (((s.val.app U).hom (1 : R.obj.obj U)).app (op (Over.mk (𝟙 U.unop)))).hom x := by
  with_unfolding_all rfl

set_option backward.isDefEq.respectTransparency true in
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
private theorem presheaf_uncurry_braiding_app (A B D : Mod)
    (f : A ⟶ SheafOfModules.homObj (R := R) B D)
    (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (((β_ A.val B.val).hom ≫
      (PresheafOfModules.homObjEquiv (R := R.obj) B.val A.val D.val).symm f.val).app U).hom
        (x ⊗ₜ[R.obj.obj U] y) =
      (((f.val.app U).hom x).app (op (Over.mk (𝟙 U.unop)))).hom y := by
  rfl

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem curry_condition_reindex (K L M : CochainComplex Mod ℤ) (d : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a : (homComplex (R := R) K (homComplex (R := R) L M)).X d ⟶
      (homComplex (R := R) (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X d),
      HomTensorCurryCondition R K L M d a →
      ∀ (p q j k : ℤ) (hj : p + d = j) (hk : p + q + d = k)
        (hk' : q + j = k) (U : Cᵒᵖ)
        (s : (homComplex (R := R) K (homComplex (R := R) L M)).X d |>.val.obj U)
        (x : (K.X p).val.obj U) (y : (L.X q).val.obj U),
        let φ := ((homTensorCurryProjection R
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
          d (p + q) k hk).val.app U).hom ((a.val.app U).hom s)
        let ψ := ((homTensorCurryProjection R K (homComplex (R := R) L M)
          d p j hj).val.app U).hom s
        let χ := ((homTensorCurryProjection R L M j q k hk').val.app U).hom
          ((ψ.app (op (Over.mk (𝟙 U.unop)))).hom x)
        (φ.app (op (Over.mk (𝟙 U.unop)))).hom
          (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
            p q (p + q) rfl).val.app U).hom
            (((homTensorCurrySectionMap R (K.X p) (L.X q)).app U).hom
              (x ⊗ₜ[R.obj.obj U] y))) =
          (χ.app (op (Over.mk (𝟙 U.unop)))).hom y := by
  let := SheafOfModules.monoidalCategory R
  intro a ha p q j k hj hk hk' U s x y
  subst j
  subst k
  exact ha p q U s (op (Over.mk (𝟙 U.unop))) x y

-- Work over an abstract ring sheaf before specializing the global comparison.
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_hom_global_component (K L M : CochainComplex Mod ℤ) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    let H := homComplex (R := R) L M
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    ∀ (a : (homComplex (R := R) K H).X 0 ⟶ (homComplex (R := R) T M).X 0),
      HomTensorCurryCondition R K L M 0 a →
      ∀ (c : Cochain K H 0) (p r : ℤ) (h' : r + p = p + r),
        CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p r (p + r) rfl ≫
          (normalizedHomGlobalCochains R T M 0
            ((normalizedHomGlobalCochains R K H 0).symm c ≫ a)).v
              (p + r) (p + r) (add_zero (p + r)) =
        (β_ (K.X p) (L.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := R) (L.X r) (K.X p) (M.X (p + r))).symm
            (c.v p p (add_zero p) ≫ homTensorProjection R L M p r (p + r) h') := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let H := homComplex (R := R) L M
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  dsimp only
  intro a ha c p r h'
  obtain ⟨s, rfl⟩ := (normalizedHomGlobalCochains R K H 0).surjective c
  rw [AddEquiv.symm_apply_apply, normalizedHomGlobalCochains_v,
    normalizedHomGlobalCochains_v]
  apply tensor_section_ext R (K.X p) (L.X r) (M.X (p + r))
  rw [tensor_section_braiding_uncurry R]
  simp only [normalized_projection_eq R]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  erw [presheaf_uncurry_braiding_app R]
  change ((normalizedHomFactorEquiv (T.X (p + r)) (M.X (p + r))
      (s ≫ a ≫
        homTensorCurryProjection R T M 0 (p + r) (p + r) (add_zero (p + r)))).val.app U).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p r (p + r) rfl).val.app U).hom
          (((homTensorCurrySectionMap R (K.X p) (L.X r)).app U).hom
            (x ⊗ₜ[R.obj.obj U] y))) = _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply, normalized_factor_app R]
  exact curry_condition_reindex R K L M 0 a ha p r p (p + r)
    (add_zero p) (add_zero (p + r)) h' U
    ((s.val.app U).hom (1 : R.obj.obj U)) x y

end TensorHelpers

-- The normalized Hom and tensor types require additional elaboration fuel.
set_option backward.isDefEq.respectTransparency true in
/-- Restricting the explicitly constructed degree-zero uncurrying comparison
 to a tensor summand gives the inverse sheaf tensor-Hom adjunction.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochain-components).

Proof: put s equal to the inverse normalized global comparison applied to c.
The global comparison component formula identifies c's p-component with the
morphism corresponding to s followed by the lemma-identity-component projection. On the
output side, the same formula identifies the displayed component with the
morphism corresponding to s followed by homTensorDegreewiseMap and the
n-product projection. Apply homTensorDegreewiseMap_spec. Its localized
pure-tensor equation says that this latter morphism, restricted to the
(p,r) summand, evaluates x tensor y as c's p-component at x, projected onto
the r-factor, evaluated at y. Expanding tensorHomEquiv through the presheaf
adjunction and sheafification gives this very evaluation for the right side:
the symmetry interchanges x and y and the inverse adjunction evaluates at y.
Naturality under restriction gives equality on every localized site, not
only on global pure tensors. Linear maps from the presheaf tensor are
determined by pure tensors; the sheafification adjunction determines maps
from the sheaf tensor by their presheaf pullbacks. Thus the sheaf morphisms
are equal. Only the degreewise pure-tensor specification and the explicit
global projection formula are used, with no differential, cocycle, or
homotopy assertion. Zero factors give zero morphisms; there is no finiteness
assumption because only a single coproduct summand is tested. -/
theorem normalizedTensorHomCochains_component (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : Cochain P (homComplex (R := X.sheaf) L I) 0)
    (p r n : ℤ) (h : p + r = n) (h' : r + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
        (normalizedTensorHomCochains X P L I 0 c).v n n (add_zero n) =
      (β_ (P.X p) (L.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
          (c.v p p (add_zero p) ≫ homTensorProjection X.sheaf L I p r n h') := by
  let R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} := X.sheaf
  let 𝓡 := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let Mod := SheafOfModules.{u} 𝓡
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  subst n
  let H := homComplex (R := R) L I
  let T := CochainComplex.mapBifunctor P L (curriedTensor Mod)
  change HomologicalComplex.ιMapBifunctor P L (curriedTensor Mod) (.up ℤ)
    p r (p + r) rfl ≫
      (normalizedHomGlobalCochains R T I 0
        ((normalizedHomGlobalCochains R P H 0).symm c ≫ homTensorDegreewiseMap R P L I 0)).v
          (p + r) (p + r) (add_zero (p + r)) = _
  exact tensor_hom_global_component R P L I (homTensorDegreewiseMap R P L I 0)
    (homTensorDegreewiseMap_spec R P L I 0).1 c p r h'

end AlgebraicGeometry
