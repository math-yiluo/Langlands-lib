/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftGeneratorPresentation
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Corepresentability of closed Čech cochains
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An additive universal property for one degree of a cochain functor. -/
structure CochainDegreeCorepresenter
    {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type w} [Ring R] (H : C ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
    (n : ℕ) where
  object : C
  equiv : ∀ M : C, (object ⟶ M) ≃+ (H.obj M).X n
  natural : ∀ {M N : C} (f : M ⟶ N) (g : object ⟶ M),
    equiv N (g ≫ f) = (H.map f).f n (equiv M g)

private theorem presentation_corepresentable
    {C : Type*} {D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (Q T S : C) (e : T ⟶ Q) (d : S ⟶ kernel e)
    [Epi (F.map e)] [Epi (F.map d)]
    (hT : ∀ N, Function.Bijective (fun f : T ⟶ N ↦ F.map f))
    (hS : ∀ N, Function.Bijective (fun f : S ⟶ N ↦ F.map f)) :
    ∃ E : C, ∃ a : ∀ N : C, (E ⟶ N) ≃+ (F.obj Q ⟶ F.obj N),
      ∀ {N N' : C} (f : N ⟶ N') (g : E ⟶ N),
        a N' (g ≫ f) = a N g ≫ F.map f := by
  classical
  let r := d ≫ kernel.ι e
  let E := cokernel r
  let m (N : C) : (T ⟶ N) ≃+ (F.obj T ⟶ F.obj N) :=
    AddEquiv.ofBijective (F.mapAddHom : (T ⟶ N) →+ _) (hT N)
  have hz (N : C) (f : F.obj Q ⟶ F.obj N) :
      r ≫ (m N).symm (F.map e ≫ f) = 0 := by
    apply (hS N).injective
    simp only [F.map_comp, F.map_zero]
    dsimp only [r]
    rw [F.map_comp, Category.assoc]
    change F.map d ≫ (F.map (kernel.ι e) ≫
      m N ((m N).symm (F.map e ≫ f))) = 0
    rw [AddEquiv.apply_symm_apply,
      ← Category.assoc (F.map (kernel.ι e)), ← F.map_comp,
      kernel.condition, F.map_zero, zero_comp, comp_zero]
  let l (N : C) (f : F.obj Q ⟶ F.obj N) : E ⟶ N :=
    cokernel.desc r ((m N).symm (F.map e ≫ f)) (hz N f)
  have hl (N : C) (f : F.obj Q ⟶ F.obj N) :
      F.map (cokernel.π r) ≫ F.map (l N f) = F.map e ≫ f := by
    rw [← F.map_comp, cokernel.π_desc]
    exact (m N).apply_symm_apply _
  have hbij (N : C) : Function.Bijective (l N) := by
    constructor
    · intro f g h
      apply (cancel_epi (F.map e)).mp
      rw [← hl N f, ← hl N g, h]
    · intro g
      have hk : F.map (kernel.ι e) ≫ F.map (cokernel.π r ≫ g) = 0 := by
        apply (cancel_epi (F.map d)).mp
        simp only [comp_zero, ← F.map_comp, ← Category.assoc]
        rw [show d ≫ kernel.ι e = r from rfl, Category.assoc,
          cokernel.condition_assoc, zero_comp, F.map_zero]
      let hc := Abelian.isColimitMapCoconeOfCokernelCoforkOfπ e F
      let hc' := (CokernelCofork.ofπ e (kernel.condition e)).isColimitMapCoconeEquiv F hc
      let f : F.obj Q ⟶ F.obj N :=
        hc'.desc (CokernelCofork.ofπ (F.map (cokernel.π r ≫ g)) hk)
      have hf : F.map e ≫ f = F.map (cokernel.π r ≫ g) :=
        hc'.fac _ WalkingParallelPair.one
      refine ⟨f, ?_⟩
      apply (cancel_epi (cokernel.π r)).mp
      apply (hT N).injective
      change F.map (cokernel.π r ≫ l N f) = F.map (cokernel.π r ≫ g)
      rw [F.map_comp, hl, hf]
  let a (N : C) : (E ⟶ N) ≃+ (F.obj Q ⟶ F.obj N) :=
    (AddEquiv.ofBijective
      ({ toFun := l N
         map_zero' := by
           apply (cancel_epi (cokernel.π r)).mp
           simp [l]
         map_add' := by
           intro f g
           apply (cancel_epi (cokernel.π r)).mp
           simp [l, Preadditive.comp_add] } : _ →+ _) (hbij N)).symm
  have ha (N : C) (g : E ⟶ N) :
      F.map e ≫ a N g = F.map (cokernel.π r ≫ g) := by
    calc
      _ = F.map (cokernel.π r) ≫ F.map (l N (a N g)) := (hl N (a N g)).symm
      _ = F.map (cokernel.π r) ≫ F.map g := by
        rw [show l N (a N g) = g from (a N).symm_apply_apply g]
      _ = _ := (F.map_comp _ _).symm
  refine ⟨E, a, ?_⟩
  intro N N' f g
  apply (cancel_epi (F.map e)).mp
  calc
    _ = F.map (cokernel.π r ≫ (g ≫ f)) := ha N' (g ≫ f)
    _ = F.map (cokernel.π r ≫ g) ≫ F.map f := by
      rw [← Category.assoc, F.map_comp]
    _ = (F.map e ≫ a N g) ≫ F.map f := by rw [ha]
    _ = _ := Category.assoc _ _ _

end CategoryTheory

namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The actual fixed-coefficient closed push-pull, followed by localization and
Čech sections. This construction uses the functors in the assigned statement. -/
noncomputable def closedCechCoefficientFunctor
    (A : Type u) [CommRing A] {B O : Scheme.{u}} (b : O ⟶ B) [IsOpenImmersion b]
    (P : B.ProEt) (V : P.left.ProEt) {n : ℕ} (U : Fin n → Over V) :
    Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℕ :=
  ProEtale.upperStar _ b.closedComplement ⋙ ProEtale.lowerStar _ b.closedComplement ⋙
    ProEtale.upperStar _ P.hom ⋙ sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op ⋙ cechComplexFunctor U

private theorem freeSheafHomEquiv_add
    (A : Type u) [CommRing A] {B : Scheme.{u}} (W : B.ProEt)
    (M : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (f g : (ProEtale.freeSheaf (ULift.{u + 1, u} A) B).obj W ⟶ M) :
    ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M (f + g) =
      ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M f +
        ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M g := by
  let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) B).obj W
  let x := ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W Q (𝟙 Q)
  have hx (t : Q ⟶ M) :
      ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M t = t.hom.app (op W) x := by
    exact (congrArg (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M)
      (Category.id_comp t)).symm.trans
        (ProEtale.freeSheafHomEquiv_comp (ULift.{u + 1, u} A) W (𝟙 Q) t)
  rw [hx, hx, hx]
  rfl

private theorem closedSection_corepresentable
    (A : Type u) [CommRing A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (W : P.left.ProEt) :
    let F := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        b.closedComplement ⋙ ProEtale.lowerStar _ b.closedComplement ⋙
      ProEtale.upperStar _ P.hom
    ∃ E : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)),
      ∃ a : ∀ M, (E ⟶ M) ≃+ (F.obj M).obj.obj (op W),
        ∀ {M N} (f : M ⟶ N) (g : E ⟶ M),
          a N (g ≫ f) = (F.map f).hom.app (op W) (a M g) := by
  classical
  dsimp only
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let L := ProEtale.upperStar Λ b.closedComplement
  let R := ProEtale.lowerStar Λ b.closedComplement
  let J := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ P.prop
  let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) B).obj (J.obj W)
  let e := closedLiftGeneratorAugmentation A b.closedComplement Q
  let d := closedLiftGeneratorAugmentation A b.closedComplement (kernel e.hom)
  have hpair : Set.range b = (Set.range b.closedComplement)ᶜ := by
    rw [Scheme.Hom.range_closedComplement, compl_compl]
  have he := closedLiftGeneratorPresentation A b.closedComplement b hpair Q
  have hd := closedLiftGeneratorPresentation A b.closedComplement b hpair (kernel e.hom)
  have : Epi (L.map e.hom) := he.1
  have : Epi (L.map d.hom) := hd.1
  obtain ⟨E, a, ha⟩ := presentation_corepresentable L Q e.left d.left e.hom d.hom he.2 hd.2
  let adj := ProEtale.upperStarLowerStarAdjunction Λ b.closedComplement
  let ev (M : Sheaf (ProEt.topology B) Λ) :
      (Q ⟶ R.obj (L.obj M)) ≃+ (R.obj (L.obj M)).obj.obj (op (J.obj W)) :=
    { ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) (J.obj W) (R.obj (L.obj M)) with
      map_add' := freeSheafHomEquiv_add A (J.obj W) _ }
  let iso := ProEtale.upperStarIsoLocalizationRestriction Λ P.hom P.prop
  let loc (M : Sheaf (ProEt.topology B) Λ) :=
    (((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ Λ).obj (op W)).mapIso
      (iso.app (R.obj (L.obj M)))).toLinearEquiv.toAddEquiv)
  refine ⟨E, fun M ↦ ((a M).trans ((adj.homAddEquiv Q (L.obj M)).trans
    (ev M))).trans (loc M).symm, ?_⟩
  intro M N f g
  let x := ev M (adj.homEquiv Q (L.obj M) (a M g))
  have hx : ev N (adj.homEquiv Q (L.obj N) (a N (g ≫ f))) =
      (R.map (L.map f)).hom.app (op (J.obj W)) x := by
    calc
      _ = ev N (adj.homEquiv Q (L.obj N) (a M g ≫ L.map f)) :=
        congrArg (fun t ↦ ev N (adj.homEquiv Q (L.obj N) t)) (ha f g)
      _ = ev N (adj.homEquiv Q (L.obj M) (a M g) ≫ R.map (L.map f)) :=
        congrArg (ev N) (adj.homEquiv_naturality_right (a M g) (L.map f))
      _ = _ := ProEtale.freeSheafHomEquiv_comp (ULift.{u + 1, u} A) (J.obj W)
        (adj.homEquiv Q (L.obj M) (a M g)) (R.map (L.map f))
  have hn := congrArg (fun t ↦ t.hom.app (op W)) (iso.hom.naturality (R.map (L.map f)))
  have hnat (t) :
      (loc N) (((ProEtale.upperStar Λ P.hom).map (R.map (L.map f))).hom.app (op W) t) =
        (R.map (L.map f)).hom.app (op (J.obj W)) ((loc M) t) :=
    ConcreteCategory.congr_hom hn t
  have hnx := (hnat ((loc M).symm x)).trans
    (congrArg ((R.map (L.map f)).hom.app (op (J.obj W))) ((loc M).apply_symm_apply x))
  apply (loc N).injective
  exact ((loc N).apply_symm_apply _).trans (hx.trans hnx.symm)

/-- Each degree of the closed Čech coefficient functor is corepresentable in
ambient fixed-coefficient module sheaves. -/
theorem exists_closedCech_degreeCorepresenter
    (A : Type u) [CommRing A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) {n : ℕ} (U : Fin n → Over V) (k : ℕ) :
    Nonempty (CochainDegreeCorepresenter (closedCechCoefficientFunctor A b P V U) k) := by
  classical
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let F := ProEtale.upperStar Λ b.closedComplement ⋙ ProEtale.lowerStar Λ b.closedComplement ⋙
    ProEtale.upperStar Λ P.hom
  let T (y : Fin (k + 1) → Fin n) : P.left.ProEt := (Presheaf.cechNerveObj U y).left
  choose E a ha using fun y ↦ closedSection_corepresentable A b P (T y)
  let Z (M : Sheaf (ProEt.topology B) Λ) (y : Fin (k + 1) → Fin n) :=
    (F.obj M).obj.obj (op (T y))
  let S := ∐ E
  let eqv (M : Sheaf (ProEt.topology B) Λ) :
      (S ⟶ M) ≃+ (∀ y, Z M y) :=
    { toFun := fun f y ↦ a y M (Sigma.ι E y ≫ f)
      invFun := fun s ↦ Sigma.desc (fun y ↦ (a y M).symm (s y))
      left_inv := by
        intro f
        apply Sigma.hom_ext
        intro y
        simp only [Sigma.ι_comp_desc, AddEquiv.symm_apply_apply]
      right_inv := by
        intro s
        funext y
        dsimp only
        rw [Sigma.ι_comp_desc, AddEquiv.apply_symm_apply]
      map_add' := by
        intro f g
        funext y
        change a y M (Sigma.ι E y ≫ (f + g)) =
          a y M (Sigma.ι E y ≫ f) + a y M (Sigma.ι E y ≫ g)
        rw [Preadditive.comp_add, map_add] }
  let prod (M : Sheaf (ProEt.topology B) Λ) :=
    (ModuleCat.piIsoPi (Z M)).toLinearEquiv.toAddEquiv
  refine ⟨{
    object := S
    equiv := fun M ↦ (eqv M).trans (prod M).symm
    natural := ?_ }⟩
  intro M N f g
  apply (prod N).injective
  funext y
  have hp (c) : (prod N c) y = Pi.π (Z N) y c :=
    ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype (Z N) y) c
  let z := (prod M).symm (eqv M g)
  have hM : Pi.π (Z M) y z = (eqv M g) y :=
    (ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype (Z M) y) z).symm.trans
        (congrFun ((prod M).apply_symm_apply (eqv M g)) y)
  have hmap := ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun y ↦ (F.map f).hom.app (op (T y))) y) z
  have hc : (eqv N (g ≫ f)) y = (F.map f).hom.app (op (T y)) ((eqv M g) y) :=
    (congrArg (a y N) (Category.assoc (Sigma.ι E y) g f).symm).trans
      (ha y f (Sigma.ι E y ≫ g))
  calc
    _ = (eqv N (g ≫ f)) y :=
      congrFun ((prod N).apply_symm_apply (eqv N (g ≫ f))) y
    _ = (F.map f).hom.app (op (T y)) ((eqv M g) y) := hc
    _ = (F.map f).hom.app (op (T y)) (Pi.π (Z M) y z) :=
      congrArg ((F.map f).hom.app (op (T y))) hM.symm
    _ = Pi.π (Z N) y
        ((Limits.Pi.map (fun y ↦ (F.map f).hom.app (op (T y)))) z) := hmap.symm
    _ = _ := (hp _).symm

end AlgebraicGeometry.Scheme
