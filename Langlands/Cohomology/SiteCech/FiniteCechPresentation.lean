import Langlands.Cohomology.SiteCech.FiniteCoverCechSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Finite representable presentations of Čech nerves -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w a

variable {C : Type u} [Category.{v} C]

/-- Sections of a coproduct of set-valued presheaves retain their summand. -/
def coproductSectionsEquiv {I : Type} (P : I → Cᵒᵖ ⥤ Type w) (Z : Cᵒᵖ) :
    (∐ P).obj Z ≃ Σ i, (P i).obj Z :=
  (sigmaObjIso P Z ≪≫ Types.coproductIso (fun i => (P i).obj Z)).toEquiv

@[simp]
theorem coproductSectionsEquiv_ι {I : Type} (P : I → Cᵒᵖ ⥤ Type w)
    (Z : Cᵒᵖ) (i : I) (x : (P i).obj Z) :
    coproductSectionsEquiv P Z ((Sigma.ι P i).app Z x) = ⟨i, x⟩ := by
  change (((Sigma.ι P i).app Z ≫ (sigmaObjIso P Z).hom) ≫
    (Types.coproductIso (fun i => (P i).obj Z)).hom) x = _
  rw [ι_comp_sigmaObjIso_hom, Types.coproductIso_ι_comp_hom]
  rfl

/-- Recover a section from its coproduct summand. -/
theorem coproductSectionsEquiv_symm {I : Type} (P : I → Cᵒᵖ ⥤ Type w)
    (Z : Cᵒᵖ) (i : I) (x : (P i).obj Z) :
    (coproductSectionsEquiv P Z).symm ⟨i, x⟩ = (Sigma.ι P i).app Z x := by
  apply (coproductSectionsEquiv P Z).injective
  simp

/-- Two sections of a presheaf wide pullback agree when all their projections agree. -/
theorem presheafWidePullback_sections_ext {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    {k : ℕ} {Z : Cᵒᵖ}
    (x y : (widePullback Q (fun _ : Fin k => P) (fun _ => f)).obj Z)
    (hπ : ∀ j, (WidePullback.π (fun _ : Fin k => f) j).app Z x =
      (WidePullback.π (fun _ : Fin k => f) j).app Z y)
    (hb : (WidePullback.base (fun _ : Fin k => f)).app Z x =
      (WidePullback.base (fun _ : Fin k => f)).app Z y) : x = y := by
  apply (Types.isLimitEquivSections
    (isLimitOfPreserves ((evaluation Cᵒᵖ (Type w)).obj Z)
      (limit.isLimit (WidePullbackShape.wideCospan Q
        (fun _ : Fin k => P) (fun _ => f))))).injective
  apply Subtype.ext
  funext j
  cases j with
  | none => exact hb
  | some j => exact hπ j

variable [LocallySmall.{w} C]

/-- The coproduct of representables associated with a finite family over `U`. -/
def representableCoproductArrow {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U) : Arrow (Cᵒᵖ ⥤ Type w) :=
  Arrow.mk (Sigma.desc (fun i => shrinkYoneda.{w}.map (f i)))

/-- A tuplewise geometric cone maps canonically into the presheaf wide pullback. -/
def coproductWidePullbackMap {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j))) :
    (∐ fun α => shrinkYoneda.{w}.obj (c α).pt) ⟶
      widePullback (representableCoproductArrow.{u, v, w} f).right
        (fun _ : Fin k => (representableCoproductArrow.{u, v, w} f).left)
        (fun _ => (representableCoproductArrow.{u, v, w} f).hom) :=
  Sigma.desc fun α => WidePullback.lift (shrinkYoneda.{w}.map (c α).base)
    (fun j => shrinkYoneda.{w}.map ((c α).π j) ≫
      Sigma.ι (fun i => shrinkYoneda.{w}.obj (V i)) (α j)) (by
        intro j
        simp only [representableCoproductArrow, Arrow.mk_hom,
          Category.assoc, Sigma.ι_comp_desc, ← Functor.map_comp,
          WidePullbackCone.condition])

@[reassoc (attr := simp)]
theorem coproductWidePullbackMap_ι_π {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j)))
    (α : Fin k → Fin m) (j : Fin k) :
    Sigma.ι (fun α => shrinkYoneda.{w}.obj (c α).pt) α ≫
      coproductWidePullbackMap f c ≫ WidePullback.π _ j =
        shrinkYoneda.{w}.map ((c α).π j) ≫
          Sigma.ι (fun i => shrinkYoneda.{w}.obj (V i)) (α j) := by
  dsimp only [coproductWidePullbackMap]
  rw [Sigma.ι_comp_desc_assoc]
  exact WidePullback.lift_π _ _ _ _ j

@[reassoc (attr := simp)]
theorem coproductWidePullbackMap_ι_base {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j)))
    (α : Fin k → Fin m) :
    Sigma.ι (fun α => shrinkYoneda.{w}.obj (c α).pt) α ≫
      coproductWidePullbackMap f c ≫ WidePullback.base _ =
        shrinkYoneda.{w}.map (c α).base := by
  dsimp only [coproductWidePullbackMap]
  rw [Sigma.ι_comp_desc_assoc]
  exact WidePullback.lift_base _ _ _ _

/-- Every presheaf wide-pullback section is represented by its unique tuple of summands. -/
theorem coproductWidePullbackMap_surjective {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) (Z : Cᵒᵖ) :
    Function.Surjective ((coproductWidePullbackMap.{u, v, w} f c).app Z) := by
  intro x
  let A := representableCoproductArrow.{u, v, w} f
  let P := fun i => shrinkYoneda.{w}.obj (V i)
  let T := fun α => shrinkYoneda.{w}.obj (c α).pt
  let d : ∀ j : Fin k, Σ i, (P i).obj Z := fun j =>
    coproductSectionsEquiv P Z ((WidePullback.π (fun _ : Fin k => A.hom) j).app Z x)
  let α : Fin k → Fin m := fun j => (d j).1
  let g : ∀ j, Z.unop ⟶ V (α j) := fun j => shrinkYonedaObjObjEquiv (d j).2
  let b : Z.unop ⟶ U :=
    shrinkYonedaObjObjEquiv ((WidePullback.base (fun _ : Fin k => A.hom)).app Z x)
  have hd (j : Fin k) :
      (Sigma.ι P (α j)).app Z (d j).2 =
        (WidePullback.π (fun _ : Fin k => A.hom) j).app Z x := by
    rw [← coproductSectionsEquiv_symm]
    exact (coproductSectionsEquiv P Z).symm_apply_apply _
  have hw (j : Fin k) : g j ≫ f (α j) = b := by
    have h : (shrinkYoneda.{w}.map (f (α j))).app Z (d j).2 =
        (WidePullback.base (fun _ : Fin k => A.hom)).app Z x := by
      calc
        _ = A.hom.app Z ((Sigma.ι P (α j)).app Z (d j).2) := by
          change _ = ((Sigma.ι P (α j) ≫ A.hom).app Z (d j).2)
          simp only [A, representableCoproductArrow, Arrow.mk_hom, Sigma.ι_comp_desc]
          rfl
        _ = A.hom.app Z ((WidePullback.π (fun _ : Fin k => A.hom) j).app Z x) :=
          congrArg (fun y => A.hom.app Z y) (hd j)
        _ = _ := congrArg (fun t => t.app Z x)
          (WidePullback.π_arrow (fun _ : Fin k => A.hom) j)
    dsimp only [g, b]
    rw [← shrinkYonedaObjObjEquiv_map_app]
    exact congrArg shrinkYonedaObjObjEquiv h
  let l := WidePullbackCone.IsLimit.lift (hc α) b g hw
  refine ⟨(Sigma.ι T α).app Z (shrinkYonedaObjObjEquiv.symm l), ?_⟩
  apply presheafWidePullback_sections_ext A.hom
  · intro j
    change ((Sigma.ι T α ≫ coproductWidePullbackMap f c ≫
      WidePullback.π (fun _ : Fin k => A.hom) j).app Z
        (shrinkYonedaObjObjEquiv.symm l)) = _
    rw [coproductWidePullbackMap_ι_π]
    change (Sigma.ι P (α j)).app Z
      ((shrinkYoneda.{w}.map ((c α).π j)).app Z
        (shrinkYonedaObjObjEquiv.symm l)) = _
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
    dsimp only [l]
    rw [WidePullbackCone.IsLimit.lift_π]
    simpa only [g, Equiv.symm_apply_apply] using hd j
  · change ((Sigma.ι T α ≫ coproductWidePullbackMap f c ≫
      WidePullback.base (fun _ : Fin k => A.hom)).app Z
        (shrinkYonedaObjObjEquiv.symm l)) = _
    rw [coproductWidePullbackMap_ι_base]
    exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm l (c α).base).trans
      ((congrArg shrinkYonedaObjObjEquiv.symm
        (WidePullbackCone.IsLimit.lift_base (hc α) b g hw)).trans
          (Equiv.symm_apply_apply _ _))

/-- A limiting tuple cone is determined by all the canonical projections. -/
theorem coproductWidePullbackMap_injective {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) (Z : Cᵒᵖ) :
    Function.Injective ((coproductWidePullbackMap.{u, v, w} f c).app Z) := by
  intro x y h
  let A := representableCoproductArrow.{u, v, w} f
  let P := fun i => shrinkYoneda.{w}.obj (V i)
  let T := fun α => shrinkYoneda.{w}.obj (c α).pt
  obtain ⟨⟨α, a⟩, hx⟩ := (coproductSectionsEquiv T Z).symm.surjective x
  obtain ⟨⟨β, b⟩, hy⟩ := (coproductSectionsEquiv T Z).symm.surjective y
  rw [coproductSectionsEquiv_symm] at hx hy
  subst x
  subst y
  have hp (j : Fin k) :
      (Sigma.ι P (α j)).app Z ((shrinkYoneda.map ((c α).π j)).app Z a) =
        (Sigma.ι P (β j)).app Z ((shrinkYoneda.map ((c β).π j)).app Z b) := by
    have hj := congrArg (fun t =>
      (WidePullback.π (fun _ : Fin k => A.hom) j).app Z t) h
    change ((Sigma.ι T α ≫ coproductWidePullbackMap f c ≫
      WidePullback.π (fun _ : Fin k => A.hom) j).app Z a) =
        ((Sigma.ι T β ≫ coproductWidePullbackMap f c ≫
          WidePullback.π (fun _ : Fin k => A.hom) j).app Z b) at hj
    rw [coproductWidePullbackMap_ι_π, coproductWidePullbackMap_ι_π] at hj
    exact hj
  have ht : α = β := by
    funext j
    have hj := congrArg (fun t => (coproductSectionsEquiv P Z t).1) (hp j)
    simpa only [coproductSectionsEquiv_ι] using hj
  subst β
  have hb :
      (shrinkYoneda.map (c α).base).app Z a =
        (shrinkYoneda.map (c α).base).app Z b := by
    have hj := congrArg (fun t =>
      (WidePullback.base (fun _ : Fin k => A.hom)).app Z t) h
    change ((Sigma.ι T α ≫ coproductWidePullbackMap f c ≫
      WidePullback.base (fun _ : Fin k => A.hom)).app Z a) =
        ((Sigma.ι T α ≫ coproductWidePullbackMap f c ≫
          WidePullback.base (fun _ : Fin k => A.hom)).app Z b) at hj
    rw [coproductWidePullbackMap_ι_base] at hj
    exact hj
  have hab : shrinkYonedaObjObjEquiv a = shrinkYonedaObjObjEquiv b := by
    apply WidePullbackCone.IsLimit.hom_ext (hc α)
    · exact (shrinkYonedaObjObjEquiv_map_app a (c α).base).symm.trans
        ((congrArg shrinkYonedaObjObjEquiv hb).trans
          (shrinkYonedaObjObjEquiv_map_app b (c α).base))
    · intro j
      have hj := congrArg (coproductSectionsEquiv P Z) (hp j)
      simp only [coproductSectionsEquiv_ι] at hj
      have hv := eq_of_heq (Sigma.mk.inj hj).2
      exact (shrinkYonedaObjObjEquiv_map_app a ((c α).π j)).symm.trans
        ((congrArg shrinkYonedaObjObjEquiv hv).trans
          (shrinkYonedaObjObjEquiv_map_app b ((c α).π j)))
  exact congrArg ((Sigma.ι T α).app Z) (shrinkYonedaObjObjEquiv.injective hab)

/-- Tuplewise limiting geometric cones give the actual presheaf wide pullback. -/
def coproductWidePullbackIso {m k : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ α : Fin k → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) :
    (∐ fun α => shrinkYoneda.{w}.obj (c α).pt) ≅
      widePullback (representableCoproductArrow.{u, v, w} f).right
        (fun _ : Fin k => (representableCoproductArrow.{u, v, w} f).left)
        (fun _ => (representableCoproductArrow.{u, v, w} f).hom) := by
  haveI : IsIso (coproductWidePullbackMap.{u, v, w} f c) :=
    (NatTrans.isIso_iff_isIso_app _).mpr fun Z =>
      (isIso_iff_bijective _).mpr
        ⟨coproductWidePullbackMap_injective f c hc Z,
          coproductWidePullbackMap_surjective f c hc Z⟩
  exact asIso (coproductWidePullbackMap f c)

/-- The tuple-indexed representable decomposition of an actual Čech nerve term. -/
def representableCoproductCechIso {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U) (n : ℕ)
    (c : ∀ α : Fin (n + 1) → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) :
    (representableCoproductArrow.{u, v, w} f).cechNerve.obj (op ⦋n⦌) ≅
      ∐ (fun α => shrinkYoneda.{w}.obj (c α).pt) :=
  (coproductWidePullbackIso f c hc).symm

@[reassoc (attr := simp)]
theorem representableCoproductCechIso_ι_inv_π {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U) (n : ℕ)
    (c : ∀ α : Fin (n + 1) → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) (α : Fin (n + 1) → Fin m) (j : Fin (n + 1)) :
    Sigma.ι (fun α => shrinkYoneda.{w}.obj (c α).pt) α ≫
      (representableCoproductCechIso f n c hc).inv ≫ WidePullback.π _ j =
        shrinkYoneda.{w}.map ((c α).π j) ≫
          Sigma.ι (fun i => shrinkYoneda.{w}.obj (V i)) (α j) :=
  coproductWidePullbackMap_ι_π f c α j

@[reassoc (attr := simp)]
theorem representableCoproductCechIso_ι_inv_base {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U) (n : ℕ)
    (c : ∀ α : Fin (n + 1) → Fin m, WidePullbackCone (fun j => f (α j)))
    (hc : ∀ α, IsLimit (c α)) (α : Fin (n + 1) → Fin m) :
    Sigma.ι (fun α => shrinkYoneda.{w}.obj (c α).pt) α ≫
      (representableCoproductCechIso f n c hc).inv ≫ WidePullback.base _ =
        shrinkYoneda.{w}.map (c α).base :=
  coproductWidePullbackMap_ι_base f c α

variable (J : GrothendieckTopology C) {ι : Type a} (B : ι → C)

/-- Limiting tuple cones with basis-valued points give finite presentations of
every actual Čech nerve term. -/
def FiniteBasisCover.cechPresentationOfCones {U : C} (s : FiniteBasisCover J B U)
    (b : ∀ n, (Fin (n + 1) → Fin s.size) → ι)
    (c : ∀ n (α : Fin (n + 1) → Fin s.size),
      WidePullbackCone (fun j => s.arrow (α j)))
    (hc : ∀ n α, IsLimit (c n α))
    (e : ∀ n α, (c n α).pt ≅ B (b n α)) :
    s.CechPresentation J B where
  size n := Fintype.card (Fin (n + 1) → Fin s.size)
  index n j := b n ((Fintype.equivFin _).symm j)
  iso n := representableCoproductCechIso s.arrow n (c n) (hc n) ≪≫
    Sigma.mapIso (fun α => shrinkYoneda.{w}.mapIso (e n α)) ≪≫
      (Sigma.reindex (Fintype.equivFin _).symm
        (fun α => shrinkYoneda.{w}.obj (B (b n α)))).symm

@[reassoc (attr := simp)]
theorem FiniteBasisCover.cechPresentationOfCones_ι_inv_π
    {U : C} (s : FiniteBasisCover J B U)
    (b : ∀ n, (Fin (n + 1) → Fin s.size) → ι)
    (c : ∀ n (α : Fin (n + 1) → Fin s.size),
      WidePullbackCone (fun j => s.arrow (α j)))
    (hc : ∀ n α, IsLimit (c n α))
    (e : ∀ n α, (c n α).pt ≅ B (b n α)) (n : ℕ)
    (i : Fin (Fintype.card (Fin (n + 1) → Fin s.size))) (j : Fin (n + 1)) :
    Sigma.ι (fun i => shrinkYoneda.{w}.obj
        (B (b n ((Fintype.equivFin _).symm i)))) i ≫
      ((s.cechPresentationOfCones J B b c hc e).iso n).inv ≫
        WidePullback.π (fun _ : Fin (n + 1) => (s.presheafArrow J B).hom) j =
      shrinkYoneda.{w}.map
        ((e n ((Fintype.equivFin _).symm i)).inv ≫
          (c n ((Fintype.equivFin _).symm i)).π j) ≫
            Sigma.ι (fun k => shrinkYoneda.{w}.obj (B (s.index k)))
              (((Fintype.equivFin _).symm i) j) := by
  change Sigma.ι (fun i => shrinkYoneda.{w}.obj
      (B (b n ((Fintype.equivFin _).symm i)))) i ≫
    ((Sigma.reindex (Fintype.equivFin _).symm
        (fun α => shrinkYoneda.{w}.obj (B (b n α)))).hom ≫
      (Sigma.mapIso (fun α => shrinkYoneda.{w}.mapIso (e n α))).inv ≫
        coproductWidePullbackMap s.arrow (c n)) ≫
          WidePullback.π (fun _ : Fin (n + 1) =>
            (representableCoproductArrow s.arrow).hom) j = _
  simp only [Category.assoc]
  erw [Sigma.ι_reindex_hom_assoc (Fintype.equivFin _).symm
    (fun α => shrinkYoneda.{w}.obj (B (b n α))) i]
  erw [Sigma.ι_mapIso_inv_assoc (fun α => shrinkYoneda.{w}.mapIso (e n α))]
  simp only [Functor.mapIso_inv, coproductWidePullbackMap_ι_π]
  erw [Functor.map_comp, Category.assoc]
  rfl

@[reassoc (attr := simp)]
theorem FiniteBasisCover.cechPresentationOfCones_ι_inv_base
    {U : C} (s : FiniteBasisCover J B U)
    (b : ∀ n, (Fin (n + 1) → Fin s.size) → ι)
    (c : ∀ n (α : Fin (n + 1) → Fin s.size),
      WidePullbackCone (fun j => s.arrow (α j)))
    (hc : ∀ n α, IsLimit (c n α))
    (e : ∀ n α, (c n α).pt ≅ B (b n α)) (n : ℕ)
    (i : Fin (Fintype.card (Fin (n + 1) → Fin s.size))) :
    Sigma.ι (fun i => shrinkYoneda.{w}.obj
        (B (b n ((Fintype.equivFin _).symm i)))) i ≫
      ((s.cechPresentationOfCones J B b c hc e).iso n).inv ≫
        WidePullback.base (fun _ : Fin (n + 1) => (s.presheafArrow J B).hom) =
      shrinkYoneda.{w}.map
        ((e n ((Fintype.equivFin _).symm i)).inv ≫
          (c n ((Fintype.equivFin _).symm i)).base) := by
  change Sigma.ι (fun i => shrinkYoneda.{w}.obj
      (B (b n ((Fintype.equivFin _).symm i)))) i ≫
    ((Sigma.reindex (Fintype.equivFin _).symm
        (fun α => shrinkYoneda.{w}.obj (B (b n α)))).hom ≫
      (Sigma.mapIso (fun α => shrinkYoneda.{w}.mapIso (e n α))).inv ≫
        coproductWidePullbackMap s.arrow (c n)) ≫
          WidePullback.base (fun _ : Fin (n + 1) =>
            (representableCoproductArrow s.arrow).hom) = _
  simp only [Category.assoc]
  erw [Sigma.ι_reindex_hom_assoc (Fintype.equivFin _).symm
    (fun α => shrinkYoneda.{w}.obj (B (b n α))) i]
  erw [Sigma.ι_mapIso_inv_assoc (fun α => shrinkYoneda.{w}.mapIso (e n α))]
  simp only [Functor.mapIso_inv, coproductWidePullbackMap_ι_base]
  exact (shrinkYoneda.map_comp _ _).symm

end Langlands.Cohomology.SiteCech
