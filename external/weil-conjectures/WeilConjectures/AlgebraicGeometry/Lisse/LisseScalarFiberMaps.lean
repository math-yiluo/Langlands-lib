/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement

/-! # Scalar maps on integral geometric stalk systems

## References

* Weil II (1.1.1) b), Stacks Tag 09B8
* Weil II (1.1.1) b), d)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe d
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

noncomputable section

local instance scalarFiberSheafify (Y : Scheme.{d}) (R : Type (d + 1)) [Ring R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{d + 1} R) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology
    (ModuleCat.{d + 1} R) Y).isRightAdjoint

private def coneOfSuccessor {C : Type*} [Category C] (D : ℕᵒᵖ ⥤ C) (M : C)
    (p : ∀ n : ℕ, M ⟶ D.obj (op n))
    (hp : ∀ n : ℕ, p (n + 1) ≫ D.map (homOfLE (Nat.le_succ n)).op = p n) : Cone D := by
  have hall (m n : ℕ) (h : m ≤ n) : p n ≫ D.map (homOfLE h).op = p m := by
    induction n, h using Nat.le_induction with
    | base =>
      have he : (homOfLE (le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
      simp only [he, D.map_id, Category.comp_id]
    | succ n h ih =>
      have he : (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op =
          (homOfLE (Nat.le_trans h (Nat.le_succ n))).op := Subsingleton.elim _ _
      rw [← he, D.map_comp, ← Category.assoc, hp n, ih]
  exact { pt := M, π :=
    { app j := p j.unop
      naturality i j f := by
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        change 𝟙 M ≫ p j.unop = p i.unop ≫ D.map f
        rw [Category.id_comp, hf]
        exact (hall j.unop i.unop (leOfHom f.unop)).symm } }

private def limitSectionsLinearEquiv {R : Type*} [Ring R]
    (D : ℕᵒᵖ ⥤ ModuleCat.{d + 1} R) :
    ↥(limit D) ≃ₗ[R] ModuleCat.sectionsSubmodule D :=
  { Types.isLimitEquivSections
      (isLimitOfPreserves (CategoryTheory.forget (ModuleCat R)) (limit.isLimit D)) with
    map_add' x y := Subtype.ext (funext (fun j ↦ map_add (limit.π D j).hom x y))
    map_smul' r x := Subtype.ext (funext (fun j ↦ map_smul (limit.π D j).hom r x)) }

variable (Y : Scheme.{d}) {Ω : Type d} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

private def scalarStalkComparison {R A : Type (d + 1)} [Ring R] [Ring A]
    (f : R →+* A) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R)) :
    (ModuleCat.ringExtendScalars.{d + 1, d + 1} f).obj
        ((pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj F) ≅
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj
        ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology f).obj F) :=
  let p := (pointSmallEtale y).ulift.{d + 1}
  let E := ModuleCat.ringExtendScalars.{d + 1, d + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).isLeftAdjoint
  ((p.presheafFiberCompIso E).app F.obj).symm ≪≫
    ((p.presheafToSheafCompSheafFiberIso (ModuleCat.{d + 1} A)).app (F.obj ⋙ E)).symm

variable (l : ℕ) [Fact l.Prime] (E : Type (d + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L : Type (d + 1)) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

private lemma integralStalk_annihilated (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    I ^ (n + 1) • (⊤ : Submodule R
      ((pointSmallEtale y).ulift.{d + 1}.sheafFiber (A := ModuleCat.{d + 1} R) |>.obj
        (F.obj.obj (op n)))) = ⊥ := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro r hr z _
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (F.obj.obj (op n)).obj) z
  have hz : r • s = 0 := by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := s))
    rw [F.property.2.1 n U] at h
    exact h
  change r • p.toPresheafFiber U x (F.obj.obj (op n)).obj s = 0
  rw [← map_smul, hz, map_zero]

private lemma integralStalk_adicLimit (F : LisseIntegralSheaf l E Y) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    let D := F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber
    let M := ModuleCat.sectionsSubmodule D
    Module.Finite R M ∧
      ∀ n : ℕ, Function.Surjective ((LinearMap.proj (op n)).comp M.subtype) ∧
        LinearMap.ker ((LinearMap.proj (op n)).comp M.subtype) =
          I ^ (n + 1) • (⊤ : Submodule R M) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  have hf (n : ℕ) : Module.Finite (Padic.coefficientExtensionIntegers l E)
      ↥(p.sheafFiber.obj (F.obj.obj (op n))) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp
      (((F.property.1 n).toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω y).of_iso
        (((pointSmallEtale y).uliftSheafFiberIso.{d + 1}
          (ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E))).app
            (F.obj.obj (op n))).symm)
  have h := Padic.adicLimit_finite_modules l E (F.obj ⋙ p.sheafFiber) hf
    (integralStalk_annihilated Y y l E F) (F.property.2.2 Ω y)
  exact ⟨h.1, h.2.1⟩

/-- The integral geometric fibre is a finite coefficient module. -/
theorem lisseIntegralFiber_finite (F : LisseIntegralSheaf l E Y) :
    Module.Finite (Padic.coefficientExtensionIntegers l E) (lisseIntegralFiber l E Y y F) := by
  have := (integralStalk_adicLimit Y y l E F).1
  exact Module.Finite.equiv (limitSectionsLinearEquiv
    (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber)).symm

/-- Projections of an integral geometric fibre are its coefficient reductions. -/
theorem lisseIntegralFiber_projection (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    let π := (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber) (op n)).hom
    Function.Surjective π ∧ LinearMap.ker π =
      I ^ (n + 1) • (⊤ : Submodule R (lisseIntegralFiber l E Y y F)) := by
  let D := F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber
  let M := ModuleCat.sectionsSubmodule D
  let e := limitSectionsLinearEquiv D
  let q := (LinearMap.proj (op n)).comp M.subtype
  have hq := (integralStalk_adicLimit Y y l E F).2 n
  change Function.Surjective (q.comp e.toLinearMap) ∧
    LinearMap.ker (q.comp e.toLinearMap) = _
  refine ⟨hq.1.comp e.surjective, ?_⟩
  rw [LinearMap.ker_comp, hq.2, Submodule.comap_smul'' e.injective
    (by rw [e.range]), Submodule.comap_top]

private def scalarFiberLevelMap (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    (pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))) ⟶
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι)).obj
        ((pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj
          (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj.obj (op m))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let A := Padic.coefficientExtensionRing l L (m + 1)
  let α := lisseIntegerInclusion l E L ι
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))
  let r := lisseScalarCoefficientMap l E L ι m
  let p := (pointSmallEtale y).ulift.{d + 1}
  let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
  let D := (Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology r).obj Fₙ
  let c := scalarStalkComparison Y y r Fₙ
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r
  let := (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} q).isLeftAdjoint
  let e := p.sheafFiberCompIso (ModuleCat.restrictScalars.{d + 1} q)
  let t := p.sheafFiber.mapIso ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F m)
  exact adj.unit.app _ ≫ (ModuleCat.restrictScalars r).map c.hom ≫
      (ModuleCat.restrictScalars α).map (e.inv.app D ≫ t.inv)

private lemma scalarFiberLevelMap_germ (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (U : Y.Etale) (x : (pointSmallEtale y).ulift.{d + 1}.fiber.obj U)
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    scalarFiberLevelMap Y y l E L ι F m
      ((pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj s) =
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
        ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F m).inv
        ((pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
          (lisseIntegralScalarLevel l E Y L ι F m).obj
            (lisseIntegralScalarGenerator l E Y L ι F m U 1 s)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let A := Padic.coefficientExtensionRing l L (m + 1)
  let α := lisseIntegerInclusion l E L ι
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))
  let r := lisseScalarCoefficientMap l E L ι m
  let p := (pointSmallEtale y).ulift.{d + 1}
  let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
  let D := (Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology r).obj Fₙ
  let Efun := ModuleCat.ringExtendScalars.{d + 1, d + 1} r
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r
  let c := scalarStalkComparison Y y r Fₙ
  let := (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} q).isLeftAdjoint
  let e := p.sheafFiberCompIso (ModuleCat.restrictScalars.{d + 1} q)
  have hc := (etale_stalk_scalar_component_unique y r Efun adj Fₙ).2.1 U x
  have hv := congrArg (fun f ↦ f s) hc
  change c.hom (adj.unit.app _ (p.toPresheafFiber U x Fₙ.obj s)) =
    p.toPresheafFiber U x D.obj
      ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
        (adj.unit.app _ s)) at hv
  have he := p.toPresheafFiber_presheafFiberCompIso_hom_app
    (ModuleCat.restrictScalars.{d + 1} q) U x D.obj
  have hev := congrArg (fun f ↦ f
    ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
      (adj.unit.app _ s))) he
  have hgen : lisseIntegralScalarGenerator l E Y L ι F m U 1 s =
      (toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
        (adj.unit.app _ s) := by
    simp only [lisseIntegralScalarGenerator, ModuleCat.ringExtensionTmul, one_smul]
    rfl
  change e.hom.app D
      (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι F m).obj
        ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
          (adj.unit.app _ s))) =
      p.toPresheafFiber U x D.obj
        ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
          (adj.unit.app _ s)) at hev
  change (p.sheafFiber.map
      ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F m).inv)
        (e.inv.app D (c.hom (adj.unit.app _ (p.toPresheafFiber U x Fₙ.obj s)))) = _
  rw [hv, ← hev, ← hgen]
  congr 1
  exact ConcreteCategory.congr_hom (e.hom_inv_id_app D) _

private lemma scalarFiberLevelMap_transition (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    scalarFiberLevelMap Y y l E L ι F (m + 1) ≫
        (ModuleCat.restrictScalars (lisseIntegerInclusion l E L ι)).map
          ((pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
            (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj.map
              (homOfLE (Nat.le_succ m)).op)) =
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
        (F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op) ≫
          scalarFiberLevelMap Y y l E L ι F m := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let D := lisseIntegralScalarExtensionData l E Y L ι
  apply p.presheafFiber_hom_ext
  intro U x
  apply ModuleCat.hom_ext
  ext s
  change p.sheafFiber.map (((D.functor.obj F).obj.map (homOfLE (Nat.le_succ m)).op))
    (scalarFiberLevelMap Y y l E L ι F (m + 1) (p.toPresheafFiber U x
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj s)) =
      scalarFiberLevelMap Y y l E L ι F m
        (p.sheafFiber.map (F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op)
          (p.toPresheafFiber U x
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj s))
  rw [scalarFiberLevelMap_germ]
  change _ = scalarFiberLevelMap Y y l E L ι F m
    (p.presheafFiber.map
      (F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op).hom
        (p.toPresheafFiber U x
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj s))
  rw [p.toPresheafFiber_naturality_apply, scalarFiberLevelMap_germ]
  apply (ConcreteCategory.bijective_of_isIso
    (p.sheafFiber.map (D.levelIso F m).hom)).injective
  have h := D.transition F m U 1 s
  simp only [map_one] at h
  change p.presheafFiber.map (D.levelIso F m).hom.hom
    (p.presheafFiber.map (((D.functor.obj F).obj.map (homOfLE (Nat.le_succ m)).op).hom)
      (p.presheafFiber.map (D.levelIso F (m + 1)).inv.hom
        (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι F (m + 1)).obj
          (lisseIntegralScalarGenerator l E Y L ι F (m + 1) U 1 s)))) =
    p.presheafFiber.map (D.levelIso F m).hom.hom
      (p.presheafFiber.map (D.levelIso F m).inv.hom
        (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι F m).obj
          (lisseIntegralScalarGenerator l E Y L ι F m U 1
            ((F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op).hom.app
              (op U) s))))
  simp only [p.toPresheafFiber_naturality_apply]
  rw [h]
  congr 1
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) (D.levelIso F m).inv_hom_id) _).symm

private lemma scalarFiberLevelMap_naturality {F G : LisseIntegralSheaf l E Y}
    (f : F ⟶ G) (m : ℕ) :
    scalarFiberLevelMap Y y l E L ι F m ≫
        (ModuleCat.restrictScalars (lisseIntegerInclusion l E L ι)).map
          ((pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
            (((lisseIntegralScalarExtensionData l E Y L ι).functor.map f).hom.app (op m))) =
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
        (f.hom.app (op (lisseScalarSourceIndex l E L ι m))) ≫
          scalarFiberLevelMap Y y l E L ι G m := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let D := lisseIntegralScalarExtensionData l E Y L ι
  apply p.presheafFiber_hom_ext
  intro U x
  apply ModuleCat.hom_ext
  ext s
  change p.sheafFiber.map ((D.functor.map f).hom.app (op m))
    (scalarFiberLevelMap Y y l E L ι F m (p.toPresheafFiber U x
      (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj s)) =
      scalarFiberLevelMap Y y l E L ι G m
        (p.sheafFiber.map (f.hom.app (op (lisseScalarSourceIndex l E L ι m)))
          (p.toPresheafFiber U x
            (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj s))
  rw [scalarFiberLevelMap_germ]
  change _ = scalarFiberLevelMap Y y l E L ι G m
    (p.presheafFiber.map (f.hom.app (op (lisseScalarSourceIndex l E L ι m))).hom
      (p.toPresheafFiber U x (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj s))
  rw [p.toPresheafFiber_naturality_apply, scalarFiberLevelMap_germ]
  apply (ConcreteCategory.bijective_of_isIso
    (p.sheafFiber.map (D.levelIso G m).hom)).injective
  have h := D.map F G f m U 1 s
  change p.presheafFiber.map (D.levelIso G m).hom.hom
    (p.presheafFiber.map ((D.functor.map f).hom.app (op m)).hom
      (p.presheafFiber.map (D.levelIso F m).inv.hom
        (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι F m).obj
          (lisseIntegralScalarGenerator l E Y L ι F m U 1 s)))) =
    p.presheafFiber.map (D.levelIso G m).hom.hom
      (p.presheafFiber.map (D.levelIso G m).inv.hom
        (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι G m).obj
          (lisseIntegralScalarGenerator l E Y L ι G m U 1
            ((f.hom.app (op (lisseScalarSourceIndex l E L ι m))).hom.app (op U) s))))
  simp only [p.toPresheafFiber_naturality_apply]
  rw [h]
  congr 1
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) (D.levelIso G m).inv_hom_id) _).symm

private def scalarIntegralFiberUnit (F : LisseIntegralSheaf l E Y) :
    lisseIntegralFiber l E Y y F ⟶
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι)).obj
        (lisseIntegralFiber l L Y y
          ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F)) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let α := ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι)
  let D := ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙ p.sheafFiber
  let maps := fun n : ℕ ↦
    limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι n)) ≫
      scalarFiberLevelMap Y y l E L ι F n
  have hm (n : ℕ) : maps (n + 1) ≫ (D ⋙ α).map (homOfLE (Nat.le_succ n)).op = maps n := by
    dsimp only [maps, Functor.comp_map, D]
    rw [Category.assoc, scalarFiberLevelMap_transition, ← Category.assoc]
    change (limit.π (F.obj ⋙ p.sheafFiber) _ ≫
      (F.obj ⋙ p.sheafFiber).map (homOfLE (lisseScalarSourceIndex_le l E L ι n)).op) ≫ _ = _
    rw [limit.w]
  exact limit.lift (D ⋙ α) (coneOfSuccessor (D ⋙ α) _ maps hm) ≫
    (preservesLimitIso α D).inv

private lemma scalarIntegralFiberUnit_π (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    scalarIntegralFiberUnit Y y l E L ι F ≫
        (ModuleCat.restrictScalars (lisseIntegerInclusion l E L ι)).map
          (limit.π (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙
            (pointSmallEtale y).ulift.{d + 1}.sheafFiber) (op n)) =
      limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber)
          (op (lisseScalarSourceIndex l E L ι n)) ≫
        scalarFiberLevelMap Y y l E L ι F n := by
  dsimp only [scalarIntegralFiberUnit]
  rw [Category.assoc, preservesLimitIso_inv_π, limit.lift_π]
  rfl

private lemma scalarIntegralFiberUnit_naturality {F G : LisseIntegralSheaf l E Y}
    (f : F ⟶ G) :
    scalarIntegralFiberUnit Y y l E L ι F ≫
        (ModuleCat.restrictScalars (lisseIntegerInclusion l E L ι)).map
          (lim.map (Functor.whiskerRight
            ((lisseIntegralScalarExtensionData l E Y L ι).functor.map f).hom
              (pointSmallEtale y).ulift.{d + 1}.sheafFiber)) =
      lim.map (Functor.whiskerRight f.hom
          (pointSmallEtale y).ulift.{d + 1}.sheafFiber) ≫
        scalarIntegralFiberUnit Y y l E L ι G := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let α := ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι)
  let D := ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj G).obj ⋙ p.sheafFiber
  apply (cancel_mono (preservesLimitIso α D).hom).mp
  apply limit.hom_ext
  intro j
  simp only [Category.assoc, preservesLimitIso_hom_π, lim]
  rw [← α.map_comp, limMap_π, α.map_comp]
  rw [← Category.assoc, scalarIntegralFiberUnit_π]
  simp only [Functor.whiskerRight_app]
  dsimp only [α]
  rw [Category.assoc, scalarFiberLevelMap_naturality, ← Category.assoc]
  rw [Category.assoc, scalarIntegralFiberUnit_π, ← Category.assoc]
  conv_rhs => rw [← Category.assoc, limMap_π]
  rfl

private def scalarIntegralFiberComparison (F : LisseIntegralSheaf l E Y) :
    (ModuleCat.ringExtendScalars.{d + 1, d + 1} (lisseIntegerInclusion l E L ι)).obj
        (lisseIntegralFiber l E Y y F) ⟶
      lisseIntegralFiber l L Y y
        ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F) :=
  (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1}
    (lisseIntegerInclusion l E L ι)).homEquiv _ _ |>.symm
      (scalarIntegralFiberUnit Y y l E L ι F)

private lemma scalarIntegralFiberComparison_unit (F : LisseIntegralSheaf l E Y)
    (z : lisseIntegralFiber l E Y y F) :
    scalarIntegralFiberComparison Y y l E L ι F
      (ModuleCat.ringExtensionTmul (lisseIntegerInclusion l E L ι)
        (lisseIntegralFiber l E Y y F) 1 z) = scalarIntegralFiberUnit Y y l E L ι F z := by
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1}
    (lisseIntegerInclusion l E L ι)
  have h := congrArg (fun f ↦ f z)
    ((adj.homEquiv _ _).apply_symm_apply (scalarIntegralFiberUnit Y y l E L ι F))
  simp only [Adjunction.homEquiv_apply, ModuleCat.comp_apply] at h
  change scalarIntegralFiberComparison Y y l E L ι F
    (adj.unit.app _ z) = scalarIntegralFiberUnit Y y l E L ι F z at h
  simpa only [ModuleCat.ringExtensionTmul, one_smul] using h

/-- The projection and pure-germ formula specifying the integral scalar comparison. -/
def IsLisseIntegralScalarFiberComparison (F : LisseIntegralSheaf l E Y)
    (c : (ModuleCat.ringExtendScalars.{d + 1, d + 1}
        (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F) ⟶
      lisseIntegralFiber l L Y y
        ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F)) : Prop :=
  ∀ (n : ℕ) (z : lisseIntegralFiber l E Y y F) (U : Y.Etale)
    (x : (pointSmallEtale y).ulift.{d + 1}.fiber.obj U)
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj.obj (op U)),
    limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber)
        (op (lisseScalarSourceIndex l E L ι n)) z =
      (pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj s →
    (pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
      ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n).hom
        (limit.π (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙
          (pointSmallEtale y).ulift.{d + 1}.sheafFiber) (op n)
            (c (ModuleCat.ringExtensionTmul (lisseIntegerInclusion l E L ι)
              (lisseIntegralFiber l E Y y F) 1 z))) =
      (pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
        (lisseIntegralScalarLevel l E Y L ι F n).obj
          (lisseIntegralScalarGenerator l E Y L ι F n U 1 s)

private theorem scalarIntegralFiberComparison_spec (F : LisseIntegralSheaf l E Y) :
    IsLisseIntegralScalarFiberComparison Y y l E L ι F
      (scalarIntegralFiberComparison Y y l E L ι F) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let D := lisseIntegralScalarExtensionData l E Y L ι
  intro n z U x s hs
  rw [scalarIntegralFiberComparison_unit]
  have hπ := congrArg (fun f ↦ f z) (scalarIntegralFiberUnit_π Y y l E L ι F n)
  change limit.π ((D.functor.obj F).obj ⋙ p.sheafFiber) (op n)
    (scalarIntegralFiberUnit Y y l E L ι F z) =
      scalarFiberLevelMap Y y l E L ι F n
        (limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι n)) z) at hπ
  rw [hπ, hs, scalarFiberLevelMap_germ]
  exact ConcreteCategory.congr_hom
    (p.sheafFiber.mapIso (D.levelIso F n)).inv_hom_id _

/-- The canonical integral scalar comparison exists and is uniquely determined by
its finite-level pure-germ formula. -/
theorem lisseIntegralScalarFiberComparison_exists (F : LisseIntegralSheaf l E Y) :
    ∃! c : (ModuleCat.ringExtendScalars.{d + 1, d + 1}
        (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F) ⟶
      lisseIntegralFiber l L Y y
        ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F),
      IsLisseIntegralScalarFiberComparison Y y l E L ι F c := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let D := lisseIntegralScalarExtensionData l E Y L ι
  let c₀ := scalarIntegralFiberComparison Y y l E L ι F
  have h₀ := scalarIntegralFiberComparison_spec Y y l E L ι F
  refine ⟨c₀, h₀, ?_⟩
  intro c hc
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1}
    (lisseIntegerInclusion l E L ι)
  apply (adj.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  ext z
  change c (adj.unit.app _ z) = c₀ (adj.unit.app _ z)
  apply Concrete.limit_ext ((D.functor.obj F).obj ⋙ p.sheafFiber)
  intro j
  obtain ⟨U, x, s, hs⟩ := p.toPresheafFiber_jointly_surjective
    (P := (F.obj.obj (op (lisseScalarSourceIndex l E L ι j.unop))).obj)
      (limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι j.unop)) z)
  apply (ConcreteCategory.bijective_of_isIso
    (p.sheafFiber.map (D.levelIso F j.unop).hom)).injective
  simpa only [ModuleCat.ringExtensionTmul, one_smul] using
    (hc j.unop z U x s hs.symm).trans (h₀ j.unop z U x s hs.symm).symm

/-- The integral scalar comparison, constructed by its uniquely specified finite levels. -/
def lisseIntegralScalarFiberComparison (F : LisseIntegralSheaf l E Y) :
    (ModuleCat.ringExtendScalars.{d + 1, d + 1} (lisseIntegerInclusion l E L ι)).obj
        (lisseIntegralFiber l E Y y F) ⟶
      lisseIntegralFiber l L Y y
        ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F) :=
  (lisseIntegralScalarFiberComparison_exists Y y l E L ι F).choose

/-- The integral scalar comparison has the prescribed pure-germ formula. -/
theorem lisseIntegralScalarFiberComparison_spec (F : LisseIntegralSheaf l E Y) :
    IsLisseIntegralScalarFiberComparison Y y l E L ι F
      (lisseIntegralScalarFiberComparison Y y l E L ι F) :=
  (lisseIntegralScalarFiberComparison_exists Y y l E L ι F).choose_spec.1

private lemma lisseIntegralScalarFiberComparison_eq (F : LisseIntegralSheaf l E Y) :
    lisseIntegralScalarFiberComparison Y y l E L ι F =
      scalarIntegralFiberComparison Y y l E L ι F := by
  exact ((lisseIntegralScalarFiberComparison_exists Y y l E L ι F).choose_spec.2 _
    (scalarIntegralFiberComparison_spec Y y l E L ι F)).symm

/-- The integral scalar comparison is natural in the integral sheaf. -/
theorem lisseIntegralScalarFiberComparison_naturality {F G : LisseIntegralSheaf l E Y}
    (f : F ⟶ G) :
    (ModuleCat.ringExtendScalars.{d + 1, d + 1} (lisseIntegerInclusion l E L ι)).map
        (lim.map (Functor.whiskerRight f.hom
          (pointSmallEtale y).ulift.{d + 1}.sheafFiber)) ≫
        lisseIntegralScalarFiberComparison Y y l E L ι G =
      lisseIntegralScalarFiberComparison Y y l E L ι F ≫
        lim.map (Functor.whiskerRight
          ((lisseIntegralScalarExtensionData l E Y L ι).functor.map f).hom
            (pointSmallEtale y).ulift.{d + 1}.sheafFiber) := by
  rw [lisseIntegralScalarFiberComparison_eq, lisseIntegralScalarFiberComparison_eq]
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1}
    (lisseIntegerInclusion l E L ι)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  have he (H : LisseIntegralSheaf l E Y) :
      adj.homEquiv (lisseIntegralFiber l E Y y H) _
        (scalarIntegralFiberComparison Y y l E L ι H) =
          scalarIntegralFiberUnit Y y l E L ι H :=
    (adj.homEquiv _ _).apply_symm_apply _
  erw [he, he]
  exact (scalarIntegralFiberUnit_naturality Y y l E L ι f).symm

end
end AlgebraicGeometry.Scheme
