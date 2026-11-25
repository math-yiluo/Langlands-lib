/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import all WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry

/-! The two residual finite-level identifications used by the main theorem. -/

/-- The canonical finite-level map is the base change of a quotient immersion.
Source: Stacks Project, Tag 02OD, finite fibre factorisation.
The finite fibre is obtained by pulling back the quotient
`Spec (A / m^(n+1)) → Spec A` along `X → Y`. The quotient map is
surjective, hence its affine morphism is a closed immersion. Stability of
closed immersions under pullback, together with the defining pullback
comparison for `formalFunctionsFiniteι`, gives the result.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed) -/
theorem formalFunctionsFiniteι_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (n : ℕ) : IsClosedImmersion (formalFunctionsFiniteι f y n) := by
  have hp : IsPullback (pullback.fst (formalFibreBaseMap Y y n) f)
      (formalFunctionsFiniteι f y n)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n))))
      (pullback.fst (Y.fromSpecStalk y) f) := by
    apply ((IsPullback.of_hasPullback (Y.fromSpecStalk y) f).paste_vert_iff
      (by simp [formalFunctionsFiniteι])).mp
    simpa [formalFunctionsFiniteι, formalFibreBaseMap, formalFibreι] using
      (IsPullback.of_hasPullback (formalFibreBaseMap Y y n) f)
  apply MorphismProperty.of_isPullback hp
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_unit_factor {A B C : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (w : k = i ≫ g)
    (adjI : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i)
    (F : C.Modules) :
    ∃ e : (Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback g).obj F) ≅
          (Scheme.Modules.tensorPullback k).obj F,
      adjI.unit.app ((Scheme.Modules.tensorPullback g).obj F) ≫
          (Scheme.Modules.pushforward i).map e.hom =
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv F
          _).symm
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app F ≫
            (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
            (Scheme.Modules.pushforwardComp i g).inv.app _) := by
  let adjG := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let adjK := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let r := Scheme.Modules.pushforwardCongr w ≪≫ (Scheme.Modules.pushforwardComp i g).symm
  let e := ((conjugateIsoEquiv adjK (adjG.comp adjI)).symm r).app F
  refine ⟨e, ?_⟩
  apply (adjG.homEquiv F _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_conjugateEquiv_symm adjK (adjG.comp adjI) r.hom F
  change adjG.unit.app F ≫ (Scheme.Modules.pushforward g).map
      (adjI.unit.app ((Scheme.Modules.tensorPullback g).obj F)) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward i).map
          (((conjugateEquiv adjK (adjG.comp adjI)).symm r.hom).app F)) = _
  simpa only [r, Iso.trans_hom, NatTrans.comp_app, Functor.comp_map,
    Iso.symm_hom, Adjunction.comp_unit_app, Category.assoc] using hu.symm


set_option backward.isDefEq.respectTransparency false in
private theorem power_quotient_iso {B : Scheme.{u}} (J : B.IdealSheafData)
    (n : ℕ) (F : B.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        cokernel (Scheme.idealModuleProductι (J ^ n).toModulesι F),
      formalModuleQuotientπ J n F ≫ e.hom =
        cokernel.π (Scheme.idealModuleProductι (J ^ n).toModulesι F) := by
  have := Scheme.Modules.power_mono J n
  let e := Subobject.isoOfMkEqMk _ _ (Scheme.Modules.power_subobject J n)
  have he : e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
    simp [e]
  let : MonoidalCategory B.Modules := SheafOfModules.monoidalCategory B.sheaf
  open MonoidalCategory in
  have hμ : (Scheme.idealSheafPower J.toModulesι n).2 ▷ F ≫ (λ_ F).hom =
      e.hom ▷ F ≫ ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom) := by
    rw [← Category.assoc, ← comp_whiskerRight, he]
  open MonoidalCategory in
  have hs : imageSubobject ((Scheme.idealSheafPower J.toModulesι n).2 ▷ F ≫ (λ_ F).hom) =
      imageSubobject ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom) := by
    calc
      _ = imageSubobject (e.hom ▷ F ≫ ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom)) :=
        congrArg (fun f ↦ imageSubobject f) hμ
      _ = _ := imageSubobject_iso_comp _ _
  let q := Subobject.isoOfMkEqMk _ _ hs
  have hq : q.hom ≫ Scheme.idealModuleProductι (J ^ n).toModulesι F =
      Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F := by
    simp [q, Scheme.idealModuleProductι]
  refine ⟨cokernel.mapIso _ _ q (Iso.refl F) (by simpa using hq.symm), ?_⟩
  simp [formalModuleQuotientπ, cokernel.mapIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the closed-immersion unit quotient to the canonical finite-level map.
Source: Stacks Project, Tags 02OD and 04CJ (1).
Apply `closedImmersion_unit_quotient` to the finite-level closed immersion.
The quotient-base-change ideal calculation identifies its kernel with the
extension of the `(n+1)`-st power of the maximal ideal; the product formula
identifies this with the ideal used by `formalModuleQuotient`. Finally, the
canonical tensor-pullback comparison identifies the resulting unit with
`formalFunctionsFiniteFMap`, yielding the displayed isomorphism and equation.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso) -/
theorem formalFunctionsFinite_sheaf_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (n : ℕ) :
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    ∃ e : formalModuleQuotient J (n + 1) F' ≅
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
      formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
        formalFunctionsFiniteFMap f y F n := by
  classical
  dsimp only
  let g := pullback.snd (Y.fromSpecStalk y) f
  let a := pullback.fst (Y.fromSpecStalk y) f
  let i := formalFunctionsFiniteι f y n
  let F' := (Scheme.Modules.tensorPullback g).obj F
  let J := (Scheme.IdealSheafData.ofIdealTop
    ((maximalIdeal (Y.presheaf.stalk y)).map
      (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap a
  have hi : IsClosedImmersion i := formalFunctionsFiniteι_isClosedImmersion f y n
  have hp : IsPullback (pullback.fst (formalFibreBaseMap Y y n) f) i
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n)))) a := by
    apply ((IsPullback.of_hasPullback (Y.fromSpecStalk y) f).paste_vert_iff
      (by simp [i, formalFunctionsFiniteι])).mp
    simpa [i, formalFunctionsFiniteι, formalFibreBaseMap, formalFibreι] using
      (IsPullback.of_hasPullback (formalFibreBaseMap Y y n) f)
  have hk : i.ker = J ^ (n + 1) := by
    rw [← hp.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
    rw [(quotientBaseChange_closedImmersion_ideal a (formalFibreIdeal Y y n)).2.1]
    exact ((quotientBaseChange_extendedIdeal_mul_pow a).2
      (maximalIdeal (Y.presheaf.stalk y)) (n + 1) (by omega)).symm
  let adjI : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  obtain ⟨η, hη, _⟩ := Scheme.Modules.closedImmersion_unit_quotient i
  have hηF := hη F'
  dsimp only at hηF
  have : IsIso (η F') := hηF.2.2.2
  let e₀ := asIso (η F')
  have hpower : ∃ e : formalModuleQuotient J (n + 1) F' ≅
      cokernel (Scheme.idealModuleProductι i.ker.toModulesι F'),
      formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
        cokernel.π (Scheme.idealModuleProductι i.ker.toModulesι F') := by
    rw [hk]
    exact power_quotient_iso J (n + 1) F'
  obtain ⟨e₁, he₁⟩ := hpower
  obtain ⟨e₂, he₂⟩ := tensor_unit_factor i g (formalFibreι f y n)
    (formalFunctionsFiniteι_snd f y n).symm adjI F
  refine ⟨e₁ ≪≫ e₀ ≪≫ (Scheme.Modules.pushforward i).mapIso e₂, ?_⟩
  change formalModuleQuotientπ J (n + 1) F' ≫ e₁.hom ≫ e₀.hom ≫
    (Scheme.Modules.pushforward i).map e₂.hom = _
  have he₀ : cokernel.π (Scheme.idealModuleProductι i.ker.toModulesι F') ≫
      e₀.hom = adjI.unit.app F' := hηF.2.2.1
  rw [← Category.assoc, he₁, ← Category.assoc, he₀]
  exact he₂

end AlgebraicGeometry
