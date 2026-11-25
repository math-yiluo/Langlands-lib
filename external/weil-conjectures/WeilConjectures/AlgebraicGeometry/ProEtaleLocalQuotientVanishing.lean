/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-! # Vanishing of local quotient obstructions

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private lemma conj_congr_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    conjugateEquiv (upperStarLowerStarAdjunction Ab.{u + 1} g')
      (upperStarLowerStarAdjunction Ab.{u + 1} g)
      (upperStarCongr Ab.{u + 1} h).hom = (lowerStarCongr Ab.{u + 1} h).inv := by
  subst h
  simp [upperStarCongr, lowerStarCongr]

private lemma lowerCongr_inv {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (lowerStarCongr Ab.{u + 1} h).inv = (lowerStarCongr Ab.{u + 1} h.symm).hom := by
  subst h
  rfl

private lemma conj_square {W A B X : Scheme.{u}} {p : W ⟶ A} {s : W ⟶ B}
    {i : A ⟶ X} {j : B ⟶ X} (h : p ≫ i = s ≫ j) :
    conjugateEquiv
      ((upperStarLowerStarAdjunction Ab.{u + 1} j).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} s))
      ((upperStarLowerStarAdjunction Ab.{u + 1} i).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} p))
      (upperStarCompIso Ab.{u + 1} h).hom =
        (squareLowerStarIso Ab.{u + 1} (CommSq.mk h)).hom := by
  simp only [upperStarCompIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction Ab.{u + 1} (s ≫ j)),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction Ab.{u + 1} (p ≫ i)),
    conjugateEquiv_upperStarComp_hom, conj_congr_hom,
    coefficient_conjugateEquiv_upperStarComp_inv]
  simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom]
  rw [lowerCongr_inv]

section AbstractMate
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
private lemma reverse_mate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (α : TwoSquare F₁ L₁ L₂ F₂) (β : TwoSquare U₂ R₂ R₁ U₁)
    (h : conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α = β) :
    (mateEquiv adj₁ adj₂ α) =
      ((mateEquiv adj₄ adj₃).symm β) := by
  have he := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α
  rw [h] at he
  apply (mateEquiv adj₄ adj₃).eq_symm_apply.mpr
  refine NatTrans.ext (funext fun K ↦ ?_)
  exact congrArg (fun t => t.app K) he

private lemma mate_zero [HasZeroMorphisms C] [HasZeroMorphisms D]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [Functor.PreservesZeroMorphisms R₂]
    (α : TwoSquare F₁ L₁ L₂ F₂) {X : A} {Y : B} {P : C}
    (q : P ⟶ F₁.obj X) (c : L₁.obj X ⟶ Y)
    [Mono ((mateEquiv adj₁ adj₂ α).app Y)]
    (h : L₂.map q ≫ α.app X ≫ F₂.map c = 0) :
    q ≫ F₁.map ((adj₁.homEquiv X Y) c) = 0 := by
  let γ := (mateEquiv adj₁ adj₂ α)
  have hn := γ.naturality c
  change F₁.map (R₁.map c) ≫ γ.app Y = γ.app (L₁.obj X) ≫ R₂.map (F₂.map c) at hn
  have hu := unit_mateEquiv adj₁ adj₂ α X
  change F₁.map (adj₁.unit.app X) ≫ γ.app (L₁.obj X) =
    adj₂.unit.app (F₁.obj X) ≫ R₂.map (α.app X) at hu
  have hq := (adj₂.unit_naturality q).symm
  change q ≫ adj₂.unit.app (F₁.obj X) = adj₂.unit.app P ≫ R₂.map (L₂.map q) at hq
  apply (cancel_mono (γ.app Y)).mp
  rw [zero_comp, Adjunction.homEquiv_unit, F₁.map_comp]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc (F₁.map (adj₁.unit.app X)), hu]
  simp only [Category.assoc]
  rw [← Category.assoc q, hq]
  simp only [Category.assoc]
  rw [← R₂.map_comp, ← R₂.map_comp, h, R₂.map_zero, comp_zero]

end AbstractMate

private lemma mate_square_iso {W A B X : Scheme.{u}} {p : W ⟶ A} {s : W ⟶ B}
    {i : A ⟶ X} {j : B ⟶ X} [WeaklyEtale i] [WeaklyEtale s]
    (h : IsPullback p s i j) :
    IsIso (mateEquiv (upperStarLowerStarAdjunction Ab.{u + 1} j)
      (upperStarLowerStarAdjunction Ab.{u + 1} p)
      (TwoSquare.mk _ _ _ _ (upperStarCompIso Ab.{u + 1} h.w).hom)) := by
  have he := reverse_mate
    (upperStarLowerStarAdjunction Ab.{u + 1} j)
    (upperStarLowerStarAdjunction Ab.{u + 1} p)
    (upperStarLowerStarAdjunction Ab.{u + 1} i)
    (upperStarLowerStarAdjunction Ab.{u + 1} s)
    (TwoSquare.mk _ _ _ _ (upperStarCompIso Ab.{u + 1} h.w).hom)
    (TwoSquare.mk _ _ _ _ (squareLowerStarIso Ab.{u + 1} h.toCommSq).hom)
    (conj_square h.w)
  change _ = _ at he
  rw [he]
  exact isIso_baseChangeMap_of_isPullback Ab.{u + 1} h

/-- A prescribed local subobject lies in the restriction of every local quotient
kernel when the subobjects agree on overlaps.

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).

Proof: inverse image along each weakly etale covering arrow is restriction to the
localized site and preserves products. It is enough to compose with each product
projection. On U_i times_X U_j, the overlap comparison identifies the pullback of
q_i with the pullback of q_j. The latter has zero composite with its own cokernel
map. Weakly etale base change identifies the restriction of the pushforward of
this local quotient with the pushforward from that overlap. Under the adjunction,
the desired composite is exactly the zero composite just obtained, including the
specified upperStarCompIso. Hence every component vanishes, and so does the map
to the product. There are no components or local conditions for an empty cover.
No global sheaf, action, factorization, or isomorphism is asserted here. -/
theorem localSubobjectQuotientMap_zero_of_compatible
    (X : Scheme.{u}) (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
    (q : ∀ i, L i ⟶ (upperStar Ab.{u + 1} (U.f i)).obj Q)
    (hcompatible : ∀ i j, ∃ c :
      (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i) ≅
        (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j),
      c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j) =
        (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i) ≫
          (upperStarCompIso Ab.{u + 1}
            (pullback.condition (f := U.f i) (g := U.f j))).hom.app Q) :
    ∀ i, q i ≫ (upperStar Ab.{u + 1} (U.f i)).map
      (localSubobjectQuotientMap X Q U L q) = 0 := by
  intro i
  let B := upperStar Ab.{u + 1} (U.f i)
  have hw : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ (.mk i)
  have : PreservesLimitsOfShape (Discrete U.I₀)
      (localizationRestriction Ab.{u + 1} (U.f i) hw) := by
    unfold localizationRestriction
    infer_instance
  have : PreservesLimitsOfShape (Discrete U.I₀) B :=
    preservesLimitsOfShape_of_natIso
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (U.f i) hw).symm
  let D := fun j => (lowerStar Ab.{u + 1} (U.f j)).obj (cokernel (q j))
  apply (isLimitOfPreserves B (limit.isLimit (Discrete.functor D))).hom_ext
  intro k
  change (q i ≫ B.map (localSubobjectQuotientMap X Q U L q)) ≫
    B.map (Pi.π D k.as) = 0 ≫ B.map (Pi.π D k.as)
  rw [Category.assoc, ← B.map_comp, localSubobjectQuotientMap, Pi.lift_comp_π, zero_comp]
  let j := k.as
  let p := pullback.fst (U.f i) (U.f j)
  let s := pullback.snd (U.f i) (U.f j)
  have : WeaklyEtale (U.f i) := hw
  have : WeaklyEtale s := by dsimp [s]; infer_instance
  let θ := TwoSquare.mk _ _ _ _
    (upperStarCompIso Ab.{u + 1} (pullback.condition (f := U.f i) (g := U.f j))).hom
  have hθ : IsIso (mateEquiv (upperStarLowerStarAdjunction Ab.{u + 1} (U.f j))
      (upperStarLowerStarAdjunction Ab.{u + 1} p) θ) :=
    mate_square_iso (IsPullback.of_hasPullback (U.f i) (U.f j))
  have : Mono ((mateEquiv (upperStarLowerStarAdjunction Ab.{u + 1} (U.f j))
      (upperStarLowerStarAdjunction Ab.{u + 1} p) θ).app (cokernel (q j))) :=
    inferInstance
  apply mate_zero (upperStarLowerStarAdjunction Ab.{u + 1} (U.f j))
    (upperStarLowerStarAdjunction Ab.{u + 1} p) θ (q i) (cokernel.π (q j))
  obtain ⟨c, hc⟩ := hcompatible i j
  change (upperStar Ab.{u + 1} p).map (q i) ≫
    (upperStarCompIso Ab.{u + 1} (pullback.condition (f := U.f i) (g := U.f j))).hom.app Q ≫
      (upperStar Ab.{u + 1} s).map (cokernel.π (q j)) = 0
  rw [← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp,
    cokernel.condition, Functor.map_zero, comp_zero]

end AlgebraicGeometry.ProEtale
