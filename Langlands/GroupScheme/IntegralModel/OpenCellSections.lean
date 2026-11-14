import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOpenContainment

/-! # Integral open-cell sections detected on the special fibre -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LocalOpenSections

variable (R : Type u) [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (x : Spec (CommRingCat.of R) ⟶ Y)

/-- An open set containing the image of the closed point contains the entire
image of the spectrum of a local ring. -/
theorem range_subset (h : x (IsLocalRing.closedPoint R) ∈ Set.range j) :
    Set.range x ⊆ Set.range j := by
  rintro _ ⟨z, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint z).map x.continuous).mem_open
    (IsOpenImmersion.isOpen_range j) h

/-- The actual factorization through an open immersion obtained from the image
of the closed point, as in KP Lemma 8.1.1. -/
def localOpenLift (h : x (IsLocalRing.closedPoint R) ∈ Set.range j) :
    Spec (CommRingCat.of R) ⟶ X :=
  IsOpenImmersion.lift j x (range_subset R j x h)

@[simp] theorem localOpenLift_fac
    (h : x (IsLocalRing.closedPoint R) ∈ Set.range j) :
    localOpenLift R j x h ≫ j = x :=
  IsOpenImmersion.lift_fac _ _ _

/-- Factoring a local-ring point through an open immersion is equivalent to
the closed point lying in its image. -/
theorem exists_lift_iff :
    (∃ y : Spec (CommRingCat.of R) ⟶ X, y ≫ j = x) ↔
      x (IsLocalRing.closedPoint R) ∈ Set.range j := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y (IsLocalRing.closedPoint R), rfl⟩
  · intro h
    exact ⟨localOpenLift R j x h, localOpenLift_fac R j x h⟩

variable {P Q : Over (Spec (CommRingCat.of R))}

/-- Sections of an open chart are exactly the original sections whose closed
point lies in the chart. The forward map is actual postcomposition. -/
def openSectionEquiv (c : P ⟶ Q) [IsOpenImmersion c.left] :
    (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ P) ≃
      {s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Q //
        s.left (IsLocalRing.closedPoint R) ∈ Set.range c.left} where
  toFun y := ⟨y ≫ c, ⟨y.left (IsLocalRing.closedPoint R), rfl⟩⟩
  invFun s := Over.homMk (localOpenLift R c.left s.val.left s.property) (by
    rw [← Over.w c, ← Category.assoc, localOpenLift_fac, Over.w s.val])
  left_inv y := by
    apply Over.OverMorphism.ext
    apply (cancel_mono c.left).mp
    exact localOpenLift_fac R c.left (y ≫ c).left
      ⟨y.left (IsLocalRing.closedPoint R), rfl⟩
  right_inv s := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact localOpenLift_fac R c.left s.val.left s.property

@[simp] theorem openSectionEquiv_val (c : P ⟶ Q) [IsOpenImmersion c.left]
    (y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ P) :
    (openSectionEquiv R c y).val = y ≫ c := rfl

end Langlands.AlgebraicGeometry.LocalOpenSections

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.LocalOpenSections

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G)
    {P : Over (Spec (CommRingCat.of R))}
    (j : P ⟶ M.group.X) [IsOpenImmersion j.left]

/-- An integral section belongs to an open chart exactly when its actual
reduction belongs to the base-changed chart. No lifting hypothesis on the
residue field or smoothness hypothesis is needed. -/
theorem section_lifts_iff_reduction_lifts (x : M.integralSections) :
    (∃ y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ P, y ≫ j = x) ↔
      ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))) ⟶
          (Over.pullback (residueBaseMap R)).obj P,
        z ≫ (Over.pullback (residueBaseMap R)).map j = M.reduction x := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : y.left ≫ j.left = x.left := congrArg (fun f => f.left) hy
    have hw : (residueBaseMap R ≫ y.left) ≫ P.hom = 𝟙 _ ≫ residueBaseMap R := by
      rw [Category.assoc, Over.w y]
      simp
    let z : Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))) ⟶
        (Over.pullback (residueBaseMap R)).obj P :=
      Over.homMk (pullback.lift (residueBaseMap R ≫ y.left) (𝟙 _) hw) (by simp)
    refine ⟨z, ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, M.reduction_left]
    change pullback.lift _ _ _ ≫
      pullback.lift (pullback.fst _ _ ≫ j.left) (pullback.snd _ _) _ = _
    apply pullback.hom_ext
    · simp [hy']
    · simp
  · rintro ⟨z, hz⟩
    have hz' := congrArg (fun f => f.left) hz
    have hprojection :
        z.left ≫ pullback.fst P.hom (residueBaseMap R) ≫ j.left =
          (M.reduction x).left ≫ M.specialFibreProjection := by
      rw [← hz']
      change _ = (z.left ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
      simp
    have hpoint : x.left (IsLocalRing.closedPoint R) ∈ Set.range j.left := by
      rw [← M.specialFibreProjection_reduction x]
      refine ⟨(z.left ≫ pullback.fst P.hom (residueBaseMap R))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)), ?_⟩
      exact congrArg
        (fun f => f (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) hprojection
    let y := (openSectionEquiv R j).symm ⟨x, hpoint⟩
    refine ⟨y, ?_⟩
    exact congrArg Subtype.val
      ((openSectionEquiv R j).apply_symm_apply ⟨x, hpoint⟩)

end Langlands.GroupScheme.IntegralModel
