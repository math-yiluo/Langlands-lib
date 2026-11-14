import Langlands.GroupScheme.IntegralModel.Smoothening
import Langlands.GroupScheme.IntegralModel.Smoothening.Lift
import Langlands.GroupScheme.IntegralModel.Smoothening.Smoothness
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.GroupScheme.HopfMorphismBaseChange

/-! # The smoothening model

Let `R` be a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`, and `M` an integral model of a smooth affine group
`G` over `K`. With `A` the coordinate Hopf algebra of `M.group` and
`B = integralFunctions R K A`, the group scheme `Spec B` is a smoothening of `M`
as soon as `B` is finitely generated over `R`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.Smoothening

section SpecMap

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

theorem flat_specMap_iff :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔ Module.Flat R A := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]

theorem locallyOfFiniteType_specMap_iff :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      Algebra.FiniteType R A := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
    RingHom.finiteType_algebraMap]

theorem smooth_specMap_iff :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔ Algebra.Smooth R A := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
    RingHom.smooth_algebraMap]

end SpecMap

section Coordinates

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsAffineHom G.X.hom]

/-- A group scheme with affine structure morphism over an affine base is affine. -/
theorem isAffine_left : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

attribute [local instance] isAffine_left

/-- The coordinate Hopf algebra of a group scheme with affine structure morphism. -/
abbrev coord : Type u :=
  (AffineCoordinates.hopfAlgebra G : Type u)

/-- The Hopf spectrum of the coordinate algebra is the group scheme itself. -/
abbrev coordIso : specA R (coord G) ≅ G :=
  AffineCoordinates.hopfSpecIso G

instance isIso_coordIso_left : IsIso (coordIso G).hom.hom.hom.left :=
  (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (coordIso G))).hom)

theorem coordIso_w :
    (coordIso G).hom.hom.hom.left ≫ G.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (coord G))) :=
  Over.w (coordIso G).hom.hom.hom

instance flat_coord [Flat G.X.hom] : Module.Flat R (coord G) := by
  rw [← flat_specMap_iff, ← coordIso_w]
  have h1 : Flat (coordIso G).hom.hom.hom.left := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h1 ‹_›

instance finiteType_coord [LocallyOfFiniteType G.X.hom] : Algebra.FiniteType R (coord G) :=
  AffineCoordinates.algebraFiniteType G

end Coordinates

variable {R : Type u} [CommRing R] [IsDomain R] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}

attribute [local instance] isAffine_left

/-- The generic fibre of the coordinate algebra of an integral model of a smooth group is
smooth. -/
theorem smooth_generic_coord (M : IntegralModel R K G) [Smooth G.X.hom] :
    Algebra.Smooth K (K ⊗[R] coord M.group) := by
  let e := (HopfCoordinates.baseChangeSpecIso R K (coord M.group)).symm ≪≫
    (baseChange (Spec.algebraMap R K)).mapIso (coordIso M.group) ≪≫ M.genericIso
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  rw [← smooth_specMap_iff]
  have h : e.hom.hom.hom.left ≫ G.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] coord M.group))) :=
    Over.w e.hom.hom.hom
  rw [← h]
  have h1 : Smooth e.hom.hom.hom.left := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h1 ‹_›

section Model

variable [IsDiscreteValuationRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]

instance isAffineHom_specB : IsAffineHom (specB R K A).X.hom :=
  inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom
    (algebraMap R (integralFunctions R K A)))))

instance flat_specB : Flat (specB R K A).X.hom :=
  (flat_specMap_iff (R := R) (integralFunctions R K A)).2 inferInstance

instance locallyOfFiniteType_specB [Algebra.FiniteType R (integralFunctions R K A)] :
    LocallyOfFiniteType (specB R K A).X.hom :=
  (locallyOfFiniteType_specMap_iff (R := R) (integralFunctions R K A)).2 inferInstance

/-- After base change to `K`, `specInclHom` is an isomorphism. -/
instance isIso_baseChange_specInclHom :
    IsIso ((baseChange (Spec.algebraMap R K)).map (specInclHom R K A)) := by
  have hring : IsIso (CommRingCat.ofHom (genericMap R K A).toRingHom) :=
    (genericEquiv R K A).toRingEquiv.toCommRingCatIso.isIso_hom
  have h : IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (incl R K A)).op)).left) := by
    rw [HopfMorphismBaseChange.tensorSpecIso_naturality]
    exact inferInstanceAs (IsIso (_ ≫ Spec.map (CommRingCat.ofHom
      (genericMap R K A).toRingHom) ≫ _))
  let F := Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget (Spec (CommRingCat.of K))
  have : IsIso (F.map ((baseChange (Spec.algebraMap R K)).map (specInclHom R K A))) := h
  exact isIso_of_reflects_iso _ F

end Model

variable [IsDiscreteValuationRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]

/-- The homomorphism `Spec B → M.group`. -/
def smoothHom (M : IntegralModel R K G) : specB R K (coord M.group) ⟶ M.group :=
  specInclHom R K (coord M.group) ≫ (coordIso M.group).hom

instance isIso_baseChange_smoothHom (M : IntegralModel R K G) :
    IsIso ((baseChange (Spec.algebraMap R K)).map (smoothHom M)) := by
  rw [smoothHom, Functor.map_comp]
  infer_instance

/-- The smoothening model `Spec B` of `M`, for `B` the integral functions of the
coordinate algebra of `M.group`. -/
def smoothModel (M : IntegralModel R K G)
    [Algebra.FiniteType R (integralFunctions R K (coord M.group))] : IntegralModel R K G where
  group := specB R K (coord M.group)
  genericIso := asIso ((baseChange (Spec.algebraMap R K)).map (smoothHom M)) ≪≫ M.genericIso

/-- The model morphism `smoothModel M → M`, the identity on the generic group. -/
def smoothModelHom (M : IntegralModel R K G)
    [Algebra.FiniteType R (integralFunctions R K (coord M.group))] :
    (smoothModel M).Hom M (𝟙 G) where
  hom := smoothHom M
  generic_comm := by
    simp only [smoothModel, Iso.trans_hom, asIso_hom, Category.comp_id]

/-- `smoothModel M` is a smoothening of `M`, given smoothness of the generic group. -/
theorem isSmoothening_smoothModel (M : IntegralModel R K G) [Smooth G.X.hom]
    [Algebra.FiniteType R (integralFunctions R K (coord M.group))] :
    IsSmoothening M (smoothModel M) (smoothModelHom M) := by
  have : Algebra.Smooth K (K ⊗[R] coord M.group) := smooth_generic_coord M
  have hB : Algebra.Smooth R (integralFunctions R K (coord M.group)) := smooth_integralFunctions
  have hsmooth : Smooth (specB R K (coord M.group)).X.hom :=
    (smooth_specMap_iff (R := R) (integralFunctions R K (coord M.group))).2 hB
  let e := (Grp.forget _).mapIso (coordIso M.group)
  refine ⟨hsmooth, ?_, fun H hH f => ?_⟩
  · have : Smooth (Over.mk (𝟙 (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of R))))
    have h1 : Function.Bijective (fun g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
        (specB R K (coord M.group)).X => g ≫ (specInclHom R K (coord M.group)).hom.hom) :=
      bijective_comp_specIncl _
    have h2 : Function.Bijective (fun y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
        (specA R (coord M.group)).X => y ≫ e.hom) :=
      ⟨fun a b h => (cancel_mono e.hom).1 h,
        fun y => ⟨y ≫ e.inv, (Category.assoc _ _ _).trans
          ((congrArg (y ≫ ·) e.inv_hom_id).trans (Category.comp_id y))⟩⟩
    have h : ⇑(rationalPoints.map (smoothModelHom M).hom) =
        (fun y => y ≫ e.hom) ∘
          (fun g => g ≫ (specInclHom R K (coord M.group)).hom.hom) := by
      funext x
      exact (congrArg (x ≫ ·) (Grp.comp_hom_hom _ _)).trans (Category.assoc _ _ _).symm
    rw [h]
    exact h2.comp h1
  · obtain ⟨g, hg, huniq⟩ := existsUnique_lift (K := K) H (f ≫ (coordIso M.group).inv)
    refine ⟨g, ?_, fun f'' hf'' => huniq f'' ?_⟩
    · change g ≫ specInclHom R K (coord M.group) ≫ (coordIso M.group).hom = f
      rw [← Category.assoc, hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · have hf3 : (f'' ≫ specInclHom R K (coord M.group)) ≫ (coordIso M.group).hom = f :=
        (Category.assoc _ _ _).trans hf''
      exact (Iso.eq_comp_inv _).2 hf3

/-- Finite generation of the integral functions implies the existence of smoothenings. -/
theorem smoothening_of_finiteType (hfin : IntegralFunctionsFiniteTypeStatement.{u}) :
    SmootheningStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ G _ hG M
  have : Algebra.Smooth K (K ⊗[R] coord M.group) := smooth_generic_coord M
  have : Algebra.FiniteType R (integralFunctions R K (coord M.group)) :=
    hfin R K (coord M.group) this
  exact ⟨smoothModel M, smoothModelHom M, isSmoothening_smoothModel M⟩

end Langlands.GroupScheme.IntegralModel.Smoothening
