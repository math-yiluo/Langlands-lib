import Langlands.GroupScheme.Rational.SplitTorusEquivariantSection
import Langlands.GroupScheme.Rational.VectorExtensionDescent
import Langlands.GroupScheme.Rational.TorusVectorCocycle

/-! # Equivariant scheme sections for actions of arbitrary tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace EquivariantSectionDescent

open RelativeRoot

variable {k : Type u} [Field k]
    {D E H N : GroupScheme (Spec (CommRingCat.of k))}
    (cE : AutomorphicAction D E) (cH : AutomorphicAction D H) (cN : AutomorphicAction D N)
    (i : N ⟶ E) [Mono i.hom.hom] (q : E ⟶ H)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (g : T ⟶ E.X),
      cE.act t g ≫ q.hom.hom = cH.act t (g ≫ q.hom.hom))
    (hi : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (w : T ⟶ N.X),
      cE.act t (w ≫ i.hom.hom) = cN.act t w ≫ i.hom.hom)
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 _)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-! ### The equivariance defect -/

/-- The equivariance defect of the scheme section on the universal pair. -/
def actionDefectUniversal : D.X ⊗ H.X ⟶ E.X :=
  cE.act (fst D.X H.X) (snd D.X H.X ≫ s) *
    (cH.act (fst D.X H.X) (snd D.X H.X) ≫ s)⁻¹

omit [Mono i.hom.hom] in
include hker hq hs in
theorem actionDefectUniversal_mem :
    actionDefectUniversal cE cH s ∈ (SubgroupFunctor.range i).carrier (D.X ⊗ H.X) := by
  rw [hker, actionDefectUniversal, MonObj.mul_comp, GrpObj.inv_comp, hq]
  simp only [Category.assoc, hs, Category.comp_id, mul_inv_cancel]

/-- The equivariance defect, as an actual morphism to the kernel. -/
def kernelActionDefect : D.X ⊗ H.X ⟶ N.X :=
  Classical.choose (actionDefectUniversal_mem cE cH i q hker hq s hs)

omit [Mono i.hom.hom] in
theorem kernelActionDefect_comp :
    kernelActionDefect cE cH i q hker hq s hs ≫ i.hom.hom = actionDefectUniversal cE cH s :=
  Classical.choose_spec (actionDefectUniversal_mem cE cH i q hker hq s hs)

/-- The equivariance defect at a torus point and a point of the quotient. -/
def actionDefect {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ D.X) (x : T ⟶ H.X) :
    T ⟶ N.X :=
  lift t x ≫ kernelActionDefect cE cH i q hker hq s hs

local notation "δ" => actionDefect cE cH i q hker hq s hs

omit [Mono i.hom.hom] in
theorem actionDefect_comp {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ D.X)
    (x : T ⟶ H.X) :
    δ t x ≫ i.hom.hom = cE.act t (x ≫ s) * (cH.act t x ≫ s)⁻¹ := by
  rw [actionDefect, Category.assoc, kernelActionDefect_comp, actionDefectUniversal,
    MonObj.comp_mul, GrpObj.comp_inv, cE.naturality, ← Category.assoc, ← Category.assoc,
    cH.naturality, lift_fst, lift_snd]

omit [Mono i.hom.hom] in
theorem comp_actionDefect {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (t : T ⟶ D.X) (x : T ⟶ H.X) :
    b ≫ δ t x = δ (b ≫ t) (b ≫ x) := by
  rw [actionDefect, actionDefect, ← Category.assoc, comp_lift]

/-! ### Contraction of an equivariant correction -/

variable [IsAffineHom N.X.hom] (he : IsLinearVectorCoordinates cN e)
    (K : Type u) [Field K] [Algebra k K]
    (b : ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj N).X)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The linear equivariance equation `δ(t, x) + C(t · x) = t · C(x)` for a regular
vector-valued map `C` over the extension field, on all compatible extension algebras. -/
def IsEquivariantCorrection : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
      [IsScalarTower k K A] (t : Lie.AffinePoints D A) (x : Lie.AffinePoints H A),
      (vectorAffineCoordinates e A (δ t x)).toAdd +
        extendedMapCoordinates e K b (cH.act t x) =
      cN.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
        (extendedMapCoordinates e K b x)

omit [Mono i.hom.hom] in
/-- A linear equivariant correction over an extension field contracts to the same
equation over every original affine test algebra. -/
theorem contracted_equation
    (hb : IsEquivariantCorrection cE cH cN i q hker hq s hs e he K b)
    {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints D A) (x : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (δ t x)).toAdd +
      contractedMapCoordinates e K b (cH.act t x) =
    cN.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
      (contractedMapCoordinates e K b x) := by
  let f : A →ₐ[k] A ⊗[k] K := Algebra.TensorProduct.includeLeft
  have h := hb (A ⊗[k] K) (Lie.affineMap D f t) (Lie.affineMap H f x)
  have hc : δ (Lie.affineMap D f t) (Lie.affineMap H f x) =
      Lie.affineMap N f (δ t x) :=
    (comp_actionDefect cE cH i q hker hq s hs _ t x).symm
  have hx : cH.act (Lie.affineMap D f t) (Lie.affineMap H f x) =
      Lie.affineMap H f (cH.act t x) := by
    simp only [Lie.affineMap_apply, cH.naturality]
  rw [hc, he.1.vectorAffineCoordinates_naturality, hx] at h
  have h' := congrArg
    (fun z : Fin d → A ⊗[k] K =>
      fun j => VectorCocycleDescent.contract k K A (z j)) h
  simp only [Pi.add_apply, map_add] at h'
  change (fun j => VectorCocycleDescent.contract k K A
      (f ((vectorAffineCoordinates e A (δ t x)).toAdd j))) +
      contractedMapCoordinates e K b (cH.act t x) =
    (fun j => VectorCocycleDescent.contract k K A
      (cN.coordinateAction (finiteLieCoordinatesOfVector e he.1)
        (CommAlgCat.of k (A ⊗[k] K)) (Lie.affineMap D f t)
        (extendedMapCoordinates e K b (Lie.affineMap H f x)) j)) at h'
  rw [AutomorphicAction.coordinateAction_contract] at h'
  simp only [f, VectorCocycleDescent.contract_includeLeft] at h'
  exact h'

omit [Mono i.hom.hom] in
/-- The contracted vector correction measures the equivariance defect. -/
theorem contractedMapPoint_act
    (hb : IsEquivariantCorrection cE cH cN i q hker hq s hs e he K b)
    {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints D A) (x : Lie.AffinePoints H A) :
    contractedMapPoint e K b (cH.act t x) =
      (δ t x)⁻¹ * cN.act t (contractedMapPoint e K b x) := by
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
    contractedMapPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have h := contracted_equation cE cH cN i q hker hq s hs e he K b hb t x
  rw [he.coordinateAction_eq] at h
  exact eq_neg_add_of_add_eq h


/-! ### Comparison with an equivariant section over a field extension -/

/-- Actual affine points commute with pullback of an arbitrary scheme map. -/
private theorem affineBaseChangeEquiv_map
    {X Y : GroupScheme (Spec (CommRingCat.of k))} (f : X.X ⟶ Y.X)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj X) A) :
    Lie.affineBaseChangeEquiv k K Y A (x ≫ (Over.pullback (algebraBaseMap k K)).map f) =
      Lie.affineBaseChangeEquiv k K X A x ≫ f := by
  apply Over.OverMorphism.ext
  simp only [Lie.affineBaseChangeEquiv_left]
  change (x.left ≫ ((Over.pullback (algebraBaseMap k K)).map f).left) ≫ _ =
    (x.left ≫ _) ≫ f.left
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rfl

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
include hker in
/-- The kernel description of the quotient persists after field extension. -/
theorem mem_range_baseChange_iff (T : Over (Spec (CommRingCat.of K)))
    (g : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj E).X) :
    g ∈ (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i)).carrier
        T ↔
      g ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom = 1 := by
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange, hker,
    ← baseChangePointsEquiv_comp, MulEquiv.map_eq_one_iff]

include hq in
/-- The quotient map remains equivariant after field extension. -/
theorem baseChange_act_comp (T : Over (Spec (CommRingCat.of K)))
    (t : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj D).X)
    (g : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj E).X) :
    (cE.baseChange (algebraBaseMap k K)).act t g ≫
        ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom =
      (cH.baseChange (algebraBaseMap k K)).act t
        (g ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom) := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) H T).injective
  rw [baseChangePointsEquiv_comp, AutomorphicAction.baseChangePointsEquiv_act,
    AutomorphicAction.baseChangePointsEquiv_act, baseChangePointsEquiv_comp, hq]

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
include hi in
/-- The kernel inclusion remains equivariant after field extension. -/
theorem baseChange_act_inclusion (T : Over (Spec (CommRingCat.of K)))
    (t : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj D).X)
    (w : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj N).X) :
    (cE.baseChange (algebraBaseMap k K)).act t
        (w ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom) =
      (cN.baseChange (algebraBaseMap k K)).act t w ≫
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) E T).injective
  rw [AutomorphicAction.baseChangePointsEquiv_act, baseChangePointsEquiv_comp,
    baseChangePointsEquiv_comp, AutomorphicAction.baseChangePointsEquiv_act, hi]

include hs in
/-- The pulled-back scheme section remains a section of the pulled-back quotient. -/
theorem baseChangedSection_comp :
    VectorExtensionDescent.baseChangedSection s K ≫
      ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom = 𝟙 _ := by
  change (Over.pullback (algebraBaseMap k K)).map s ≫
    (Over.pullback (algebraBaseMap k K)).map q.hom.hom = 𝟙 _
  rw [← Functor.map_comp, hs, CategoryTheory.Functor.map_id]

variable (σ : ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj E).X)
    (hσ : σ ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom = 𝟙 _)
    (hσact : ∀ (T : Over (Spec (CommRingCat.of K)))
      (t : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj D).X)
      (x : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X),
      (cE.baseChange (algebraBaseMap k K)).act t (x ≫ σ) =
        (cH.baseChange (algebraBaseMap k K)).act t x ≫ σ)

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
include hker hs hσ in
private theorem exists_equivariantCorrection :
    ∃ c : ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj N).X,
      c ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom =
        VectorExtensionDescent.baseChangedSection s K * σ⁻¹ := by
  apply SubgroupFunctor.mem_range.1
  rw [mem_range_baseChange_iff i q hker K, MonObj.mul_comp, GrpObj.inv_comp,
    baseChangedSection_comp q s hs K, hσ, mul_inv_cancel]

/-- The vector correction comparing the original scheme section with an
equivariant section over the extension field. -/
def equivariantCorrection :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj N).X :=
  Classical.choose (exists_equivariantCorrection i q hker s hs K σ hσ)

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
theorem equivariantCorrection_comp :
    equivariantCorrection i q hker s hs K σ hσ ≫
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom =
      VectorExtensionDescent.baseChangedSection s K * σ⁻¹ :=
  Classical.choose_spec (exists_equivariantCorrection i q hker s hs K σ hσ)

/-- Values of the extension-field section, viewed as original points. -/
def sectionPoint {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] (x : Lie.AffinePoints H A) : Lie.AffinePoints E A :=
  Lie.affineBaseChangeEquiv k K E A ((Lie.affineBaseChangeEquiv k K H A).symm x ≫ σ)

include hσact in
/-- The values of an equivariant extension-field section are equivariant. -/
theorem act_sectionPoint {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] (t : Lie.AffinePoints D A) (x : Lie.AffinePoints H A) :
    cE.act t (sectionPoint K σ x) = sectionPoint K σ (cH.act t x) := by
  obtain ⟨t', rfl⟩ := (Lie.affineBaseChangeEquiv k K D A).surjective t
  obtain ⟨x', rfl⟩ := (Lie.affineBaseChangeEquiv k K H A).surjective x
  rw [sectionPoint, sectionPoint, MulEquiv.symm_apply_apply,
    ← affineBaseChangeEquiv_act, ← affineBaseChangeEquiv_act,
    MulEquiv.symm_apply_apply, hσact]

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
/-- The extended correction compares the original section with the extension
section. -/
theorem extendedCorrectionPoint_comp {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (x : Lie.AffinePoints H A) :
    VectorExtensionDescent.extendedMapPoint K (equivariantCorrection i q hker s hs K σ hσ) x ≫
        i.hom.hom =
      (x ≫ s) * (sectionPoint K σ x)⁻¹ := by
  rw [VectorExtensionDescent.extendedMapPoint, ← affineBaseChangeEquiv_map K i.hom.hom]
  change Lie.affineBaseChangeEquiv k K E A
    (((Lie.affineBaseChangeEquiv k K H A).symm x ≫
      equivariantCorrection i q hker s hs K σ hσ) ≫
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom) = _
  rw [Category.assoc, equivariantCorrection_comp, VectorExtensionDescent.baseChangedSection,
    MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv,
    affineBaseChangeEquiv_map, MulEquiv.apply_symm_apply]
  rfl

omit [IsAffineHom N.X.hom] in
include hi hσact in
/-- Comparison with an equivariant section produces the equivariance equation. -/
theorem extendedCorrectionPoint_act {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (t : Lie.AffinePoints D A)
    (x : Lie.AffinePoints H A) :
    VectorExtensionDescent.extendedMapPoint K (equivariantCorrection i q hker s hs K σ hσ)
        (cH.act t x) =
      (δ t x)⁻¹ * cN.act t
        (VectorExtensionDescent.extendedMapPoint K (equivariantCorrection i q hker s hs K σ hσ)
          x) := by
  apply (cancel_mono i.hom.hom).1
  rw [MonObj.mul_comp, GrpObj.inv_comp, ← hi, extendedCorrectionPoint_comp,
    extendedCorrectionPoint_comp, actionDefect_comp, cE.act_mul_right,
    AutomorphicAction.act_inv, act_sectionPoint cE cH K σ hσact]
  group

include hi hσact in
/-- The extracted correction satisfies the linear equivariance equation. -/
theorem equivariantCorrection_equation :
    IsEquivariantCorrection cE cH cN i q hker hq s hs e he K
      (equivariantCorrection i q hker s hs K σ hσ) := by
  intro A _ _ _ _ t x
  simp only [VectorExtensionDescent.extendedMapCoordinates_eq e K _ he.1]
  rw [he.coordinateAction_eq]
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [extendedCorrectionPoint_act cE cH cN i q hker hq hi s hs K σ hσ hσact]
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

variable [IsAffineHom H.X.hom]

/-- The original scheme section corrected by contracted vector coefficients. -/
def correctedSection : H.X ⟶ E.X :=
  (contractedMap e K b ≫ i.hom.hom)⁻¹ * s

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
include he in
theorem comp_correctedSection {A : Type u} [CommRing A] [Algebra k A]
    (x : Lie.AffinePoints H A) :
    x ≫ correctedSection i s e K b =
      (contractedMapPoint e K b x ≫ i.hom.hom)⁻¹ * (x ≫ s) := by
  rw [correctedSection, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, comp_contractedMap e K b he.1]

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
include hker hs in
/-- The corrected section remains a scheme section of the quotient. -/
theorem correctedSection_comp :
    correctedSection i s e K b ≫ q.hom.hom = 𝟙 H.X := by
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (hker _ _).1 (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  rw [correctedSection, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, hiq, MonObj.comp_one, inv_one, hs, one_mul]

variable (hb : IsEquivariantCorrection cE cH cN i q hker hq s hs e he K b)

omit [Mono i.hom.hom] in
include hi hb in
/-- The corrected section is equivariant on affine points. -/
theorem act_correctedSection_affine {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints D A) (x : Lie.AffinePoints H A) :
    cE.act t (x ≫ correctedSection i s e K b) =
      cH.act t x ≫ correctedSection i s e K b := by
  have hδ : cE.act t (x ≫ s) = (δ t x ≫ i.hom.hom) * (cH.act t x ≫ s) := by
    rw [actionDefect_comp, inv_mul_cancel_right]
  rw [comp_correctedSection cN i s e he K b, comp_correctedSection cN i s e he K b,
    cE.act_mul_right, AutomorphicAction.act_inv, hi, hδ,
    contractedMapPoint_act cE cH cN i q hker hq s hs e he K b hb,
    MonObj.mul_comp, GrpObj.inv_comp]
  group

omit [Mono i.hom.hom] in
include hi hb in
/-- The corrected section is equivariant on every relative test scheme. -/
theorem act_correctedSection [IsAffineHom D.X.hom] {T : Over (Spec (CommRingCat.of k))}
    (t : T ⟶ D.X) (x : T ⟶ H.X) :
    cE.act t (x ≫ correctedSection i s e K b) =
      cH.act t x ≫ correctedSection i s e K b := by
  have huniv : cE.act (fst D.X H.X) (snd D.X H.X ≫ correctedSection i s e K b) =
      cH.act (fst D.X H.X) (snd D.X H.X) ≫ correctedSection i s e K b := by
    apply PointedCoordinateWeights.affine_hom_ext
    intro A _ _ v
    rw [cE.naturality, ← Category.assoc, ← Category.assoc, cH.naturality]
    exact act_correctedSection_affine cE cH cN i q hker hq hi s hs e he K b hb _ _
  have h := congrArg (fun F => lift t x ≫ F) huniv
  rw [cE.naturality, ← Category.assoc, ← Category.assoc, cH.naturality, lift_fst,
    lift_snd] at h
  exact h

/-- Coefficient contraction of an equivariant section over a field extension. -/
def equivariantSectionOfBaseChange : H.X ⟶ E.X :=
  correctedSection i s e K (equivariantCorrection i q hker s hs K σ hσ)

omit [Mono i.hom.hom] [IsAffineHom N.X.hom] in
/-- The descended section is a scheme section of the quotient. -/
theorem equivariantSectionOfBaseChange_comp :
    equivariantSectionOfBaseChange i q hker s hs e K σ hσ ≫ q.hom.hom = 𝟙 H.X :=
  correctedSection_comp i q hker s hs e K _

include hq hi he hσact in
/-- The descended section is equivariant on every relative test scheme. -/
theorem act_equivariantSectionOfBaseChange [IsAffineHom D.X.hom]
    {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ D.X) (x : T ⟶ H.X) :
    cE.act t (x ≫ equivariantSectionOfBaseChange i q hker s hs e K σ hσ) =
      cH.act t x ≫ equivariantSectionOfBaseChange i q hker s hs e K σ hσ :=
  act_correctedSection cE cH cN i q hker hq hi s hs e he K _
    (equivariantCorrection_equation cE cH cN i q hker hq hi s hs e he K σ hσ hσact) t x

end EquivariantSectionDescent

section

open RelativeRoot

variable {k : Type u} [Field k]
    {D E H N : GroupScheme (Spec (CommRingCat.of k))} (hD : IsTorus D)
    [IsAffineHom H.X.hom] [IsAffineHom N.X.hom]
    (cE : AutomorphicAction D E) (cH : AutomorphicAction D H) (cN : AutomorphicAction D N)
    (i : N ⟶ E) [Mono i.hom.hom] (q : E ⟶ H)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (g : T ⟶ E.X),
      cE.act t g ≫ q.hom.hom = cH.act t (g ≫ q.hom.hom))
    (hi : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (w : T ⟶ N.X),
      cE.act t (w ≫ i.hom.hom) = cN.act t w ≫ i.hom.hom)
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 _) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates cN e)

include hD hker hq hi hs he in
/-- **Equivariant sections for arbitrary tori.** A torus acts compatibly on a group
scheme `E`, on a quotient `q : E ⟶ H` with affine `H`, and on its kernel `N`, an
affine vector group with linear coordinates. If `q` has a section as a morphism of
schemes, it has an equivariant one. -/
theorem IsTorus.exists_equivariantSection :
    ∃ σ : H.X ⟶ E.X, σ ≫ q.hom.hom = 𝟙 _ ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (x : T ⟶ H.X),
        cE.act t (x ≫ σ) = cH.act t x ≫ σ := by
  classical
  have : IsAffine D.X.left := SplittingAssembly.isAffine_of_isTorus D hD
  have : IsAffineHom D.X.hom := inferInstance
  obtain ⟨K, _, _, hDK⟩ := hD
  let bK := algebraBaseMap k K
  have : Mono ((GroupScheme.baseChange bK).map i).hom.hom :=
    Functor.map_mono (Over.pullback bK) i.hom.hom
  have : IsAffineHom ((GroupScheme.baseChange bK).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom bK)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange bK).obj N).X.hom := by
    change IsAffineHom (pullback.snd N.X.hom bK)
    infer_instance
  obtain ⟨σK, hσK, hσact⟩ := IsSplitTorus.exists_equivariantSection hDK
    (cE.baseChange bK) (cH.baseChange bK) (cN.baseChange bK)
    ((GroupScheme.baseChange bK).map i) ((GroupScheme.baseChange bK).map q)
    (EquivariantSectionDescent.mem_range_baseChange_iff i q hker K)
    (EquivariantSectionDescent.baseChange_act_comp cE cH q hq K)
    (EquivariantSectionDescent.baseChange_act_inclusion cE cN i hi K)
    (VectorExtensionDescent.baseChangedSection s K)
    (EquivariantSectionDescent.baseChangedSection_comp q s hs K)
    (vectorBaseChangeCoordinates e K) he.baseChange
  exact ⟨EquivariantSectionDescent.equivariantSectionOfBaseChange i q hker s hs e K σK hσK,
    EquivariantSectionDescent.equivariantSectionOfBaseChange_comp i q hker s hs e K σK hσK,
    fun T t x => EquivariantSectionDescent.act_equivariantSectionOfBaseChange cE cH cN i q
      hker hq hi s hs e he K σK hσK hσact t x⟩

/-- A chosen torus-equivariant scheme section of the quotient. -/
def IsTorus.equivariantSection : H.X ⟶ E.X :=
  Classical.choose (hD.exists_equivariantSection cE cH cN i q hker hq hi s hs e he)

/-- The chosen equivariant section is a scheme section of the quotient. -/
theorem IsTorus.equivariantSection_comp :
    hD.equivariantSection cE cH cN i q hker hq hi s hs e he ≫ q.hom.hom = 𝟙 H.X :=
  (Classical.choose_spec (hD.exists_equivariantSection cE cH cN i q hker hq hi s hs e he)).1

/-- The chosen section is equivariant on every relative test scheme. -/
theorem IsTorus.act_equivariantSection {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ D.X)
    (x : T ⟶ H.X) :
    cE.act t (x ≫ hD.equivariantSection cE cH cN i q hker hq hi s hs e he) =
      cH.act t x ≫ hD.equivariantSection cE cH cN i q hker hq hi s hs e he :=
  (Classical.choose_spec
    (hD.exists_equivariantSection cE cH cN i q hker hq hi s hs e he)).2 T t x

end

end Langlands.GroupScheme
