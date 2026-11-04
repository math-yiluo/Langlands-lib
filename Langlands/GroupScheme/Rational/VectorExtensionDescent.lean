import Langlands.GroupScheme.Rational.VectorMapContraction
import Langlands.GroupScheme.Rational.QuotientHomCocycle
import Langlands.GroupScheme.Rational.PointedTensorWeights
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitTorusVectorExtension

/-! # Descent of sections of extensions by linear vector groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.VectorExtensionDescent

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {H E V : GroupScheme (Spec (CommRingCat.of k))}
    (n : V ⟶ E) (q : E ⟶ H)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 H.X)

/-- The multiplicativity defect of the supplied scheme section. -/
def sectionDefect : H.X ⊗ H.X ⟶ E.X :=
  (fst H.X H.X ≫ s) * (snd H.X H.X ≫ s) *
    ((fst H.X H.X * snd H.X H.X) ≫ s)⁻¹

include hn hs in
private theorem sectionDefect_mem :
    sectionDefect s ∈ (SubgroupFunctor.range n).carrier (H.X ⊗ H.X) := by
  rw [hn, mem_range_kernelι_iff, sectionDefect, MonObj.mul_comp,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc,
    Category.assoc, hs, Category.comp_id, Category.comp_id,
    Category.comp_id, mul_inv_cancel]

/-- The actual vector-kernel-valued defect morphism. -/
def kernelDefect : H.X ⊗ H.X ⟶ V.X :=
  Classical.choose (sectionDefect_mem n q hn s hs)

@[reassoc]
theorem kernelDefect_comp :
    kernelDefect n q hn s hs ≫ n.hom.hom = sectionDefect s :=
  Classical.choose_spec (sectionDefect_mem n q hn s hs)

/-- Evaluation of the actual kernel-valued defect. -/
def defect {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ H.X) : T ⟶ V.X :=
  lift t r ≫ kernelDefect n q hn s hs

theorem defect_comp {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ H.X) :
    defect n q hn s hs t r ≫ n.hom.hom =
      (t ≫ s) * (r ≫ s) * ((t * r) ≫ s)⁻¹ := by
  rw [defect, Category.assoc, kernelDefect_comp, sectionDefect,
    MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, lift_fst, ← Category.assoc, lift_snd,
    ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd]

theorem comp_defect {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (t r : T ⟶ H.X) :
    f ≫ defect n q hn s hs t r = defect n q hn s hs (f ≫ t) (f ≫ r) := by
  simp only [defect, ← Category.assoc, comp_lift]

variable [Mono n.hom.hom]

/-- Conjugation by the ambient group on its actual vector kernel. -/
def action : AutomorphicAction E V :=
  QuotientHomCocycle.action n q hn (𝟙 E)

theorem action_act_comp {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ E.X) (v : T ⟶ V.X) :
    (action n q hn).act g v ≫ n.hom.hom =
      g * (v ≫ n.hom.hom) * g⁻¹ := by
  simpa only [action, Grp.id_hom_hom, Category.comp_id] using
    QuotientHomCocycle.action_act_comp n q hn (𝟙 E) g v

variable [IsAffineHom V.X.hom] {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates (action n q hn) e)
    (K : Type u) [Field K] [Algebra k K]
    (b : ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The linear cochain equation over all compatible extension algebras. -/
def IsExtensionCorrection : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
      [IsScalarTower k K A] (t r : Lie.AffinePoints H A),
      (RelativeRoot.vectorAffineCoordinates e A (defect n q hn s hs t r)).toAdd +
        RelativeRoot.extendedMapCoordinates e K b (t * r) =
      (action n q hn).coordinateAction (RelativeRoot.finiteLieCoordinatesOfVector e he.1)
        (CommAlgCat.of k A) (t ≫ s) (RelativeRoot.extendedMapCoordinates e K b r) +
        RelativeRoot.extendedMapCoordinates e K b t

/-- A linear correction over an extension field contracts to the same defect
identity over every original affine test algebra. -/
theorem contracted_defect_equation
    (hb : IsExtensionCorrection n q hn s hs e he K b)
    {A : Type u} [CommRing A] [Algebra k A] (t r : Lie.AffinePoints H A) :
    (RelativeRoot.vectorAffineCoordinates e A (defect n q hn s hs t r)).toAdd +
      RelativeRoot.contractedMapCoordinates e K b (t * r) =
    (action n q hn).coordinateAction (RelativeRoot.finiteLieCoordinatesOfVector e he.1)
      (CommAlgCat.of k A) (t ≫ s) (RelativeRoot.contractedMapCoordinates e K b r) +
      RelativeRoot.contractedMapCoordinates e K b t := by
  let f : A →ₐ[k] A ⊗[k] K := Algebra.TensorProduct.includeLeft
  have h := hb (A ⊗[k] K) (Lie.affineMap H f t) (Lie.affineMap H f r)
  have hc : defect n q hn s hs (Lie.affineMap H f t) (Lie.affineMap H f r) =
      Lie.affineMap V f (defect n q hn s hs t r) :=
    (comp_defect n q hn s hs _ t r).symm
  have hts : Lie.affineMap H f t ≫ s = Lie.affineMap E f (t ≫ s) := by
    simp only [Lie.affineMap_apply, Category.assoc]
  rw [hc, he.1.vectorAffineCoordinates_naturality, ← map_mul, hts] at h
  have h' := congrArg
    (fun z : Fin d → A ⊗[k] K =>
      fun j => VectorCocycleDescent.contract k K A (z j)) h
  simp only [Pi.add_apply, map_add] at h'
  change (fun j => VectorCocycleDescent.contract k K A
      (f ((RelativeRoot.vectorAffineCoordinates e A (defect n q hn s hs t r)).toAdd j))) +
      RelativeRoot.contractedMapCoordinates e K b (t * r) =
    (fun j => VectorCocycleDescent.contract k K A
      ((action n q hn).coordinateAction (RelativeRoot.finiteLieCoordinatesOfVector e he.1)
        (CommAlgCat.of k (A ⊗[k] K)) (Lie.affineMap E f (t ≫ s))
        (RelativeRoot.extendedMapCoordinates e K b (Lie.affineMap H f r)) j)) +
      RelativeRoot.contractedMapCoordinates e K b t at h'
  rw [AutomorphicAction.coordinateAction_contract] at h'
  simp only [f, VectorCocycleDescent.contract_includeLeft] at h'
  exact h'

variable [IsAffineHom H.X.hom]

/-- The original scheme section corrected by contracted vector coefficients. -/
def correctedSectionHom : H.X ⟶ E.X :=
  (RelativeRoot.contractedMap e K b ≫ n.hom.hom)⁻¹ * s

omit [IsAffineHom V.X.hom] in
include he in
theorem comp_correctedSectionHom {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    t ≫ correctedSectionHom n s e K b =
      (RelativeRoot.contractedMapPoint e K b t ≫ n.hom.hom)⁻¹ * (t ≫ s) := by
  rw [correctedSectionHom, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, RelativeRoot.comp_contractedMap e K b he.1]

omit [Mono n.hom.hom] [IsAffineHom V.X.hom] in
include hn hs in
/-- The corrected section remains a scheme section of the quotient. -/
theorem correctedSectionHom_comp :
    correctedSectionHom n s e K b ≫ q.hom.hom = 𝟙 H.X := by
  have hnq : n.hom.hom ≫ q.hom.hom = 1 := by
    have hm : n.hom.hom ∈ (SubgroupFunctor.range n).carrier V.X :=
      SubgroupFunctor.mem_range.2 ⟨𝟙 V.X, Category.id_comp _⟩
    rw [hn, mem_range_kernelι_iff] at hm
    exact hm
  rw [correctedSectionHom, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, hnq, MonObj.comp_one, inv_one, hs, one_mul]


variable (hb : IsExtensionCorrection n q hn s hs e he K b)

omit [IsAffineHom H.X.hom] in
include hb in
/-- The contracted vector correction bounds the original multiplicativity defect. -/
theorem contractedMapPoint_mul {A : Type u} [CommRing A] [Algebra k A]
    (t r : Lie.AffinePoints H A) :
    RelativeRoot.contractedMapPoint e K b (t * r) =
      (defect n q hn s hs t r)⁻¹ *
        (action n q hn).act (t ≫ s) (RelativeRoot.contractedMapPoint e K b r) *
        RelativeRoot.contractedMapPoint e K b t := by
  apply (RelativeRoot.vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
    RelativeRoot.contractedMapPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have h := contracted_defect_equation n q hn s hs e he K b hb t r
  rw [he.coordinateAction_eq] at h
  exact (eq_neg_add_of_add_eq h).trans (add_assoc _ _ _).symm

include hb in
/-- The corrected scheme section preserves products on affine points. -/
theorem correctedSectionHom_mul_affine {A : Type u} [CommRing A] [Algebra k A]
    (t r : Lie.AffinePoints H A) :
    (t * r) ≫ correctedSectionHom n s e K b =
      (t ≫ correctedSectionHom n s e K b) * (r ≫ correctedSectionHom n s e K b) := by
  rw [comp_correctedSectionHom n q hn s e he K b,
    comp_correctedSectionHom n q hn s e he K b,
    comp_correctedSectionHom n q hn s e he K b,
    contractedMapPoint_mul n q hn s hs e he K b hb,
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    action_act_comp, defect_comp]
  group

include hb in
/-- The corrected scheme section preserves products on every relative test scheme. -/
theorem correctedSectionHom_mul {T : Over (Spec (CommRingCat.of k))}
    (t r : T ⟶ H.X) :
    (t * r) ≫ correctedSectionHom n s e K b =
      (t ≫ correctedSectionHom n s e K b) * (r ≫ correctedSectionHom n s e K b) := by
  have hu : (fst H.X H.X * snd H.X H.X) ≫ correctedSectionHom n s e K b =
      (fst H.X H.X ≫ correctedSectionHom n s e K b) *
        (snd H.X H.X ≫ correctedSectionHom n s e K b) := by
    apply PointedCoordinateWeights.affine_hom_ext
    intro A _ _ x
    simp only [← Category.assoc, MonObj.comp_mul,
      correctedSectionHom_mul_affine n q hn s hs e he K b hb]
  have htr : t * r = lift t r ≫ (fst H.X H.X * snd H.X H.X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [htr, Category.assoc, hu, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

/-- The actual group-scheme section constructed by coefficient contraction. -/
def extensionSectionOfCorrection : H ⟶ E :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ correctedSectionHom n s e K b)
    (correctedSectionHom_mul n q hn s hs e he K b hb))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The contracted group-scheme section splits the original quotient map. -/
theorem extensionSectionOfCorrection_comp :
    extensionSectionOfCorrection n q hn s hs e he K b hb ≫ q = 𝟙 H := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, extensionSectionOfCorrection, comp_homOfPoints,
    MonoidHom.mk'_apply, Category.assoc,
    correctedSectionHom_comp n q hn s hs e K b, Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]


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

omit [Mono n.hom.hom] [IsAffineHom V.X.hom] [IsAffineHom H.X.hom] in
include hn in
/-- The actual vector-kernel presentation remains exact after field extension. -/
theorem range_baseChange_kernel :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map n) =
      SubgroupFunctor.range (kernelι ((GroupScheme.baseChange (algebraBaseMap k K)).map q)) := by
  ext T x
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    hn, mem_range_kernelι_iff, mem_range_kernelι_iff,
    ← baseChangePointsEquiv_comp, MulEquiv.map_eq_one_iff]

variable (σ : (GroupScheme.baseChange (algebraBaseMap k K)).obj H ⟶
    (GroupScheme.baseChange (algebraBaseMap k K)).obj E)
    (hσ : σ ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map q =
      𝟙 ((GroupScheme.baseChange (algebraBaseMap k K)).obj H))

/-- The original scheme section pulled back to the extension field. -/
def baseChangedSection :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj E).X :=
  (Over.pullback (algebraBaseMap k K)).map s

omit [Mono n.hom.hom] [IsAffineHom V.X.hom] [IsAffineHom H.X.hom] in
include hn hs hσ in
private theorem exists_extensionCorrection :
    ∃ c : ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X,
      c ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map n).hom.hom =
        baseChangedSection s K * σ.hom.hom⁻¹ := by
  apply SubgroupFunctor.mem_range.1
  rw [range_baseChange_kernel n q hn K, mem_range_kernelι_iff,
    MonObj.mul_comp, GrpObj.inv_comp]
  have hsK : baseChangedSection s K ≫
      ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom = 𝟙 _ := by
    change (Over.pullback (algebraBaseMap k K)).map s ≫
      (Over.pullback (algebraBaseMap k K)).map q.hom.hom = 𝟙 _
    rw [← Functor.map_comp, hs, CategoryTheory.Functor.map_id]
  have hσK : σ.hom.hom ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map q).hom.hom =
      𝟙 _ := by
    rw [← Grp.comp_hom_hom, hσ, Grp.id_hom_hom]
  rw [hsK, hσK, mul_inv_cancel]

/-- The actual vector correction obtained by comparing the original scheme
section with a group section over the extension field. -/
def extensionCorrection :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X :=
  Classical.choose (exists_extensionCorrection n q hn s hs K σ hσ)

@[reassoc]
theorem extensionCorrection_comp :
    extensionCorrection n q hn s hs K σ hσ ≫
        ((GroupScheme.baseChange (algebraBaseMap k K)).map n).hom.hom =
      baseChangedSection s K * σ.hom.hom⁻¹ :=
  Classical.choose_spec (exists_extensionCorrection n q hn s hs K σ hσ)

/-- Extension group-section values viewed on the original group over an
extension test algebra. -/
def extensionSectionPoint {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] (t : Lie.AffinePoints H A) : Lie.AffinePoints E A :=
  Lie.affineBaseChangeEquiv k K E A
    ((Lie.affineBaseChangeEquiv k K H A).symm t ≫ σ.hom.hom)

omit [IsAffineHom H.X.hom] in
theorem extensionSectionPoint_mul {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (t r : Lie.AffinePoints H A) :
    extensionSectionPoint K σ (t * r) =
      extensionSectionPoint K σ t * extensionSectionPoint K σ r := by
  simp only [extensionSectionPoint, map_mul, MonObj.mul_comp]

/-- A regular extension-field vector map viewed as original vector points. -/
def extendedMapPoint {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] (t : Lie.AffinePoints H A) : Lie.AffinePoints V A :=
  Lie.affineBaseChangeEquiv k K V A ((Lie.affineBaseChangeEquiv k K H A).symm t ≫ b)

omit [IsAffineHom V.X.hom] [IsAffineHom H.X.hom] in
theorem extendedMapCoordinates_eq (h : RelativeRoot.IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (t : Lie.AffinePoints H A) :
    RelativeRoot.extendedMapCoordinates e K b t =
      (RelativeRoot.vectorAffineCoordinates e A (extendedMapPoint K b t)).toAdd := by
  rw [RelativeRoot.extendedMapCoordinates, RelativeRoot.vectorAffineCoordinates_baseChange h]
  rfl

theorem extendedCorrectionPoint_comp {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (t : Lie.AffinePoints H A) :
    extendedMapPoint K (extensionCorrection n q hn s hs K σ hσ) t ≫ n.hom.hom =
      (t ≫ s) * (extensionSectionPoint K σ t)⁻¹ := by
  rw [extendedMapPoint, ← affineBaseChangeEquiv_map K n.hom.hom]
  change Lie.affineBaseChangeEquiv k K E A
    (((Lie.affineBaseChangeEquiv k K H A).symm t ≫
      extensionCorrection n q hn s hs K σ hσ) ≫
      ((GroupScheme.baseChange (algebraBaseMap k K)).map n).hom.hom) = _
  rw [Category.assoc, extensionCorrection_comp, baseChangedSection,
    MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv,
    affineBaseChangeEquiv_map, MulEquiv.apply_symm_apply]
  rfl

/-- Comparison with a group section produces the vector cochain identity. -/
theorem extendedCorrectionPoint_mul {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (t r : Lie.AffinePoints H A) :
    extendedMapPoint K (extensionCorrection n q hn s hs K σ hσ) (t * r) =
      (defect n q hn s hs t r)⁻¹ *
        (action n q hn).act (t ≫ s)
          (extendedMapPoint K (extensionCorrection n q hn s hs K σ hσ) r) *
        extendedMapPoint K (extensionCorrection n q hn s hs K σ hσ) t := by
  apply (cancel_mono n.hom.hom).1
  simp only [MonObj.mul_comp, GrpObj.inv_comp, action_act_comp, defect_comp,
    extendedCorrectionPoint_comp, extensionSectionPoint_mul]
  group

include he in
/-- The extracted extension correction satisfies the required linear equation. -/
theorem extensionCorrection_equation :
    IsExtensionCorrection n q hn s hs e he K (extensionCorrection n q hn s hs K σ hσ) := by
  intro A _ _ _ _ t r
  simp only [extendedMapCoordinates_eq e K _ he.1]
  rw [he.coordinateAction_eq]
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have h := congrArg (fun x : Lie.AffinePoints V A =>
      (RelativeRoot.vectorAffineCoordinates e A x).toAdd)
    (extendedCorrectionPoint_mul n q hn s hs K σ hσ t r)
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv] at h
  rw [h]
  abel

/-- Coefficient contraction descends a group-scheme section over any field
extension when an original scheme section and linear vector kernel are supplied. -/
def extensionSectionOfBaseChange : H ⟶ E :=
  extensionSectionOfCorrection n q hn s hs e he K
    (extensionCorrection n q hn s hs K σ hσ)
    (extensionCorrection_equation n q hn s hs e he K σ hσ)

/-- The descended section splits the original quotient homomorphism. -/
theorem extensionSectionOfBaseChange_comp :
    extensionSectionOfBaseChange n q hn s hs e he K σ hσ ≫ q = 𝟙 H :=
  extensionSectionOfCorrection_comp n q hn s hs e he K
    (extensionCorrection n q hn s hs K σ hσ)
    (extensionCorrection_equation n q hn s hs e he K σ hσ)

end Langlands.GroupScheme.VectorExtensionDescent
