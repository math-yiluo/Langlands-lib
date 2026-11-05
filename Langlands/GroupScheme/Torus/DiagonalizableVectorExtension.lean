import Langlands.GroupScheme.Torus.DiagonalizableAveraging
import Langlands.GroupScheme.Rational.SplitTorusVectorExtension

/-! # Group sections of diagonalizable extensions by linear vector groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableVectorExtension
open RelativeRoot PointedCoordinateWeights
open splitTorus (conj conj_act_comp)

variable {k : Type u} [Field k] (Λ : Type u) [AddCommGroup Λ]
    {E N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom N.X.hom]
    (i : N ⟶ E) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range (𝟙 E)))
    (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (s : ((Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp).X ⟶ E.X)
    (hs : s ≫ q.hom.hom = 𝟙 _)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

local notation "𝔻" => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)

/-- The defect of the scheme section on the universal pair of diagonalizable points. -/
def sectionDefect : (𝔻).X ⊗ (𝔻).X ⟶ E.X :=
  (fst (𝔻).X (𝔻).X ≫ s) * (snd (𝔻).X (𝔻).X ≫ s) * ((fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ s)⁻¹

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
include hker hs in
theorem sectionDefect_mem :
    sectionDefect Λ s ∈ (SubgroupFunctor.range i).carrier ((𝔻).X ⊗ (𝔻).X) := by
  rw [hker, sectionDefect, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, Category.assoc, Category.assoc, hs, Category.comp_id,
    Category.comp_id, Category.comp_id, mul_inv_cancel]

/-- The defect of the scheme section, as an actual morphism to the kernel. -/
def kernelDefect : (𝔻).X ⊗ (𝔻).X ⟶ N.X :=
  Classical.choose (sectionDefect_mem Λ i q hker s hs)

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem kernelDefect_comp : kernelDefect Λ i q hker s hs ≫ i.hom.hom = sectionDefect Λ s :=
  Classical.choose_spec (sectionDefect_mem Λ i q hker s hs)

/-- The section defect at a pair of points. -/
def defect {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) : T ⟶ N.X :=
  lift t r ≫ kernelDefect Λ i q hker s hs

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem defect_comp {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) :
    defect Λ i q hker s hs t r ≫ i.hom.hom = (t ≫ s) * (r ≫ s) * ((t * r) ≫ s)⁻¹ := by
  rw [defect, Category.assoc, kernelDefect_comp, sectionDefect, MonObj.comp_mul,
    MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_snd, MonObj.comp_mul, lift_fst, lift_snd]

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem comp_defect {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (t r : T ⟶ (𝔻).X) :
    b ≫ defect Λ i q hker s hs t r = defect Λ i q hker s hs (b ≫ t) (b ≫ r) := by
  rw [defect, defect, ← Category.assoc, comp_lift]

omit [IsAffineHom N.X.hom] in
/-- The defect is a Hochschild two-cocycle for the conjugation action. -/
theorem defect_cocycle {T : Over (Spec (CommRingCat.of k))} (t r w : T ⟶ (𝔻).X) :
    defect Λ i q hker s hs t r * defect Λ i q hker s hs (t * r) w =
      (conj i hn).act (t ≫ s) (defect Λ i q hker s hs r w) *
        defect Λ i q hker s hs t (r * w) := by
  apply (cancel_mono i.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp, conj_act_comp, defect_comp, defect_comp,
    defect_comp, defect_comp, mul_assoc t r w]
  group

/-! ### Averaging the defect over the diagonalizable group -/

section Averaging

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The inclusion of coefficients into group algebras. -/
abbrev coefficientInclusion (A : Type u) [CommRing A] [Algebra k A] :
    A →ₐ[k] AddMonoidAlgebra A Λ :=
  IsScalarTower.toAlgHom k A (AddMonoidAlgebra A Λ)

/-- Extension of scalars of the universal group algebras. -/
abbrev scalarExtension (A : Type u) [CommRing A] [Algebra k A] :
    AddMonoidAlgebra k Λ →ₐ[k] AddMonoidAlgebra A Λ :=
  AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId k A)

/-- The universal diagonalizable point over group algebras with coefficients in `A`. -/
abbrev averagingPoint (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints (𝔻) (AddMonoidAlgebra A Λ) :=
  Lie.affineMap _ (scalarExtension Λ A) (Diagonalizable.Averaging.universalPoint (CommRingCat.of k) Λ)

local notation "δ" => defect Λ i q hker s hs

/-- The degree-zero group-algebra coefficient of the defect against the universal point:
the average of `defect t r` over the diagonalizable group point `r`. -/
def averageVector (t : Lie.AffinePoints (𝔻) A) : Fin d → A :=
  fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
    (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (averagingPoint Λ A))).toAdd j).coeff 0

/-- The averaged defect, as an actual point of the vector group. -/
def averagePoint (t : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints N A :=
  (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (averageVector Λ i q hker s hs e t))

local notation "β" => averageVector Λ i q hker s hs e
local notation "ρ" => averagePoint Λ i q hker s hs e

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem averagePoint_coordinates (t : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (ρ t)).toAdd = β t := by
  rw [averagePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- Applying a coefficient map to an actual defect. -/
theorem affineMap_defect {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t r : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap N φ (δ t r) = δ (Lie.affineMap _ φ t) (Lie.affineMap _ φ r) :=
  comp_defect Λ i q hker s hs _ t r

/-- The scheme section corrected by the averaged defect. -/
def sectionPoint (t : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints E A :=
  (ρ t ≫ i.hom.hom)⁻¹ * (t ≫ s)

local notation "σ" => sectionPoint Λ i q hker s hs e

/-- The corrected section as a morphism of schemes. -/
def sectionHom : (𝔻).X ⟶ E.X :=
  homOfAffinePoints fun _ _ _ t => σ t

variable (he : IsLinearVectorCoordinates (conj i hn) e)
include he

omit [IsAffineHom N.X.hom] in
/-- The average is invariant under translation of the averaging variable. -/
theorem averageVector_translate (t r : Lie.AffinePoints (𝔻) A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t)
        (Lie.affineMap _ (coefficientInclusion Λ A) r * averagingPoint Λ A))).toAdd j).coeff 0) =
      β t := by
  let τ := (Diagonalizable.Averaging.translation Λ (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A r)).restrictScalars k
  rw [← Diagonalizable.Averaging.translation_point (CommRingCat.of k), ← Diagonalizable.Averaging.translation_const (CommRingCat.of k) Λ
    (Diagonalizable.Averaging.pointsEquiv (CommRingCat.of k) Λ A r) t, ← affineMap_defect, he.1.vectorAffineCoordinates_naturality]
  funext j
  exact Diagonalizable.Averaging.coeff_zero_translation Λ _ _

omit [IsAffineHom N.X.hom] in
/-- Constant group-algebra coefficients of a constant point. -/
theorem coeff_zero_coefficientInclusion (x : Lie.AffinePoints N A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (Lie.affineMap N (coefficientInclusion Λ A) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A x).toAdd := by
  rw [he.1.vectorAffineCoordinates_naturality]
  funext j
  change (AddMonoidAlgebra.single 0 _).coeff 0 = _
  simp

/-- Constant group-algebra coefficients of the action of a constant point. -/
theorem coeff_zero_act (h : Lie.AffinePoints E A)
    (x : Lie.AffinePoints N (AddMonoidAlgebra A Λ)) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      ((conj i hn).act (Lie.affineMap E (coefficientInclusion Λ A) h) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A ((conj i hn).act h ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (fun j =>
          ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd j).coeff 0))))).toAdd := by
  have hx := he.coordinateAction_eq (CommAlgCat.of k (AddMonoidAlgebra A Λ))
    (Lie.affineMap E (coefficientInclusion Λ A) h)
    (vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hx
  rw [← hx, (conj i hn).coordinateAction_coeff, he.coordinateAction_eq]

/-- The averaged defect bounds the defect: the Hochschild two-cocycle is the
coboundary of the average. -/
theorem defect_add_averageVector (t r : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) =
      (vectorAffineCoordinates e A ((conj i hn).act (t ≫ s) (ρ r))).toAdd + β t := by
  have hc := congrArg (fun x : Lie.AffinePoints N (AddMonoidAlgebra A Λ) =>
      fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ) x).toAdd j).coeff 0)
    (defect_cocycle Λ i hn q hker s hs (Lie.affineMap _ (coefficientInclusion Λ A) t)
      (Lie.affineMap _ (coefficientInclusion Λ A) r) (averagingPoint Λ A))
  simp only [map_mul, toAdd_mul] at hc
  have h1 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (Lie.affineMap _ (coefficientInclusion Λ A) r))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t * Lie.affineMap _ (coefficientInclusion Λ A) r)
        (averagingPoint Λ A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) := by
    rw [← affineMap_defect, ← map_mul]
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (fun a b : A => a + b) (congrFun (coeff_zero_coefficientInclusion Λ i hn e he _) j) rfl
  have h2 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      ((conj i hn).act (Lie.affineMap _ (coefficientInclusion Λ A) t ≫ s)
        (δ (Lie.affineMap _ (coefficientInclusion Λ A) r) (averagingPoint Λ A)))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A Λ)
      (δ (Lie.affineMap _ (coefficientInclusion Λ A) t)
        (Lie.affineMap _ (coefficientInclusion Λ A) r * averagingPoint Λ A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A ((conj i hn).act (t ≫ s) (ρ r))).toAdd + β t := by
    have hts : Lie.affineMap _ (coefficientInclusion Λ A) t ≫ s =
        Lie.affineMap E (coefficientInclusion Λ A) (t ≫ s) := by
      simp only [Lie.affineMap_apply, Category.assoc]
    rw [hts]
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (· + ·)
      (congrFun (coeff_zero_act Λ i hn e he _ _) j)
      (congrFun (averageVector_translate Λ i hn q hker s hs e he t r) j)
  rw [← h1, ← h2]
  exact hc

/-- The averaged defect corrects the multiplicativity defect of the section. -/
theorem averagePoint_mul (t r : Lie.AffinePoints (𝔻) A) :
    ρ (t * r) = (δ t r)⁻¹ * (conj i hn).act (t ≫ s) (ρ r) * ρ t := by
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, averagePoint_coordinates]
  exact (eq_neg_add_of_add_eq (defect_add_averageVector Λ i hn q hker s hs e he t r)).trans
    (add_assoc _ _ _).symm

/-- The corrected section is multiplicative on affine points. -/
theorem sectionPoint_mul (t r : Lie.AffinePoints (𝔻) A) : σ (t * r) = σ t * σ r := by
  simp only [sectionPoint]
  rw [averagePoint_mul Λ i hn q hker s hs e he, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, conj_act_comp, defect_comp]
  group

omit [IsAffineHom N.X.hom] in
/-- The average commutes with extension of coefficients. -/
theorem averageVector_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    β (Lie.affineMap _ φ t) = fun j => φ (β t j) := by
  have hc : (AddMonoidAlgebra.mapAlgHom Λ φ).comp (coefficientInclusion Λ A) =
      (coefficientInclusion Λ B).comp φ := by
    ext a
    simp [coefficientInclusion, AddMonoidAlgebra.coe_algebraMap]
  have hl : (AddMonoidAlgebra.mapAlgHom Λ φ).comp (scalarExtension Λ A) =
      scalarExtension Λ B := by
    rw [scalarExtension, scalarExtension, ← AddMonoidAlgebra.mapRangeAlgHom_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have hd : δ (Lie.affineMap _ (coefficientInclusion Λ B) (Lie.affineMap _ φ t)) (averagingPoint Λ B) =
      Lie.affineMap N (AddMonoidAlgebra.mapAlgHom Λ φ)
        (δ (Lie.affineMap _ (coefficientInclusion Λ A) t) (averagingPoint Λ A)) := by
    rw [affineMap_defect, averagingPoint, averagingPoint, ← Lie.affineMap_comp,
      ← Lie.affineMap_comp, ← Lie.affineMap_comp, hc, hl]
  funext j
  simp only [averageVector]
  rw [hd, he.1.vectorAffineCoordinates_naturality]
  exact AddMonoidAlgebra.coeff_mapAlgHom _ _ _

omit [IsAffineHom N.X.hom] in
/-- The averaged point commutes with extension of coefficients. -/
theorem averagePoint_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap N φ (ρ t) = ρ (Lie.affineMap _ φ t) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.1.vectorAffineCoordinates_naturality, averagePoint_coordinates,
    averagePoint_coordinates, averageVector_naturality Λ i hn q hker s hs e he]

omit [IsAffineHom N.X.hom] in
/-- The corrected section commutes with extension of coefficients. -/
theorem sectionPoint_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap E φ (σ t) = σ (Lie.affineMap _ φ t) := by
  rw [sectionPoint, sectionPoint, map_mul, map_inv,
    ← averagePoint_naturality Λ i hn q hker s hs e he]
  simp only [Lie.affineMap_apply, Category.assoc]

omit [IsAffineHom N.X.hom] in
/-- The morphism of the corrected section on affine points. -/
theorem comp_sectionHom (t : Lie.AffinePoints (𝔻) A) :
    t ≫ sectionHom Λ i q hker s hs e = σ t :=
  comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => sectionPoint_naturality Λ i hn q hker s hs e he f v) t

/-- The corrected section is multiplicative on the universal pair of points. -/
theorem sectionHom_mul_universal :
    (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ sectionHom Λ i q hker s hs e =
      (fst (𝔻).X (𝔻).X ≫ sectionHom Λ i q hker s hs e) *
        (snd (𝔻).X (𝔻).X ≫ sectionHom Λ i q hker s hs e) := by
  apply affine_hom_ext
  intro A _ _ v
  simp only [← Category.assoc, MonObj.comp_mul, comp_sectionHom Λ i hn q hker s hs e he,
    sectionPoint_mul Λ i hn q hker s hs e he]

/-- The corrected section is multiplicative on all points. -/
theorem sectionHom_mul {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ (𝔻).X) :
    (x * y) ≫ sectionHom Λ i q hker s hs e =
      (x ≫ sectionHom Λ i q hker s hs e) * (y ≫ sectionHom Λ i q hker s hs e) := by
  have hxy : x * y = lift x y ≫ (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hxy, Category.assoc, sectionHom_mul_universal Λ i hn q hker s hs e he, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

omit [IsAffineHom N.X.hom] in
/-- The corrected section is a section of the quotient map on schemes. -/
theorem sectionHom_comp : sectionHom Λ i q hker s hs e ≫ q.hom.hom = 𝟙 (𝔻).X := by
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (hker _ _).1 (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  apply affine_hom_ext
  intro A _ _ t
  rw [← Category.assoc, comp_sectionHom Λ i hn q hker s hs e he, sectionPoint, MonObj.mul_comp,
    GrpObj.inv_comp, Category.assoc, Category.assoc, hs, hiq, MonObj.comp_one, inv_one,
    one_mul, Category.comp_id]

/-- The group-scheme section of a diagonalizable extension by a linear vector group. -/
def extensionSection : 𝔻 ⟶ E :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ sectionHom Λ i q hker s hs e)
    (sectionHom_mul Λ i hn q hker s hs e he))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The group-scheme section splits the quotient map. -/
theorem extensionSection_comp : extensionSection Λ i hn q hker s hs e he ≫ q = 𝟙 𝔻 := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, extensionSection, comp_homOfPoints,
    MonoidHom.mk'_apply,
    Category.assoc, sectionHom_comp Λ i hn q hker s hs e he, Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

include hker hs in
/-- A diagonalizable extension by a linear vector group with a scheme section splits. -/
theorem exists_extensionSection : ∃ φ : 𝔻 ⟶ E, φ ≫ q = 𝟙 𝔻 :=
  ⟨_, extensionSection_comp Λ i hn q hker s hs e he⟩

end Averaging

end Langlands.GroupScheme.diagonalizableVectorExtension
