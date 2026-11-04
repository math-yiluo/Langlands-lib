import Langlands.GroupScheme.Rational.NaturalAdditiveCocycle
import Langlands.GroupScheme.Rational.AffineVectorExtension

/-! # Group sections of commutative extensions over the additive group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CommutativeAdditiveExtension

open RelativeRoot VectorExtensionDescent

set_option backward.isDefEq.respectTransparency false

private theorem commutative_defect_identity {G : Type*} [CommGroup G]
    (a b c d e f : G) :
    a * b * c⁻¹ * d * e * a⁻¹ = d * f * c⁻¹ * e * b * f⁻¹ := by
  calc
    _ = (a * a⁻¹) * (b * c⁻¹ * d * e) := by ac_rfl
    _ = (f * f⁻¹) * (b * c⁻¹ * d * e) := by simp
    _ = _ := by ac_rfl

private theorem commutative_correction_identity {G : Type*} [CommGroup G]
    (a b c x y : G) :
    (a * b * c⁻¹ * x * y) * c = (x * a) * (y * b) := by
  calc
    _ = (c⁻¹ * c) * ((x * a) * (y * b)) := by ac_rfl
    _ = _ := by simp

section AdditivePoints

variable {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (eH : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ H.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))

/-- The point of the one-dimensional quotient with specified additive coordinate. -/
def additivePoint (A : Type u) [CommRing A] [Algebra k A] (x : A) :
    Lie.AffinePoints H A :=
  (vectorAffineCoordinates eH A).symm (Multiplicative.ofAdd fun _ => x)

theorem additivePoint_add {A : Type u} [CommRing A] [Algebra k A] (x y : A) :
    additivePoint eH A (x + y) = additivePoint eH A x * additivePoint eH A y := by
  apply (vectorAffineCoordinates eH A).injective
  simp only [additivePoint, map_mul, MulEquiv.apply_symm_apply]
  rfl

theorem additivePoint_coordinate {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    additivePoint eH A ((vectorAffineCoordinates eH A t).toAdd 0) = t := by
  apply (vectorAffineCoordinates eH A).injective
  rw [additivePoint, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  funext i
  exact congrArg ((vectorAffineCoordinates eH A t).toAdd) (Subsingleton.elim 0 i)

theorem additivePoint_map (heH : IsNaturalVectorCoordinates eH)
    {A D : Type u} [CommRing A] [Algebra k A] [CommRing D] [Algebra k D]
    (f : A →ₐ[k] D) (x : A) :
    Lie.affineMap H f (additivePoint eH A x) = additivePoint eH D (f x) := by
  apply (vectorAffineCoordinates eH D).injective
  apply Multiplicative.toAdd.injective
  rw [heH.vectorAffineCoordinates_naturality]
  simp only [additivePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

end AdditivePoints

section Section

variable {k : Type u} [Field k]
    {E K H : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj E.X]
    (j : K ⟶ E) [Mono j.hom.hom] (q : E ⟶ H)
    (hn : SubgroupFunctor.range j = SubgroupFunctor.range (kernelι q))
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 H.X) {d : ℕ}
    (eK : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ K.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (heK : IsNaturalVectorCoordinates eK)
    (eH : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ H.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))
    (heH : IsNaturalVectorCoordinates eH)

/-- Each coordinate of the section defect as a scalar family. -/
def scalarDefect (i : Fin d) : NaturalAdditiveCocycle.ScalarFamily (k := k) :=
  fun A _ _ x y => (vectorAffineCoordinates eK A
    (defect j q hn s hs (additivePoint eH A x) (additivePoint eH A y))).toAdd i

omit [IsCommMonObj E.X] [Mono j.hom.hom] in
include heK heH in
/-- Every scalar coordinate of the defect is natural under coefficient maps. -/
theorem scalarDefect_natural (i : Fin d) :
    NaturalAdditiveCocycle.IsNatural (scalarDefect j q hn s hs eK eH i) := by
  intro A D _ _ _ _ f x y
  have hd : defect j q hn s hs (Lie.affineMap H f (additivePoint eH A x))
      (Lie.affineMap H f (additivePoint eH A y)) =
      Lie.affineMap K f
        (defect j q hn s hs (additivePoint eH A x) (additivePoint eH A y)) :=
    (comp_defect j q hn s hs _ _ _).symm
  rw [additivePoint_map eH heH, additivePoint_map eH heH] at hd
  simp only [scalarDefect, hd, heK.vectorAffineCoordinates_naturality]

include j q hn s hs eK eH in
/-- In a commutative extension the scalar defect obeys the additive cocycle law. -/
theorem scalarDefect_isCocycle (i : Fin d) :
    NaturalAdditiveCocycle.IsCocycle (scalarDefect j q hn s hs eK eH i) := by
  intro A _ _ x y z
  have hd :
      defect j q hn s hs (additivePoint eH A (x + y)) (additivePoint eH A z) *
        defect j q hn s hs (additivePoint eH A x) (additivePoint eH A y) =
      defect j q hn s hs (additivePoint eH A x) (additivePoint eH A (y + z)) *
        defect j q hn s hs (additivePoint eH A y) (additivePoint eH A z) := by
    rw [additivePoint_add, additivePoint_add]
    apply (cancel_mono j.hom.hom).mp
    simp only [MonObj.mul_comp, defect_comp, mul_assoc]
    simpa only [mul_assoc] using commutative_defect_identity
      ((additivePoint eH A x * additivePoint eH A y) ≫ s)
      (additivePoint eH A z ≫ s)
      ((additivePoint eH A x * additivePoint eH A y * additivePoint eH A z) ≫ s)
      (additivePoint eH A x ≫ s) (additivePoint eH A y ≫ s)
      ((additivePoint eH A y * additivePoint eH A z) ≫ s)
  have h := congrArg (fun v : Lie.AffinePoints K A =>
    (vectorAffineCoordinates eK A v).toAdd i) hd
  simpa only [scalarDefect, map_mul, toAdd_mul, Pi.add_apply] using h

variable [CharZero k]

/-- A polynomial primitive for each coordinate of the section defect. -/
def correctionPolynomial (i : Fin d) : k[X] :=
  NaturalAdditiveCocycle.coboundaryPolynomial
    (scalarDefect_natural j q hn s hs eK heK eH heH i)
    (scalarDefect_isCocycle j q hn s hs eK eH i)

/-- The polynomial correction on affine quotient points. -/
def correctionPoint {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) : Lie.AffinePoints K A :=
  (vectorAffineCoordinates eK A).symm (Multiplicative.ofAdd fun i =>
    aeval ((vectorAffineCoordinates eH A t).toAdd 0)
      (correctionPolynomial j q hn s hs eK heK eH heH i))

theorem correctionPoint_map
    {A D : Type u} [CommRing A] [Algebra k A] [CommRing D] [Algebra k D]
    (f : A →ₐ[k] D) (t : Lie.AffinePoints H A) :
    Lie.affineMap K f (correctionPoint j q hn s hs eK heK eH heH t) =
      correctionPoint j q hn s hs eK heK eH heH (Lie.affineMap H f t) := by
  apply (vectorAffineCoordinates eK D).injective
  apply Multiplicative.toAdd.injective
  rw [heK.vectorAffineCoordinates_naturality]
  simp only [correctionPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    heH.vectorAffineCoordinates_naturality]
  funext i
  exact (aeval_algHom_apply f _ _).symm

theorem correctionPoint_mul
    {A : Type u} [CommRing A] [Algebra k A] (t r : Lie.AffinePoints H A) :
    correctionPoint j q hn s hs eK heK eH heH (t * r) =
      defect j q hn s hs t r *
        correctionPoint j q hn s hs eK heK eH heH t *
        correctionPoint j q hn s hs eK heK eH heH r := by
  apply (vectorAffineCoordinates eK A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, correctionPoint, MulEquiv.apply_symm_apply,
    toAdd_ofAdd, toAdd_mul, Pi.add_apply]
  funext i
  have h := NaturalAdditiveCocycle.coboundaryPolynomial_spec
    (c := scalarDefect j q hn s hs eK eH i) (A := A)
    (scalarDefect_natural j q hn s hs eK heK eH heH i)
    (scalarDefect_isCocycle j q hn s hs eK eH i)
    ((vectorAffineCoordinates eH A t).toAdd 0) ((vectorAffineCoordinates eH A r).toAdd 0)
  simp only [scalarDefect, additivePoint_coordinate] at h
  simp only [Pi.add_apply]
  dsimp only [correctionPolynomial]
  rw [h]
  abel

variable [IsAffineHom H.X.hom]

/-- The actual scheme morphism given by the natural polynomial correction. -/
def correctionHom : H.X ⟶ K.X :=
  PointedCoordinateWeights.homOfAffinePoints
    (fun _ _ _ t => correctionPoint j q hn s hs eK heK eH heH t)

/-- The correction morphism has its prescribed value on every affine point. -/
theorem comp_correctionHom {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    t ≫ correctionHom j q hn s hs eK heK eH heH =
      correctionPoint j q hn s hs eK heK eH heH t := by
  apply PointedCoordinateWeights.comp_homOfAffinePoints
  intro A D _ _ _ _ f t
  exact correctionPoint_map j q hn s hs eK heK eH heH f t

/-- Correct the original section by its polynomial kernel-valued cochain. -/
def correctedSectionHom : H.X ⟶ E.X :=
  (correctionHom j q hn s hs eK heK eH heH ≫ j.hom.hom) * s

/-- Evaluation of the corrected section on affine points. -/
theorem comp_correctedSectionHom {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    t ≫ correctedSectionHom j q hn s hs eK heK eH heH =
      (correctionPoint j q hn s hs eK heK eH heH t ≫ j.hom.hom) * (t ≫ s) := by
  rw [correctedSectionHom, MonObj.comp_mul, ← Category.assoc, comp_correctionHom]

/-- A kernel-valued correction preserves the section identity. -/
theorem correctedSectionHom_comp :
    correctedSectionHom j q hn s hs eK heK eH heH ≫ q.hom.hom = 𝟙 H.X := by
  have hnq : j.hom.hom ≫ q.hom.hom = 1 := by
    have hm : j.hom.hom ∈ (SubgroupFunctor.range j).carrier K.X :=
      SubgroupFunctor.mem_range.2 ⟨𝟙 K.X, Category.id_comp _⟩
    rw [hn, mem_range_kernelι_iff] at hm
    exact hm
  rw [correctedSectionHom, MonObj.mul_comp, Category.assoc,
    hnq, MonObj.comp_one, hs, one_mul]

/-- The correction kills the multiplicativity defect on every affine test. -/
theorem correctedSectionHom_mul_affine {A : Type u} [CommRing A] [Algebra k A]
    (t r : Lie.AffinePoints H A) :
    (t * r) ≫ correctedSectionHom j q hn s hs eK heK eH heH =
      (t ≫ correctedSectionHom j q hn s hs eK heK eH heH) *
        (r ≫ correctedSectionHom j q hn s hs eK heK eH heH) := by
  rw [comp_correctedSectionHom, comp_correctedSectionHom, comp_correctedSectionHom,
    correctionPoint_mul, MonObj.mul_comp, MonObj.mul_comp, defect_comp]
  exact commutative_correction_identity (t ≫ s) (r ≫ s) ((t * r) ≫ s)
    (correctionPoint j q hn s hs eK heK eH heH t ≫ j.hom.hom)
    (correctionPoint j q hn s hs eK heK eH heH r ≫ j.hom.hom)

/-- Multiplicativity on affine points gives multiplicativity on every scheme test. -/
theorem correctedSectionHom_mul {T : Over (Spec (CommRingCat.of k))}
    (t r : T ⟶ H.X) :
    (t * r) ≫ correctedSectionHom j q hn s hs eK heK eH heH =
      (t ≫ correctedSectionHom j q hn s hs eK heK eH heH) *
        (r ≫ correctedSectionHom j q hn s hs eK heK eH heH) := by
  have hu : (fst H.X H.X * snd H.X H.X) ≫
      correctedSectionHom j q hn s hs eK heK eH heH =
      (fst H.X H.X ≫ correctedSectionHom j q hn s hs eK heK eH heH) *
        (snd H.X H.X ≫ correctedSectionHom j q hn s hs eK heK eH heH) := by
    apply PointedCoordinateWeights.affine_hom_ext
    intro A _ _ x
    simp only [← Category.assoc, MonObj.comp_mul,
      correctedSectionHom_mul_affine j q hn s hs eK heK eH heH]
  have htr : t * r = lift t r ≫ (fst H.X H.X * snd H.X H.X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [htr, Category.assoc, hu, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

/-- The corrected scheme section, packaged as an actual group-scheme morphism. -/
def extensionSection : H ⟶ E :=
  homOfPoints
    (fun _ => MonoidHom.mk' (· ≫ correctedSectionHom j q hn s hs eK heK eH heH)
      (correctedSectionHom_mul j q hn s hs eK heK eH heH))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The corrected group-scheme section splits the original quotient. -/
theorem extensionSection_comp :
    extensionSection j q hn s hs eK heK eH heH ≫ q = 𝟙 H := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, extensionSection, comp_homOfPoints,
    MonoidHom.mk'_apply, Category.assoc, correctedSectionHom_comp, Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

end Section

section Existence

variable {k : Type u} [Field k] [CharZero k]
    {E K H : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj E.X]
    [IsAffineHom E.X.hom]
    (j : K ⟶ E) [Mono j.hom.hom] (q : E ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hn : SubgroupFunctor.range j = SubgroupFunctor.range (kernelι q)) {d : ℕ}

include hn in
/-- A commutative affine extension of a one-dimensional additive group by any
finite-dimensional vector group splits as group schemes in characteristic zero. -/
theorem exists_extensionSection (hK : IsVectorGroupOfDimension K d)
    (hH : IsVectorGroupOfDimension H 1) : ∃ σ : H ⟶ E, σ ≫ q = 𝟙 H := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨s, hs⟩ := hK.exists_quotientSection j q hn
  obtain ⟨eK, heK⟩ := hK
  obtain ⟨eH, heH⟩ := hH
  exact ⟨extensionSection j q hn s hs eK heK eH heH,
    extensionSection_comp j q hn s hs eK heK eH heH⟩

end Existence

end Langlands.GroupScheme.CommutativeAdditiveExtension
