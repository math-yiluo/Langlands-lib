import Langlands.GroupScheme.Rational.SplitTorusVectorCocycle
import Langlands.GroupScheme.Rational.PointedCoordinateAction
import Langlands.GroupScheme.Rational.PointedTensorWeights
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Group sections of split-torus extensions by linear vector groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

namespace PointedCoordinateWeights

variable {k : Type u} [Field k] {V W : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom]

/-- Morphisms out of an affine scheme over the field agree when they agree on
all affine points. -/
theorem affine_hom_ext {Φ Ψ : V ⟶ W}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (v : Points V A), v ≫ Φ = v ≫ Ψ) :
    Φ = Ψ :=
  (cancel_epi (coordinateIso V).hom).1 (h (Coord V) (coordinateIso V).hom)

/-- The morphism out of an affine scheme with prescribed values on affine points. -/
def homOfAffinePoints
    (φ : ∀ (A : Type u) [CommRing A] [Algebra k A], Points V A → Points W A) : V ⟶ W :=
  (coordinateIso V).inv ≫ φ (Coord V) (coordinateIso V).hom

/-- A natural family of maps on affine points is induced by its morphism. -/
theorem comp_homOfAffinePoints
    (φ : ∀ (A : Type u) [CommRing A] [Algebra k A], Points V A → Points W A)
    (hφ : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (f : A →ₐ[k] B) (v : Points V A), pointsMap f (φ A v) = φ B (pointsMap f v))
    {A : Type u} [CommRing A] [Algebra k A] (v : Points V A) :
    v ≫ homOfAffinePoints φ = φ A v := by
  have hv : pointsMap (pointCoordinates v) (coordinateIso V).hom = v :=
    pointCoordinates.symm_apply_apply v
  calc v ≫ homOfAffinePoints φ =
        pointsMap (pointCoordinates v) (coordinateIso V).hom ≫ homOfAffinePoints φ := by
          rw [hv]
    _ = pointsMap (pointCoordinates v) (φ (Coord V) (coordinateIso V).hom) := by
          simp [pointsMap, homOfAffinePoints]
    _ = φ A (pointsMap (pointCoordinates v) (coordinateIso V).hom) := hφ _ _ _ _
    _ = φ A v := by rw [hv]

end PointedCoordinateWeights

namespace splitTorus

open RelativeRoot PointedCoordinateWeights

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]
    {E N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom N.X.hom]
    (i : N ⟶ E) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range (𝟙 E)))
    (q : E ⟶ splitTorus (Spec (CommRingCat.of k)) I)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (s : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ E.X)
    (hs : s ≫ q.hom.hom = 𝟙 _)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

local notation "𝔻" => splitTorus (Spec (CommRingCat.of k)) I

/-- The defect of the scheme section on the universal pair of torus points. -/
def sectionDefect : (𝔻).X ⊗ (𝔻).X ⟶ E.X :=
  (fst (𝔻).X (𝔻).X ≫ s) * (snd (𝔻).X (𝔻).X ≫ s) * ((fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ s)⁻¹

omit [DecidableEq I] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
include hker hs in
theorem sectionDefect_mem :
    sectionDefect I s ∈ (SubgroupFunctor.range i).carrier ((𝔻).X ⊗ (𝔻).X) := by
  rw [hker, sectionDefect, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, Category.assoc, Category.assoc, hs, Category.comp_id,
    Category.comp_id, Category.comp_id, mul_inv_cancel]

/-- The defect of the scheme section, as an actual morphism to the kernel. -/
def kernelDefect : (𝔻).X ⊗ (𝔻).X ⟶ N.X :=
  Classical.choose (sectionDefect_mem I i q hker s hs)

omit [DecidableEq I] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem kernelDefect_comp : kernelDefect I i q hker s hs ≫ i.hom.hom = sectionDefect I s :=
  Classical.choose_spec (sectionDefect_mem I i q hker s hs)

/-- The section defect at a pair of points. -/
def defect {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) : T ⟶ N.X :=
  lift t r ≫ kernelDefect I i q hker s hs

omit [DecidableEq I] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem defect_comp {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) :
    defect I i q hker s hs t r ≫ i.hom.hom = (t ≫ s) * (r ≫ s) * ((t * r) ≫ s)⁻¹ := by
  rw [defect, Category.assoc, kernelDefect_comp, sectionDefect, MonObj.comp_mul,
    MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_snd, MonObj.comp_mul, lift_fst, lift_snd]

omit [DecidableEq I] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem comp_defect {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (t r : T ⟶ (𝔻).X) :
    b ≫ defect I i q hker s hs t r = defect I i q hker s hs (b ≫ t) (b ≫ r) := by
  rw [defect, defect, ← Category.assoc, comp_lift]

/-- The conjugation action of the extension on its normal vector subgroup. -/
abbrev conj : AutomorphicAction E N :=
  AutomorphicAction.ofNormalizedConjugation i (𝟙 E) hn

omit [IsAffineHom N.X.hom] in
theorem conj_act_comp {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X) (x : T ⟶ N.X) :
    (conj i hn).act g x ≫ i.hom.hom = g * (x ≫ i.hom.hom) * g⁻¹ := by
  simpa only [AutomorphicAction.act, AutomorphicAction.ofNormalizedConjugation,
    Grp.id_hom_hom, Category.comp_id] using
    SubgroupFunctor.lift_comp_normalizedConjugation_comp i (𝟙 E) hn g x

omit [DecidableEq I] [IsAffineHom N.X.hom] in
/-- The defect is a Hochschild two-cocycle for the conjugation action. -/
theorem defect_cocycle {T : Over (Spec (CommRingCat.of k))} (t r w : T ⟶ (𝔻).X) :
    defect I i q hker s hs t r * defect I i q hker s hs (t * r) w =
      (conj i hn).act (t ≫ s) (defect I i q hker s hs r w) *
        defect I i q hker s hs t (r * w) := by
  apply (cancel_mono i.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp, conj_act_comp, defect_comp, defect_comp,
    defect_comp, defect_comp, mul_assoc t r w]
  group

/-! ### Averaging the defect over the torus -/

section Averaging

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The inclusion of coefficients into Laurent polynomials. -/
abbrev laurentConst (A : Type u) [CommRing A] [Algebra k A] :
    A →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
  IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))

/-- Extension of scalars of the universal Laurent polynomials. -/
abbrev laurentScalars (A : Type u) [CommRing A] [Algebra k A] :
    AddMonoidAlgebra k (I → ℤ) →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
  AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)

/-- The universal torus point over Laurent polynomials with coefficients in `A`. -/
abbrev laurentPoint (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints (𝔻) (AddMonoidAlgebra A (I → ℤ)) :=
  Lie.affineMap _ (laurentScalars I A) (universalPoint (R := CommRingCat.of k) I)

omit [DecidableEq I] in
/-- Translation of Laurent polynomials by a family of units. -/
def laurentTranslation (r : I → Aˣ) :
    AddMonoidAlgebra A (I → ℤ) →ₐ[A] AddMonoidAlgebra A (I → ℤ) :=
  AddMonoidAlgebra.lift A _ (I → ℤ)
    ((AddMonoidAlgebra.of A (I → ℤ)) *
      ((algebraMap A (AddMonoidAlgebra A (I → ℤ))).toMonoidHom.comp
        ((Units.coeHom A).comp (exponentValue I r))))

omit [DecidableEq I] in
@[simp] theorem laurentTranslation_single (r : I → Aˣ) (m : I → ℤ) (a : A) :
    laurentTranslation I r (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (a * (exponentValue I r (Multiplicative.ofAdd m) : A)) := by
  simp [laurentTranslation, Algebra.smul_def, AddMonoidAlgebra.of_apply,
    AddMonoidAlgebra.single_mul_single]

omit [DecidableEq I] in
/-- Translation multiplies the coefficient at `m` by the monomial's value. -/
theorem coeff_laurentTranslation (r : I → Aˣ) (x : AddMonoidAlgebra A (I → ℤ))
    (m : I → ℤ) :
    (laurentTranslation I r x).coeff m =
      x.coeff m * (exponentValue I r (Multiplicative.ofAdd m) : A) := by
  classical
  have h (p : (I → ℤ) →₀ A) :
      (laurentTranslation I r (AddMonoidAlgebra.ofCoeff p)).coeff m =
        p m * (exponentValue I r (Multiplicative.ofAdd m) : A) := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq, add_mul]
    | single n a =>
        change (laurentTranslation I r (AddMonoidAlgebra.single n a)).coeff m = _
        rw [laurentTranslation_single]
        by_cases h : n = m
        · subst m; simp
        · simp [Ne.symm h]
  exact h x.coeff

omit [DecidableEq I] in
/-- Translation fixes the constant Laurent coefficient. -/
theorem coeff_zero_laurentTranslation (r : I → Aˣ) (x : AddMonoidAlgebra A (I → ℤ)) :
    (laurentTranslation I r x).coeff 0 = x.coeff 0 := by
  rw [coeff_laurentTranslation, ofAdd_zero, map_one, Units.val_one, mul_one]

omit [DecidableEq I] in
theorem laurentTranslation_comp_laurentConst (r : I → Aˣ) :
    ((laurentTranslation I r).restrictScalars k).comp (laurentConst I A) = laurentConst I A :=
  AlgHom.ext fun a => (laurentTranslation I r).commutes a

omit [DecidableEq I] in
theorem laurentTranslation_comp_laurentScalars (r : I → Aˣ) :
    ((laurentTranslation I r).restrictScalars k).comp (laurentScalars I A) =
      translatedEvaluation (R := CommRingCat.of k) I r := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    change laurentTranslation I r (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)
      (AddMonoidAlgebra.single m 1)) = translatedEvaluation I r (AddMonoidAlgebra.single m 1)
    rw [AddMonoidAlgebra.mapAlgHom_single, laurentTranslation_single,
      translatedEvaluation_single]
    simp
  · exact Subsingleton.elim _ _

/-- Translating the universal Laurent point by an actual point. -/
theorem laurentTranslation_laurentPoint (r : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap _ ((laurentTranslation I (algebraPointsEquiv I A r)).restrictScalars k)
        (laurentPoint I A) =
      Lie.affineMap _ (laurentConst I A) r * laurentPoint I A := by
  rw [laurentPoint, ← Lie.affineMap_comp, laurentTranslation_comp_laurentScalars,
    universalPoint_translatedEvaluation, MulEquiv.symm_apply_apply]

omit [DecidableEq I] in
theorem laurentTranslation_laurentConst (r : I → Aˣ) {G : GroupScheme (Spec (CommRingCat.of k))}
    (x : Lie.AffinePoints G A) :
    Lie.affineMap _ ((laurentTranslation I r).restrictScalars k)
        (Lie.affineMap _ (laurentConst I A) x) = Lie.affineMap _ (laurentConst I A) x := by
  rw [← Lie.affineMap_comp, laurentTranslation_comp_laurentConst]

local notation "δ" => defect I i q hker s hs

/-- The exponent-zero Laurent coefficient of the defect against the universal point:
the average of `defect t r` over the torus point `r`. -/
def averageVector (t : Lie.AffinePoints (𝔻) A) : Fin d → A :=
  fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
    (δ (Lie.affineMap _ (laurentConst I A) t) (laurentPoint I A))).toAdd j).coeff 0

/-- The averaged defect, as an actual point of the vector group. -/
def averagePoint (t : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints N A :=
  (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (averageVector I i q hker s hs e t))

local notation "β" => averageVector I i q hker s hs e
local notation "ρ" => averagePoint I i q hker s hs e

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
theorem averagePoint_coordinates (t : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (ρ t)).toAdd = β t := by
  rw [averagePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [DecidableEq I] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- Applying a coefficient map to an actual defect. -/
theorem affineMap_defect {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t r : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap N φ (δ t r) = δ (Lie.affineMap _ φ t) (Lie.affineMap _ φ r) :=
  comp_defect I i q hker s hs _ t r

/-- The scheme section corrected by the averaged defect. -/
def sectionPoint (t : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints E A :=
  (ρ t ≫ i.hom.hom)⁻¹ * (t ≫ s)

local notation "σ" => sectionPoint I i q hker s hs e

attribute [local instance] isAffineHom_splitTorus_spec

/-- The corrected section as a morphism of schemes. -/
def sectionHom : (𝔻).X ⟶ E.X :=
  homOfAffinePoints fun _ _ _ t => σ t

variable (he : IsLinearVectorCoordinates (conj i hn) e)
include he

omit [IsAffineHom N.X.hom] in
/-- The average is invariant under translation of the averaging variable. -/
theorem averageVector_translate (t r : Lie.AffinePoints (𝔻) A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (δ (Lie.affineMap _ (laurentConst I A) t)
        (Lie.affineMap _ (laurentConst I A) r * laurentPoint I A))).toAdd j).coeff 0) =
      β t := by
  let τ := (laurentTranslation I (algebraPointsEquiv I A r)).restrictScalars k
  rw [← laurentTranslation_laurentPoint, ← laurentTranslation_laurentConst I
    (algebraPointsEquiv I A r) t, ← affineMap_defect, he.1.vectorAffineCoordinates_naturality]
  funext j
  exact coeff_zero_laurentTranslation I _ _

omit [Fintype I] [DecidableEq I] [IsAffineHom N.X.hom] in
/-- Constant Laurent coefficients of a constant point. -/
theorem coeff_zero_laurentConst (x : Lie.AffinePoints N A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (Lie.affineMap N (laurentConst I A) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A x).toAdd := by
  rw [he.1.vectorAffineCoordinates_naturality]
  funext j
  change (AddMonoidAlgebra.single 0 _).coeff 0 = _
  simp

omit [Fintype I] [DecidableEq I] in
/-- Constant Laurent coefficients of the action of a constant point. -/
theorem coeff_zero_act (h : Lie.AffinePoints E A)
    (x : Lie.AffinePoints N (AddMonoidAlgebra A (I → ℤ))) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      ((conj i hn).act (Lie.affineMap E (laurentConst I A) h) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A ((conj i hn).act h ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (fun j =>
          ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ)) x).toAdd j).coeff 0))))).toAdd := by
  have hx := he.coordinateAction_eq (CommAlgCat.of k (AddMonoidAlgebra A (I → ℤ)))
    (Lie.affineMap E (laurentConst I A) h)
    (vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ)) x).toAdd
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hx
  rw [← hx, (conj i hn).coordinateAction_coeff, he.coordinateAction_eq]

/-- The averaged defect bounds the defect: the Hochschild two-cocycle is the
coboundary of the average. -/
theorem defect_add_averageVector (t r : Lie.AffinePoints (𝔻) A) :
    (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) =
      (vectorAffineCoordinates e A ((conj i hn).act (t ≫ s) (ρ r))).toAdd + β t := by
  have hc := congrArg (fun x : Lie.AffinePoints N (AddMonoidAlgebra A (I → ℤ)) =>
      fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ)) x).toAdd j).coeff 0)
    (defect_cocycle I i hn q hker s hs (Lie.affineMap _ (laurentConst I A) t)
      (Lie.affineMap _ (laurentConst I A) r) (laurentPoint I A))
  simp only [map_mul, toAdd_mul] at hc
  have h1 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (δ (Lie.affineMap _ (laurentConst I A) t) (Lie.affineMap _ (laurentConst I A) r))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (δ (Lie.affineMap _ (laurentConst I A) t * Lie.affineMap _ (laurentConst I A) r)
        (laurentPoint I A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (δ t r)).toAdd + β (t * r) := by
    rw [← affineMap_defect, ← map_mul]
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (fun a b : A => a + b) (congrFun (coeff_zero_laurentConst I i hn e he _) j) rfl
  have h2 : (fun j : Fin d => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      ((conj i hn).act (Lie.affineMap _ (laurentConst I A) t ≫ s)
        (δ (Lie.affineMap _ (laurentConst I A) r) (laurentPoint I A)))).toAdd j +
      (vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (δ (Lie.affineMap _ (laurentConst I A) t)
        (Lie.affineMap _ (laurentConst I A) r * laurentPoint I A))).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A ((conj i hn).act (t ≫ s) (ρ r))).toAdd + β t := by
    have hts : Lie.affineMap _ (laurentConst I A) t ≫ s =
        Lie.affineMap E (laurentConst I A) (t ≫ s) := by
      simp only [Lie.affineMap_apply, Category.assoc]
    rw [hts]
    funext j
    rw [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    exact congrArg₂ (· + ·)
      (congrFun (coeff_zero_act I i hn e he _ _) j)
      (congrFun (averageVector_translate I i hn q hker s hs e he t r) j)
  rw [← h1, ← h2]
  exact hc

/-- The averaged defect corrects the multiplicativity defect of the section. -/
theorem averagePoint_mul (t r : Lie.AffinePoints (𝔻) A) :
    ρ (t * r) = (δ t r)⁻¹ * (conj i hn).act (t ≫ s) (ρ r) * ρ t := by
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, averagePoint_coordinates]
  exact (eq_neg_add_of_add_eq (defect_add_averageVector I i hn q hker s hs e he t r)).trans
    (add_assoc _ _ _).symm

/-- The corrected section is multiplicative on affine points. -/
theorem sectionPoint_mul (t r : Lie.AffinePoints (𝔻) A) : σ (t * r) = σ t * σ r := by
  simp only [sectionPoint]
  rw [averagePoint_mul I i hn q hker s hs e he, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, conj_act_comp, defect_comp]
  group

omit [IsAffineHom N.X.hom] in
/-- The average commutes with extension of coefficients. -/
theorem averageVector_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    β (Lie.affineMap _ φ t) = fun j => φ (β t j) := by
  have hc : (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ).comp (laurentConst I A) =
      (laurentConst I B).comp φ := by
    ext a
    simp [laurentConst, AddMonoidAlgebra.coe_algebraMap]
  have hl : (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ).comp (laurentScalars I A) =
      laurentScalars I B := by
    rw [laurentScalars, laurentScalars, ← AddMonoidAlgebra.mapRangeAlgHom_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have hd : δ (Lie.affineMap _ (laurentConst I B) (Lie.affineMap _ φ t)) (laurentPoint I B) =
      Lie.affineMap N (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ)
        (δ (Lie.affineMap _ (laurentConst I A) t) (laurentPoint I A)) := by
    rw [affineMap_defect, laurentPoint, laurentPoint, ← Lie.affineMap_comp,
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
    averagePoint_coordinates, averageVector_naturality I i hn q hker s hs e he]

omit [IsAffineHom N.X.hom] in
/-- The corrected section commutes with extension of coefficients. -/
theorem sectionPoint_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap E φ (σ t) = σ (Lie.affineMap _ φ t) := by
  rw [sectionPoint, sectionPoint, map_mul, map_inv,
    ← averagePoint_naturality I i hn q hker s hs e he]
  simp only [Lie.affineMap_apply, Category.assoc]

omit [IsAffineHom N.X.hom] in
/-- The morphism of the corrected section on affine points. -/
theorem comp_sectionHom (t : Lie.AffinePoints (𝔻) A) :
    t ≫ sectionHom I i q hker s hs e = σ t :=
  comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => sectionPoint_naturality I i hn q hker s hs e he f v) t

/-- The corrected section is multiplicative on the universal pair of points. -/
theorem sectionHom_mul_universal :
    (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ sectionHom I i q hker s hs e =
      (fst (𝔻).X (𝔻).X ≫ sectionHom I i q hker s hs e) *
        (snd (𝔻).X (𝔻).X ≫ sectionHom I i q hker s hs e) := by
  apply affine_hom_ext
  intro A _ _ v
  simp only [← Category.assoc, MonObj.comp_mul, comp_sectionHom I i hn q hker s hs e he,
    sectionPoint_mul I i hn q hker s hs e he]

/-- The corrected section is multiplicative on all points. -/
theorem sectionHom_mul {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ (𝔻).X) :
    (x * y) ≫ sectionHom I i q hker s hs e =
      (x ≫ sectionHom I i q hker s hs e) * (y ≫ sectionHom I i q hker s hs e) := by
  have hxy : x * y = lift x y ≫ (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hxy, Category.assoc, sectionHom_mul_universal I i hn q hker s hs e he, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

omit [IsAffineHom N.X.hom] in
/-- The corrected section is a section of the quotient map on schemes. -/
theorem sectionHom_comp : sectionHom I i q hker s hs e ≫ q.hom.hom = 𝟙 (𝔻).X := by
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (hker _ _).1 (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  apply affine_hom_ext
  intro A _ _ t
  rw [← Category.assoc, comp_sectionHom I i hn q hker s hs e he, sectionPoint, MonObj.mul_comp,
    GrpObj.inv_comp, Category.assoc, Category.assoc, hs, hiq, MonObj.comp_one, inv_one,
    one_mul, Category.comp_id]

/-- The group-scheme section of a split-torus extension by a linear vector group. -/
def extensionSection : 𝔻 ⟶ E :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ sectionHom I i q hker s hs e)
    (sectionHom_mul I i hn q hker s hs e he))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The group-scheme section splits the quotient map. -/
theorem extensionSection_comp : extensionSection I i hn q hker s hs e he ≫ q = 𝟙 𝔻 := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, extensionSection, comp_homOfPoints,
    MonoidHom.mk'_apply,
    Category.assoc, sectionHom_comp I i hn q hker s hs e he, Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

include hker hs in
/-- A split-torus extension by a linear vector group with a scheme section splits. -/
theorem exists_extensionSection : ∃ φ : 𝔻 ⟶ E, φ ≫ q = 𝟙 𝔻 :=
  ⟨_, extensionSection_comp I i hn q hker s hs e he⟩

end Averaging

end splitTorus

open RelativeRoot in
/-- An extension of a split torus by a vector group with linear conjugation
coordinates has a homomorphic section once the quotient map has a section of
schemes. -/
theorem IsSplitTorus.exists_extensionSection {k : Type u} [Field k]
    {E N D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom N.X.hom]
    (i : N ⟶ E) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range (𝟙 E)))
    (q : E ⟶ D) (hD : IsSplitTorus D)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (s : D.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 _) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates (splitTorus.conj i hn) e) :
    ∃ σ : D ⟶ E, σ ≫ q = 𝟙 D := by
  classical
  obtain ⟨I, hI, ⟨f⟩⟩ := hD
  have : Fintype I := Fintype.ofFinite I
  have hfi : f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, f.hom_inv_id, Grp.id_hom_hom]
  have hif : f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, f.inv_hom_id, Grp.id_hom_hom]
  have hker' : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ (q ≫ f.hom).hom.hom = 1 := by
    intro T g
    rw [hker, Grp.comp_hom_hom]
    constructor
    · intro h
      rw [← Category.assoc, h, MonObj.one_comp]
    · intro h
      rw [← Category.comp_id (g ≫ q.hom.hom), ← hfi, ← Category.assoc, Category.assoc g, h,
        MonObj.one_comp]
  have hs' : (f.inv.hom.hom ≫ s) ≫ (q ≫ f.hom).hom.hom = 𝟙 _ := by
    rw [Grp.comp_hom_hom, Category.assoc, ← Category.assoc s, hs, Category.id_comp, hif]
  obtain ⟨σ, hσ⟩ := splitTorus.exists_extensionSection I i hn (q ≫ f.hom) hker'
    (f.inv.hom.hom ≫ s) hs' e he
  refine ⟨f.hom ≫ σ, ?_⟩
  have hσq : σ ≫ q = f.inv := by
    rw [← Category.comp_id (σ ≫ q), ← f.hom_inv_id, ← Category.assoc, Category.assoc σ, hσ,
      Category.id_comp]
  rw [Category.assoc, hσq, f.hom_inv_id]

end Langlands.GroupScheme
