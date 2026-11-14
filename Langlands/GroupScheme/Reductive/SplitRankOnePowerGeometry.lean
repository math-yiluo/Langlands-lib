import Langlands.GroupScheme.Reductive.SplitRankOnePowerCell
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Geometry of positive power maps on rank-one cells -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MvPolynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCell

section Polynomial

variable {R : Type u} [CommRing R] {σ : Type v}

/-- Substitution of positive powers is an integral ring homomorphism. -/
theorem expand_isIntegral {q : ℕ} (hq : 0 < q) :
    (expand q (σ := σ) (R := R)).toRingHom.IsIntegral := by
  let f := (expand q (σ := σ) (R := R)).toRingHom
  let := f.toAlgebra
  have hX (i : σ) : IsIntegral (MvPolynomial σ R) (X i : MvPolynomial σ R) := by
    apply IsIntegral.of_pow hq
    have h := isIntegral_algebraMap (R := MvPolynomial σ R)
      (A := MvPolynomial σ R) (x := X i)
    change IsIntegral (MvPolynomial σ R) ((expand q) (X i)) at h
    simpa only [expand_X] using h
  change ∀ a : MvPolynomial σ R, IsIntegral (MvPolynomial σ R) a
  intro a
  induction a using MvPolynomial.induction_on with
  | C a =>
      have h := isIntegral_algebraMap (R := MvPolynomial σ R)
        (A := MvPolynomial σ R) (x := C a)
      change IsIntegral (MvPolynomial σ R) ((expand q) (C a)) at h
      simpa only [expand_C] using h
  | add a b ha hb => exact ha.add hb
  | mul_X a i ha => exact ha.mul (hX i)

/-- In finitely many variables, substitution of positive powers is finite. -/
theorem expand_finite [Finite σ] {q : ℕ} (hq : 0 < q) :
    (expand q (σ := σ) (R := R)).toRingHom.Finite := by
  apply (expand_isIntegral (σ := σ) (R := R) hq).to_finite
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap R (MvPolynomial σ R))
  convert (RingHom.finiteType_algebraMap (A := R) (B := MvPolynomial σ R)).mpr
    (inferInstance : Algebra.FiniteType R (MvPolynomial σ R)) using 1
  exact RingHom.ext fun a => expand_C q a

end Polynomial

variable {k : Type u} [Field k]

/-- The actual map on the additive line is the relative spectrum of power substitution. -/
theorem gaPower_eq_algSpec (q : ℕ) :
    gaPower (k := k) q =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (expand q (σ := Fin 1) (R := k))).op := by
  apply crd_injective
  rw [gaPower, crd_pt]
  rw [crd, VectorGroup.coordinates_apply]
  change (VectorGroup.coordinateSection (CommRingCat.of k) 1 0) ^ q =
    (Spec.map (CommRingCat.ofHom (expand q (σ := Fin 1) (R := k)).toRingHom)).appTop
      ((Scheme.ΓSpecIso _).inv (X 0))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  change ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) k))).inv (X 0)) ^ q =
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) k))).inv
      ((expand q) (X 0))
  rw [expand_X, map_pow]

/-- Every positive power map on the additive line is finite. -/
theorem gaPower_isFinite {q : ℕ} (hq : 0 < q) :
    IsFinite (gaPower (k := k) q).left := by
  rw [gaPower_eq_algSpec]
  change IsFinite (Spec.map
    (CommRingCat.ofHom (expand q (σ := Fin 1) (R := k)).toRingHom))
  exact (IsFinite.SpecMap_iff _).mpr (expand_finite hq)

/-- Every positive power map on the additive line is surjective on scheme points. -/
theorem gaPower_surjective {q : ℕ} (hq : 0 < q) :
    Surjective (gaPower (k := k) q).left := by
  rw [gaPower_eq_algSpec]
  exact ⟨(expand_isIntegral (σ := Fin 1) (R := k) hq).comap_surjective
    (MvPolynomial.expand_injective hq)⟩

/-- At a characteristic-power exponent, the power map is a group-scheme morphism. -/
def gaPowerHom (p e : ℕ) [ExpChar k p] : Ga k ⟶ Ga k :=
  homOfPoints (fun Z =>
    { toFun := fun a => a ≫ gaPower (p ^ e)
      map_one' := gaPower_one p e Z
      map_mul' := gaPower_mul p e })
    (fun a x => by
      change (a ≫ x) ≫ gaPower (p ^ e) = a ≫ x ≫ gaPower (p ^ e)
      exact Category.assoc _ _ _)

@[simp]
theorem gaPowerHom_hom (p e : ℕ) [ExpChar k p] :
    (gaPowerHom (k := k) p e).hom.hom = gaPower (p ^ e) := by
  have h := comp_homOfPoints
    (fun Z =>
      { toFun := fun a => a ≫ gaPower (k := k) (p ^ e)
        map_one' := gaPower_one p e Z
        map_mul' := gaPower_mul p e })
    (fun a x => by
      change (a ≫ x) ≫ gaPower (p ^ e) = a ≫ x ≫ gaPower (p ^ e)
      exact Category.assoc _ _ _)
    (Ga k).X (𝟙 (Ga k).X)
  change (𝟙 (Ga k).X) ≫ (gaPowerHom p e).hom.hom =
    (𝟙 (Ga k).X) ≫ gaPower (p ^ e) at h
  simpa only [Category.id_comp] using h

private theorem prop_tensorHom_left (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S : Scheme.{u}} {X X' Y Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : P f.left) (hg : P g.left) : P (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact P.pullbackMap hf hg f.w.symm g.w.symm

variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The rank-one coordinate power map is a product of its three component maps. -/
theorem powerCell_eq_tensorHom (t : T ⟶ T') (q : ℕ) :
    powerCell t q =
      gaPower q ⊗ₘ ((CommGroupScheme.groupHom t).hom.hom ⊗ₘ gaPower q) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [powerCell, lift_fst, tensorHom_fst]
  · apply CartesianMonoidalCategory.hom_ext <;>
      simp only [powerCell, lift_fst, lift_snd,
        Category.assoc, tensorHom_fst, tensorHom_snd]

/-- Finite torus maps and positive additive powers give finite cell maps. -/
theorem powerCell_isFinite (t : T ⟶ T') [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    {q : ℕ} (hq : 0 < q) : IsFinite (powerCell t q).left := by
  rw [powerCell_eq_tensorHom]
  exact prop_tensorHom_left @IsFinite _ _ (gaPower_isFinite hq)
    (prop_tensorHom_left @IsFinite _ _ inferInstance (gaPower_isFinite hq))

/-- Surjective torus maps and positive additive powers give surjective cell maps. -/
theorem powerCell_surjective (t : T ⟶ T')
    [Surjective (CommGroupScheme.groupHom t).hom.hom.left]
    {q : ℕ} (hq : 0 < q) : Surjective (powerCell t q).left := by
  let : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    (inferInstance : MorphismProperty.IsMultiplicative @Surjective.{u}).toIsStableUnderComposition
  rw [powerCell_eq_tensorHom]
  exact prop_tensorHom_left @Surjective _ _ (gaPower_surjective hq)
    (prop_tensorHom_left @Surjective _ _ inferInstance (gaPower_surjective hq))

end Langlands.GroupScheme.RootCell
