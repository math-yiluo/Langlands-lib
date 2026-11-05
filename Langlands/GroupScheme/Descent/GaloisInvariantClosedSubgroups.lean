import Langlands.FieldTheory.FrobeniusApproximation
import Langlands.GroupScheme.Descent.RadicalIdealSheaf
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.BaseChangeReflection

/-! # Closed-subgroup descent over arbitrary Galois extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace TensorGaloisPoint

variable (k K A : Type u) [Field k] [Fintype k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [CommRing A] [Algebra k A]

/-- On each tensor, every coefficient automorphism agrees with a Frobenius power. -/
theorem exists_coefficientConjugate_frobenius_pow_eq
    (σ : K ≃ₐ[k] K) (x : K ⊗[k] A) :
    ∃ n : ℕ, coefficientConjugate k K A
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ n) x =
        coefficientConjugate k K A σ x := by
  classical
  let b := Module.Free.chooseBasis k A
  let v := (b.baseChange K).repr x
  obtain ⟨n, hn⟩ := Langlands.FieldTheory.exists_frobenius_pow_eq_on_finset k K σ
    (v.support.image v)
  refine ⟨n, (b.baseChange K).repr.injective ?_⟩
  ext j
  rw [repr_coefficientConjugate, repr_coefficientConjugate]
  change (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ n) (v j) = σ (v j)
  by_cases hj : j ∈ v.support
  · exact hn _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  · have hz : v j = 0 := Finsupp.notMem_support_iff.mp hj
    simp only [hz, map_zero]

/-- Frobenius stability of a tensor ideal implies stability under every
coefficient automorphism, without a finite-degree assumption. -/
theorem coefficientConjugate_mem_of_frobenius
    (I : Ideal (K ⊗[k] A))
    (hF : ∀ x ∈ I, coefficientConjugate k K A
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K) x ∈ I)
    (σ : K ≃ₐ[k] K) (x : K ⊗[k] A) (hx : x ∈ I) :
    coefficientConjugate k K A σ x ∈ I := by
  have hp (n : ℕ) : coefficientConjugate k K A
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ n) x ∈ I := by
    induction n with
    | zero => simpa only [pow_zero, coefficientConjugate_one, AlgHom.id_apply] using hx
    | succ n ih =>
      rw [pow_succ', coefficientConjugate_mul, AlgHom.comp_apply]
      exact hF _ ih
  obtain ⟨n, hn⟩ := exists_coefficientConjugate_frobenius_pow_eq k K A σ x
  rw [← hn]
  exact hp n

end TensorGaloisPoint

namespace Descent.GaloisInvariantClosedSubgroup

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of K))}
    {i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- The source comparison associated with equality of actual Galois-translated
closed-subgroup images. -/
def sourceIso (hi : IsClosedSubgroup i) (σ : K ≃ₐ[k] K)
    (hσ : SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj H ≅ H :=
  ((hi.baseChange (galoisBaseMap k K σ)).comp_iso
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G)).sourceIsoOfRangeEq hi hσ

theorem sourceIso_hom_comp (hi : IsClosedSubgroup i) (σ : K ≃ₐ[k] K)
    (hσ : SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    (sourceIso hi σ hσ).hom ≫ i = radicalGaloisHom i σ :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ hσ

/-- The actual semilinear self-map on an invariant closed subgroup. -/
def sourceConjugate (hi : IsClosedSubgroup i) (σ : K ≃ₐ[k] K)
    (hσ : SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    H.X.left ⟶ H.X.left :=
  (sourceIso hi σ hσ).inv.hom.hom.left ≫
    pullback.fst H.X.hom (galoisBaseMap k K σ)

/-- The invariant closed inclusion intertwines the source and ambient
semilinear morphisms. -/
theorem sourceConjugate_comp (hi : IsClosedSubgroup i) (σ : K ≃ₐ[k] K)
    (hσ : SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    sourceConjugate hi σ hσ ≫ i.hom.hom.left =
      i.hom.hom.left ≫ TensorCoordinates.conjugate k K G.X σ := by
  apply (cancel_epi (sourceIso hi σ hσ).hom.hom.hom.left).mp
  have h := congrArg (fun f => f.hom.hom.left) (sourceIso_hom_comp hi σ hσ)
  change (sourceIso hi σ hσ).hom.hom.hom.left ≫ i.hom.hom.left =
    ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i).hom.hom.left ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G).hom.hom.hom.left at h
  have hs : (sourceIso hi σ hσ).hom.hom.hom.left ≫ sourceConjugate hi σ hσ =
      pullback.fst H.X.hom (galoisBaseMap k K σ) := by
    dsimp only [sourceConjugate]
    rw [← Category.assoc,
      show (sourceIso hi σ hσ).hom.hom.hom.left ≫
        (sourceIso hi σ hσ).inv.hom.hom.left = 𝟙 _ from
        congrArg (fun f => f.hom.hom.left) (sourceIso hi σ hσ).hom_inv_id,
      Category.id_comp]
  rw [← Category.assoc, hs, ← Category.assoc, h, Category.assoc,
    RadicalTensorIdeal.descentIso_hom_conjugate]
  change pullback.fst H.X.hom (galoisBaseMap k K σ) ≫ i.hom.hom.left =
    ((Over.pullback (galoisBaseMap k K σ)).map i.hom.hom).left ≫ _
  simp only [Over.pullback_map_left]
  exact (pullback.lift_fst _ _ _).symm

variable {A : Type u} [CommRing A] [Algebra k A]
    (e : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ≅ G.X)

/-- All-test invariance of a closed inclusion gives stability of its full
coordinate ideal under the corresponding coefficient automorphism. -/
theorem coefficientConjugate_mem (hi : IsClosedSubgroup i) (σ : K ≃ₐ[k] K)
    (hσ : SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i)
    (x : K ⊗[k] A)
    (hx : x ∈ RadicalTensorIdeal.coordinateIdeal (e := e) (i := i)) :
    TensorGaloisPoint.coefficientConjugate k K A σ x ∈
      RadicalTensorIdeal.coordinateIdeal (e := e) (i := i) := by
  change i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e
      (TensorGaloisPoint.coefficientConjugate k K A σ x)) = 0
  rw [TensorCoordinates.sectionsEquiv_coefficientConjugate]
  change (i.hom.hom.left ≫ TensorCoordinates.conjugate k K G.X σ).appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x) = 0
  rw [← sourceConjugate_comp hi σ hσ]
  change (sourceConjugate hi σ hσ).appTop (i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x)) = 0
  change i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x) = 0 at hx
  rw [hx, map_zero]

variable [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance : IsAffine ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A coefficient-stable closed-subgroup ideal over any Galois extension gives
an actual defining ideal sheaf on the original affine ambient group. -/
def idealSheafDescentOfCoefficientStable [IsGalois k K]
    (hI : ∀ (σ : K ≃ₐ[k] K) (x : K ⊗[k] A),
      x ∈ RadicalTensorIdeal.coordinateIdeal (e := e) (i := i) →
        TensorGaloisPoint.coefficientConjugate k K A σ x ∈
          RadicalTensorIdeal.coordinateIdeal (e := e) (i := i)) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      i.hom.hom.left.ker :=
  AffineIdealDescent.ofGaloisStableTensorIdeal k K A
    (pullback.fst G.X.hom (algebraBaseMap k K)) i.hom.hom.left.ker
    (TensorCoordinates.groundSectionsEquiv k A G.X e)
    (TensorCoordinates.sectionsEquiv k K A G.X e)
    (TensorCoordinates.projection_comp_groundSectionsEquiv k K A G.X e)
    (by
      intro σ x hx
      rw [RadicalTensorIdeal.ideal_top_comap_sectionsEquiv e] at hx ⊢
      exact hI σ x hx)

/-- All-test Galois invariance gives full defining-ideal descent, with no
finite-dimensionality assumption on the Galois extension. -/
def idealSheafDescent [IsGalois k K] (hi : IsClosedSubgroup i)
    (h : ∀ σ : K ≃ₐ[k] K,
      SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      i.hom.hom.left.ker :=
  idealSheafDescentOfCoefficientStable e (fun σ x hx =>
    coefficientConjugate_mem e hi σ (h σ) x hx)

/-- Over a finite ground field, Frobenius invariance alone gives full
ideal-sheaf descent over any algebraic Galois extension. -/
def idealSheafDescentOfFrobenius [Fintype k] [IsGalois k K]
    (hi : IsClosedSubgroup i)
    (hF : SubgroupFunctor.range
        (radicalGaloisHom i (FiniteField.frobeniusAlgEquivOfAlgebraic k K)) =
      SubgroupFunctor.range i) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      i.hom.hom.left.ker :=
  idealSheafDescentOfCoefficientStable e
    (TensorGaloisPoint.coefficientConjugate_mem_of_frobenius k K A _
      (fun x hx => coefficientConjugate_mem e hi _ hF x hx))

omit e [CommRing A] [Algebra k A] in
/-- Galois invariance of the actual closed subgroup implies equality on the
full fpqc overlap, including for infinite Galois extensions. -/
theorem overlap_range_eq [IsGalois k K] (hi : IsClosedSubgroup i)
    (h : ∀ σ : K ≃ₐ[k] K,
      SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i) := by
  let A₀ := Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X
  let e₀ : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A₀)) ≅ G.X :=
    (Langlands.AlgebraicGeometry.PointTopology.affineSchemeOverIso k G.X).symm
  exact hi.overlap_range_eq_of_definingIdealDescent (algebraBaseMap k K)
    (idealSheafDescent e₀ hi h)

omit e [CommRing A] [Algebra k A] in
/-- Frobenius invariance of an actual closed subgroup over an arbitrary
Galois extension of a finite field implies equality on the full fpqc overlap. -/
theorem overlap_range_eq_of_frobenius [Fintype k] [IsGalois k K]
    (hi : IsClosedSubgroup i)
    (hF : SubgroupFunctor.range
        (radicalGaloisHom i (FiniteField.frobeniusAlgEquivOfAlgebraic k K)) =
      SubgroupFunctor.range i) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i) := by
  let A₀ := Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X
  let e₀ : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A₀)) ≅ G.X :=
    (Langlands.AlgebraicGeometry.PointTopology.affineSchemeOverIso k G.X).symm
  exact hi.overlap_range_eq_of_definingIdealDescent (algebraBaseMap k K)
    (idealSheafDescentOfFrobenius e₀ hi hF)

omit e [CommRing A] [Algebra k A] in
/-- An invariant closed subgroup over any Galois extension descends as an
actual affine closed inclusion with an exact recovery isomorphism. -/
theorem exists_descent [IsGalois k K] (hi : IsClosedSubgroup i)
    (h : ∀ σ : K ≃ₐ[k] K,
      SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i) :
    ∃ (H₀ : GroupScheme (Spec (CommRingCat.of k))) (j : H₀ ⟶ G)
      (r : (GroupScheme.baseChange (algebraBaseMap k K)).obj H₀ ≅ H),
      IsAffine H₀.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange (algebraBaseMap k K)).map j = r.hom ≫ i := by
  let : Flat (algebraBaseMap k K) := (fieldExtension_fpqc k K).2.1
  let : Surjective (algebraBaseMap k K) := (fieldExtension_fpqc k K).1
  exact hi.exists_descent_of_overlap_range_eq (algebraBaseMap k K)
    (overlap_range_eq hi h)

omit e [CommRing A] [Algebra k A] in
/-- A Frobenius-invariant closed subgroup over any Galois extension of a
finite field has an actual affine closed-subgroup descent. -/
theorem exists_descent_of_frobenius [Fintype k] [IsGalois k K]
    (hi : IsClosedSubgroup i)
    (hF : SubgroupFunctor.range
        (radicalGaloisHom i (FiniteField.frobeniusAlgEquivOfAlgebraic k K)) =
      SubgroupFunctor.range i) :
    ∃ (H₀ : GroupScheme (Spec (CommRingCat.of k))) (j : H₀ ⟶ G)
      (r : (GroupScheme.baseChange (algebraBaseMap k K)).obj H₀ ≅ H),
      IsAffine H₀.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange (algebraBaseMap k K)).map j = r.hom ≫ i := by
  let : Flat (algebraBaseMap k K) := (fieldExtension_fpqc k K).2.1
  let : Surjective (algebraBaseMap k K) := (fieldExtension_fpqc k K).1
  exact hi.exists_descent_of_overlap_range_eq (algebraBaseMap k K)
    (overlap_range_eq_of_frobenius hi hF)

end Descent.GaloisInvariantClosedSubgroup

end Langlands.GroupScheme
