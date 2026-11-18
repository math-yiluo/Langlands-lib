import Langlands.CommutativeAlgebra.EulerDerivationConstants
import Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseFlat
import Langlands.GroupScheme.Lie.RepresentationDerivationPower
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry

/-! # Diagonal representations of height-one groups -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Module
open Langlands.AlgebraicGeometry Langlands.CommutativeAlgebra
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.Lie

private theorem surjective_aeval_of_cotangent_span
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
    {I : Type w} (ε : A →ₐ[k] k) (hNil : ∀ a, ε a = 0 → IsNilpotent a)
    (x : I → A) (hspan : Submodule.span k (Set.range (augmentationCotangent ε ∘ x)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial I k →ₐ[k] A) := by
  let B := Algebra.adjoin k (Set.range x)
  let f : B →ₐ[k] A := B.val
  let εB := ε.comp f
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  let : IsLocalRing A := UnramifiedFunctor.ArtinianBase.isLocalRing_of_ker_nil
    ε.toRingHom (fun c => ⟨algebraMap k A c, ε.commutes c⟩) hNil
  let : IsLocalRing B := UnramifiedFunctor.ArtinianBase.isLocalRing_of_ker_nil
    εB.toRingHom (fun c => ⟨algebraMap k B c, εB.commutes c⟩) (by
      intro b hb
      obtain ⟨m, hm⟩ := hNil (f b) hb
      refine ⟨m, Subtype.ext ?_⟩
      change f (b ^ m) = f 0
      simpa only [map_pow, map_zero] using hm)
  let : Algebra B A := f.toRingHom.toAlgebra
  let : IsScalarTower k B A := IsScalarTower.of_algHom f
  have hfin : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  have hcot : Function.Surjective (augmentationCotangentMap ε f) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let xi : B := ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    exact ⟨augmentationCotangent εB xi, augmentationCotangentMap_apply ε f xi⟩
  have hf := finiteLocalCotangentSurjectivity k B A ε f hfin hcot
  rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range]
  exact eq_top_iff.mpr fun a _ => by
    obtain ⟨b, rfl⟩ := hf a
    exact b.property

section HeightOne

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {n : ℕ}

local notation "A" => coordinateAlgebra G
local notation "ε" => coordinateOrigin G
local notation "Cot" => Ideal.Cotangent (RingHom.ker (AlgHom.toRingHom (coordinateOrigin G)))

/-- A functional on the actual cotangent defines an actual tangent point. -/
private def cotangentFunctionalPoint (ℓ : Cot →ₗ[k] k) : lieKernel G k :=
  (kernelCoordinates G).symm
    ⟨cotangentDualNumberLift ε ℓ, cotangentDualNumberLift_projection ε ℓ⟩

private theorem coordinates_cotangentFunctionalPoint (ℓ : Cot →ₗ[k] k) :
    pointCoordinates G (cotangentFunctionalPoint ℓ).val = cotangentDualNumberLift ε ℓ :=
  congrArg Subtype.val ((kernelCoordinates G).apply_symm_apply _)

private theorem tangentMatrix_cotangentFunctionalPoint (ρ : MatrixRepresentation G (Fin n))
    (ℓ : Cot →ₗ[k] k) (i j : Fin n) :
    ρ.tangentMatrix k (cotangentFunctionalPoint ℓ) i j =
      ℓ (augmentationCotangent ε (ρ.coordinateMatrix i j)) := by
  rw [tangentMatrix_eq_coordinateMatrix, Matrix.map_apply, coordinates_cotangentFunctionalPoint,
    cotangentDualNumberLift_snd]

private theorem cotangent_span_of_diagonal_tangent (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ)
    (hdiag : ∀ (X : lieKernel G k) (i j : Fin n), i ≠ j → ρ.tangentMatrix k X i j = 0) :
    Submodule.span k (Set.range (fun i => augmentationCotangent ε (ρ.coordinateMatrix i i))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨ℓ, hℓ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let X : lieKernel G k := cotangentFunctionalPoint ℓ
  have hzero : ρ.tangentMatrix k X = 0 := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [show ρ.tangentMatrix k X i i = ℓ (augmentationCotangent ε (ρ.coordinateMatrix i i))
        from tangentMatrix_cotangentFunctionalPoint ρ ℓ i i]
      exact hker (Submodule.subset_span ⟨i, rfl⟩)
    · exact hdiag X i j hij
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have hX : X = 1 := by
    apply lieKernelHom_injective ρ
    apply (GeneralLinear.DualNumber.pointKernelEquiv
      (n := Fin n) (R := CommRingCat.of k) (S := k)).symm.injective
    change ρ.tangentMatrix k X = ρ.tangentMatrix k 1
    rw [hzero, tangentMatrix_one]
  apply hℓ
  apply (cotangentDualNumberLift_eq_constant_iff ε ℓ).mp
  rw [← coordinates_cotangentFunctionalPoint ℓ]
  change pointCoordinates G X.val = _
  rw [hX]
  exact pointCoordinates_one G

/-- A closed representation of a finite height-one group whose tangent matrices
are diagonal has a diagonal universal matrix. -/
theorem isDiagonalGL_universal_of_diagonal_tangent [Module.Finite k A]
    (p : ℕ) [CharP k p] (hp : 1 < p)
    (hheight : ∀ a : A, a ^ p = algebraMap k A (ε a) ^ p)
    (ρ : MatrixRepresentation G (Fin n)) (hρ : IsClosedSubgroup ρ)
    (hdiag : ∀ (X : lieKernel G k) (i j : Fin n), i ≠ j → ρ.tangentMatrix k X i j = 0) :
    GeneralLinear.IsDiagonalGL (ρ.affineMatrix A (universalPoint G)) := by
  classical
  let U := ρ.coordinateMatrix
  have hε (i j : Fin n) : ε (U i j) = (1 : Matrix (Fin n) (Fin n) k) i j :=
    congrArg (fun M => M i j) (coordinateMatrix_origin ρ)
  have hunit (i : Fin n) : U i i ^ p = 1 := by
    rw [hheight, hε, Matrix.one_apply_eq, map_one, one_pow]
  let c (j : Fin n) := augmentationCotangent ε (U j j)
  obtain ⟨I, f, hf, hspan, hlin⟩ := exists_linearIndependent' k c
  have hc : Submodule.span k (Set.range c) = ⊤ :=
    cotangent_span_of_diagonal_tangent ρ hρ hdiag
  rw [hc] at hspan
  let : Finite I := Finite.of_injective f hf
  let : Fintype I := Fintype.ofFinite I
  let b : Basis I k Cot := Basis.mk hlin hspan.ge
  let x (i : I) := U (f i) (f i)
  let X (i : I) : lieKernel G k := cotangentFunctionalPoint (b.coord i)
  let D (i : I) : Derivation k A A := translationDerivation G (X i)
  have hweight (a : I) (i j : Fin n) : D a (U i j) = ρ.tangentMatrix k (X a) i i • U i j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) A => M i j)
      (coordinateMatrix_translationDerivation ρ (X a))
    change D a (U i j) = ∑ l, algebraMap k A (ρ.tangentMatrix k (X a) i l) * U l j at h
    rw [h, Finset.sum_eq_single i]
    · exact (Algebra.smul_def _ _).symm
    · intro l _ hli
      rw [hdiag (X a) i l hli.symm, map_zero, zero_mul]
    · simp
  have hD (i j : I) : D i (x j) = (if i = j then (1 : k) else 0) • x j := by
    change D i (U (f j) (f j)) = _
    rw [hweight]
    have he : ρ.tangentMatrix k (X i) (f j) (f j) = b.coord i (b j) := by
      change ρ.tangentMatrix k (cotangentFunctionalPoint (b.coord i)) (f j) (f j) = _
      rw [tangentMatrix_cotangentFunctionalPoint, Basis.mk_apply]
      rfl
    rw [he, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j <;> simp [hij, eq_comm, x]
  have hgen : Function.Surjective (MvPolynomial.aeval x : MvPolynomial I k →ₐ[k] A) :=
    surjective_aeval_of_cotangent_span ε (fun a ha => ⟨p, by
      rw [hheight, ha, map_zero, zero_pow (by omega : p ≠ 0)]⟩) x hspan
  intro i j hij
  change U i j = 0
  let v := U i i ^ (p - 1)
  let y := U i j * v
  have hv : v * U i i = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), hunit]
  have hyu : y * U i i = U i j := by simp only [y, mul_assoc, hv, mul_one]
  have hyD (a : I) : D a y = 0 := by
    have hl := congrArg (D a) hyu
    rw [Derivation.leibniz, hweight a i i, hweight a i j] at hl
    simp only [smul_eq_mul, mul_smul_comm, hyu] at hl
    have hzero := add_eq_left.mp hl
    calc
      D a y = v * (U i i * D a y) := by rw [← mul_assoc, hv, one_mul]
      _ = 0 := by rw [hzero, mul_zero]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_eulerDerivations p hp x
    (fun i => hunit (f i)) hgen D hD hyD
  have hεy : ε y = 0 := by simp only [y, map_mul, hε, Matrix.one_apply_ne hij, zero_mul]
  have hd0 : d = 0 := ((coordinateOrigin G).commutes d).symm.trans ((congrArg (ε : A → k) hd).trans hεy)
  rw [← hyu, ← hd, hd0, map_zero, zero_mul]

/-- A finite height-one group with a closed representation having diagonal
actual tangent matrices is of multiplicative type. -/
theorem isMultiplicativeType_of_diagonal_tangent_heightOne [Module.Finite k A]
    (p : ℕ) [CharP k p] (hp : 1 < p)
    (hheight : ∀ a : A, a ^ p = algebraMap k A (ε a) ^ p)
    (ρ : MatrixRepresentation G (Fin n)) (hρ : IsClosedSubgroup ρ)
    (hdiag : ∀ (X : lieKernel G k) (i j : Fin n), i ≠ j → ρ.tangentMatrix k X i j = 0) :
    IsMultiplicativeType G := by
  have hU : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G)) :=
    isDiagonalGL_universal_of_diagonal_tangent p hp hheight ρ hρ hdiag
  have hT := (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k))
    (ULift.{u} (Fin n))).isTorus.isMultiplicativeType
  exact hT.of_isClosedSubgroup (universalDiagonalFactor ρ hU)
    (isClosedSubgroup_universalDiagonalFactor ρ hU hρ)

end HeightOne

end Langlands.GroupScheme.MatrixRepresentation
