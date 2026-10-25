import Langlands.Global.AdelicGL
import Langlands.Global.ArchimedeanCompact
import Langlands.Global.ArchimedeanLieAlgebra
import Langlands.Global.AdelicFunctoriality.Isomorphism

/-!
# The CM involution on adelic general linear groups

For a CM field `E`, the arithmetic transport of adeles along Mathlib's CM involution
acts entrywise on the finite and infinite adelic matrix groups. At the infinite places
it is entrywise complex conjugation in the mixed coordinates, so it preserves the
standard unitary compact subgroup, and its differential is the same entrywise map on
the real matrix Lie algebra.
-/

noncomputable section

universe u

namespace Langlands.Global.CMConjugation

open NumberField NumberField.InfinitePlace AdelicFunctoriality

variable (E : Type u) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

/-- The CM involution of `E` as a ring automorphism. -/
abbrev fieldConj : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

/-- Entrywise CM conjugation on the full adelic matrix group. -/
def adelicConj : AdelicGL E n ≃ₜ* AdelicGL E n where
  toFun := Matrix.GeneralLinearGroup.map (adeleEquiv (fieldConj E)).toRingHom
  invFun := Matrix.GeneralLinearGroup.map (adeleEquiv (fieldConj E)).symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (adeleEquiv (fieldConj E)).symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (adeleEquiv (fieldConj E)).apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := (continuous_adeleEquiv (fieldConj E)).generalLinearGroup_map
  continuous_invFun := (continuous_adeleEquiv_symm (fieldConj E)).generalLinearGroup_map

@[simp]
theorem adelicConj_apply (g : AdelicGL E n) (i j : Fin n) :
    adelicConj E n g i j = adeleEquiv (fieldConj E) (g i j) := rfl

/-- Entrywise CM conjugation on the finite adelic matrix group. -/
def finiteConj : FiniteAdelicGL E n ≃ₜ* FiniteAdelicGL E n where
  toFun := Matrix.GeneralLinearGroup.map (finiteAdeleEquiv (fieldConj E)).toRingHom
  invFun := Matrix.GeneralLinearGroup.map (finiteAdeleEquiv (fieldConj E)).symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (finiteAdeleEquiv (fieldConj E)).symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (finiteAdeleEquiv (fieldConj E)).apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := (continuous_finiteAdeleEquiv (fieldConj E)).generalLinearGroup_map
  continuous_invFun := (continuous_finiteAdeleEquiv_symm (fieldConj E)).generalLinearGroup_map

@[simp]
theorem finiteConj_apply (g : FiniteAdelicGL E n) (i j : Fin n) :
    finiteConj E n g i j = finiteAdeleEquiv (fieldConj E) (g i j) := rfl

/-- Entrywise CM conjugation on the infinite adelic matrix group. -/
def infiniteConj : InfiniteAdelicGL E n ≃ₜ* InfiniteAdelicGL E n where
  toFun := Matrix.GeneralLinearGroup.map (infiniteComplexConj (K := E)).toRingHom
  invFun := Matrix.GeneralLinearGroup.map (infiniteComplexConj (K := E)).symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (infiniteComplexConj (K := E)).symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (infiniteComplexConj (K := E)).apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := (continuous_infiniteAdeleEquiv (fieldConj E)).generalLinearGroup_map
  continuous_invFun :=
    (continuous_infiniteAdeleEquiv_symm (fieldConj E)).generalLinearGroup_map

@[simp]
theorem infiniteConj_apply (g : InfiniteAdelicGL E n) (i j : Fin n) :
    infiniteConj E n g i j = infiniteComplexConj (g i j) := rfl

/-- The finite and infinite components of the full conjugation are the two factor maps. -/
@[simp]
theorem finite_adelicConj (g : AdelicGL E n) :
    AdelicGL.finite E n (adelicConj E n g) = finiteConj E n (AdelicGL.finite E n g) := by
  apply Units.ext
  rfl

@[simp]
theorem infinite_adelicConj (g : AdelicGL E n) :
    AdelicGL.infinite E n (adelicConj E n g) = infiniteConj E n (AdelicGL.infinite E n g) := by
  apply Units.ext
  rfl

/-- Rational matrices are sent to their entrywise CM conjugates. -/
theorem adelicConj_rational (γ : RationalGL E n) :
    adelicConj E n (AdelicGL.rational E n γ) =
      AdelicGL.rational E n (Matrix.GeneralLinearGroup.map (fieldConj E).toRingHom γ) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact adeleEquiv_diagonal (fieldConj E) (γ i j)

/-- Entrywise complex conjugation of the mixed archimedean coordinates. -/
def mixedConj : mixedEmbedding.mixedSpace E ≃ₐ[ℝ] mixedEmbedding.mixedSpace E :=
  AlgEquiv.prodCongr AlgEquiv.refl (AlgEquiv.piCongrRight fun _ => Complex.conjAe)

omit [NumberField E] [IsCMField E] in
@[simp]
theorem mixedConj_apply (x : mixedEmbedding.mixedSpace E) :
    mixedConj E x = (x.1, fun v => star (x.2 v)) := rfl

/-- A CM field has no real places, so the real mixed coordinates are vacuous. -/
theorem not_isReal (v : InfinitePlace E) : ¬ IsReal v :=
  not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v)

/-- In mixed coordinates the CM involution of infinite adeles is complex conjugation. -/
theorem mixedSpace_infiniteComplexConj (x : InfiniteAdeleRing E) :
    InfiniteAdeleRing.ringEquiv_mixedSpace E (infiniteComplexConj x) =
      mixedConj E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) := by
  apply Prod.ext
  · funext v
    exact absurd v.2 (not_isReal E v.1)
  · funext v
    exact infiniteComplexConj_coordinate v.1 x

/-- The coordinate form of `infiniteConj`: entrywise conjugation of mixed matrices. -/
theorem coordinates_infiniteConj (g : InfiniteAdelicGL E n) (i j : Fin n) :
    archimedeanGLCoordinates E n (infiniteConj E n g) i j =
      mixedConj E (archimedeanGLCoordinates E n g i j) :=
  mixedSpace_infiniteComplexConj E (g i j)

private theorem map_star_mem_unitaryGroup {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    A.map star ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let f := (starRingEnd ℂ).mapMatrix (m := Fin n)
  have hf : ∀ B : Matrix (Fin n) (Fin n) ℂ, star (f B) = f (star B) := by
    intro B
    ext i j
    simp [f, Matrix.star_apply]
  have hfA : f A = A.map star := rfl
  rw [← hfA]
  rw [Unitary.mem_iff] at hA ⊢
  refine ⟨?_, ?_⟩
  · rw [hf, ← map_mul, hA.1, map_one]
  · rw [hf, ← map_mul, hA.2, map_one]

/-- The CM involution preserves the standard unitary compact subgroup. -/
theorem infiniteConj_mem_standardInfiniteCompact {g : InfiniteAdelicGL E n}
    (hg : g ∈ standardInfiniteCompact E n) :
    infiniteConj E n g ∈ standardInfiniteCompact E n := by
  rw [mem_standardInfiniteCompact_iff] at hg ⊢
  refine ⟨fun v => absurd v.2 (not_isReal E v.1), fun v => ?_⟩
  have h : ArchimedeanGL.complexMatrix E n (archimedeanGLCoordinates E n (infiniteConj E n g)) v =
      (ArchimedeanGL.complexMatrix E n (archimedeanGLCoordinates E n g) v).map star := by
    ext i j
    change (archimedeanGLCoordinates E n (infiniteConj E n g) i j).2 v =
      star ((archimedeanGLCoordinates E n g i j).2 v)
    rw [coordinates_infiniteConj]
    rfl
  rw [h]
  exact map_star_mem_unitaryGroup n (hg.2 v)

/-- The restriction of the CM involution to the standard compact subgroup. -/
def compactConj : standardInfiniteCompact E n →* standardInfiniteCompact E n where
  toFun k := ⟨infiniteConj E n k, infiniteConj_mem_standardInfiniteCompact E n k.2⟩
  map_one' := Subtype.ext (map_one (infiniteConj E n))
  map_mul' k l := Subtype.ext (map_mul (infiniteConj E n) (k : InfiniteAdelicGL E n) l)

@[simp]
theorem compactConj_val (k : standardInfiniteCompact E n) :
    (compactConj E n k : InfiniteAdelicGL E n) = infiniteConj E n k := rfl

/-- Entrywise conjugation of the mixed coordinates on the real matrix Lie algebra. The
group map `infiniteConj` is given by the same entrywise map (`coordinates_infiniteConj`),
which is why this is used as its differential. -/
def lieConj : ArchimedeanGL.RealLieAlgebra E n →ₗ⁅ℝ⁆ ArchimedeanGL.RealLieAlgebra E n where
  toFun X := (mixedConj E).mapMatrix (show ArchimedeanMatrix E n from X)
  map_add' X Y := map_add (mixedConj E).mapMatrix
    (show ArchimedeanMatrix E n from X) (show ArchimedeanMatrix E n from Y)
  map_smul' c X := map_smul (mixedConj E).mapMatrix c (show ArchimedeanMatrix E n from X)
  map_lie' := by
    intro X Y
    change (mixedConj E).mapMatrix
        ((show ArchimedeanMatrix E n from X) * (show ArchimedeanMatrix E n from Y) -
          (show ArchimedeanMatrix E n from Y) * (show ArchimedeanMatrix E n from X)) =
      (mixedConj E).mapMatrix (show ArchimedeanMatrix E n from X) *
          (mixedConj E).mapMatrix (show ArchimedeanMatrix E n from Y) -
        (mixedConj E).mapMatrix (show ArchimedeanMatrix E n from Y) *
          (mixedConj E).mapMatrix (show ArchimedeanMatrix E n from X)
    rw [map_sub, map_mul, map_mul]

omit [NumberField E] [IsCMField E] in
@[simp]
theorem lieConj_apply (X : ArchimedeanGL.RealLieAlgebra E n) (i j : Fin n) :
    ArchimedeanGL.realLieAlgebraToMatrix E n (lieConj E n X) i j =
      mixedConj E (ArchimedeanGL.realLieAlgebraToMatrix E n X i j) := rfl

end Langlands.Global.CMConjugation
