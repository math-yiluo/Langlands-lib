import Langlands.GroupScheme.BorelCosetProper
import Langlands.GroupScheme.Absolute.GeneralLinearBorelProof
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.GeneralLinearPermutationConjugation
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.Reductive.GeneralLinear
import Mathlib.Data.Fin.Tuple.Sort

/-! # Proper dynamic quotients of general linear groups by matrix methods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

/-- The standard strictly decreasing weight, defining upper triangular matrices. -/
def upperWeight (N : ℕ) (i : Fin N) : ℤ := -(i.val : ℤ)

theorem strictAnti_upperWeight (N : ℕ) : StrictAnti (upperWeight N) := by
  intro a b hab
  exact neg_lt_neg (Int.ofNat_lt.mpr hab)

/-- An inner automorphism carries upper triangular matrices into the block
parabolic of any weights, on every relative scheme test. -/
theorem exists_iso_upper_to_blockParabolic {N : ℕ}
    (R : CommRingCat.{u}) (e : Fin N → ℤ) :
    ∃ ψ : groupScheme (Fin N) R ≅ groupScheme (Fin N) R,
      ∀ (T : Over (Spec R)) (x : T ⟶ (groupScheme (Fin N) R).X),
        x ∈ (blockParabolic (Fin N) R (upperWeight N)).carrier T →
        x ≫ ψ.hom.hom.hom ∈ (blockParabolic (Fin N) R e).carrier T := by
  let τ := Tuple.sort (fun i => -e i)
  have hanti : Antitone (e ∘ τ) := by
    intro a b hab
    exact neg_le_neg_iff.mp (Tuple.monotone_sort (fun i => -e i) hab)
  refine ⟨(groupScheme (Fin N) R).innerIso (permPoint R τ), ?_⟩
  intro T x hx
  rw [mem_blockParabolic]
  intro i j hij
  have hji : τ.symm j < τ.symm i := by
    by_contra h
    have hle := hanti (le_of_not_gt h)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at hle
    exact (not_lt_of_ge hle) hij
  rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
    pointsEquiv_constantPoint_permPoint]
  rw [← Equiv.symm_symm τ, permGL_symm_conj_apply]
  exact (mem_blockParabolic (upperWeight N)).mp hx _ _
    (strictAnti_upperWeight N hji)

/-- A group automorphism carries upper triangular matrices into the dynamic
parabolic of an arbitrary cocharacter of `GL_N`. -/
theorem exists_iso_upper_to_parabolic (k : Type u) [Field k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      groupScheme (Fin N) (CommRingCat.of k)) :
    ∃ ψ : groupScheme (Fin N) (CommRingCat.of k) ≅
        groupScheme (Fin N) (CommRingCat.of k),
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (x : T ⟶ (groupScheme (Fin N) (CommRingCat.of k)).X),
        x ∈ (blockParabolic (Fin N) (CommRingCat.of k) (upperWeight N)).carrier T →
        x ≫ ψ.hom.hom.hom ∈ (Dynamic.parabolic χ).carrier T := by
  obtain ⟨g, e, he⟩ := exists_innerIso_comp_eq_diagonalCocharacter k χ
  let d := (groupScheme (Fin N) (CommRingCat.of k)).innerIso g
  obtain ⟨σ, hσ⟩ := exists_iso_upper_to_blockParabolic (CommRingCat.of k) e
  refine ⟨σ ≪≫ d.symm, ?_⟩
  intro T x hx
  have hp : x ≫ σ.hom.hom.hom ∈ (Dynamic.parabolic (χ ≫ d.hom)).carrier T := by
    rw [he, parabolic_diagonalCocharacter]
    exact hσ T x hx
  have h := Dynamic.parabolic_le_comap (χ ≫ d.hom) d.inv T hp
  rw [Dynamic.comp_hom_comp_inv] at h
  exact h

/-- Every supplied separated locally finite type dynamic quotient of `GL_N`
with a surjective projection is proper. -/
theorem suppliedDynamicQuotient_isProper (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      groupScheme (Fin N) (CommRingCat.of k))
    {Q : Over (Spec (CommRingCat.of k))}
    (q : (groupScheme (Fin N) (CommRingCat.of k)).X ⟶ Q)
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [Surjective q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k)))
      (x y : T ⟶ (groupScheme (Fin N) (CommRingCat.of k)).X),
      x⁻¹ * y ∈ (Dynamic.parabolic χ).carrier T → x ≫ q = y ≫ q) :
    IsProper Q.hom := by
  let : Smooth (groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    smoothStatement (Fin N) _
  let : IsAffineHom (groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    isAffineHom_groupScheme (Fin N) _
  obtain ⟨ψ, hψ⟩ := exists_iso_upper_to_parabolic k χ
  let a := ψ.hom.hom.hom
  have : IsIso a.left := isIso_left_of_iso ψ
  have : Surjective (a ≫ q).left := by
    rw [Over.comp_left]
    infer_instance
  apply isProper_of_borel_coset
    (blockParabolicHom (Fin N) (CommRingCat.of k) (upperWeight N))
    (UpperTriangular.isBorelSubgroup_blockParabolicHom k (strictAnti_upperWeight N))
    (a ≫ q)
  intro T x y hxy
  rw [← Category.assoc, ← Category.assoc]
  apply hq
  have hx := hψ T (x⁻¹ * y)
    (by rwa [← (isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k)
      (upperWeight N)).2])
  simpa only [a, MonObj.mul_comp, GrpObj.inv_comp] using hx

/-- Every cocharacter of `GL_N` has an actual proper homogeneous quotient by
its represented dynamic parabolic. -/
theorem exists_properDynamicQuotient (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      groupScheme (Fin N) (CommRingCat.of k)) :
    ∃ D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient (@Dynamic.Affine.parabolicHom
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ),
      IsProper D.scheme.hom := by
  let G := groupScheme (Fin N) (CommRingCat.of k)
  let : Smooth G.X.hom := smoothStatement (Fin N) _
  let : IsAffineHom G.X.hom := isAffineHom_groupScheme (Fin N) _
  let i := @Dynamic.Affine.parabolicHom
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ
  have hi := @Dynamic.Affine.isRepresentedBy_parabolicHom
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ
  have hsm := (dynamicSmooth k G χ (@Dynamic.Affine.parabolicScheme
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ) i).1 hi
  obtain ⟨Q, q, hsep, hft, hqc, hsmq, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G (@Dynamic.Affine.parabolicScheme
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ) i
      (@Dynamic.Affine.isClosedSubgroup_parabolicHom
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ) hsm
  let D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i :=
    ⟨Q, q, hsep, hft, hqc, hsmq, hsurj, hqqc, hfib⟩
  refine ⟨D, ?_⟩
  let : IsSeparated Q.hom := hsep
  let : LocallyOfFiniteType Q.hom := hft
  let : Surjective q.left := hsurj
  apply suppliedDynamicQuotient_isProper k χ q
  intro T x y hxy
  apply (hfib T x y).mpr
  dsimp only [i]
  rwa [hi.2]

/-- An actual proper dynamic homogeneous quotient of `GL_N`, chosen with its
smooth surjective quasi-compact projection and all-test coset fibers. -/
def properDynamicQuotient (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      groupScheme (Fin N) (CommRingCat.of k)) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient (@Dynamic.Affine.parabolicHom
      (CommRingCat.of k) (groupScheme (Fin N) (CommRingCat.of k))
      (isAffine_groupScheme (Fin N) (CommRingCat.of k)) χ) :=
  Classical.choose (exists_properDynamicQuotient k χ)

theorem isProper_properDynamicQuotient (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      groupScheme (Fin N) (CommRingCat.of k)) :
    IsProper (properDynamicQuotient k χ).scheme.hom :=
  Classical.choose_spec (exists_properDynamicQuotient k χ)

end Langlands.GroupScheme.GeneralLinear
