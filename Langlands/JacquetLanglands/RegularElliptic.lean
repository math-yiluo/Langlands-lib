import Langlands.Group.GL.Basic
import Langlands.Algebra.ReducedCharpolyDivision
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot

/-!
# Regular elliptic elements and the correspondence `g ↔ g'`

Regular semisimple and regular elliptic elements of `GL_n(F)`, regular
elements of the unit group of a central division algebra `D` over `F`, and
the relation `g ↔ g'` of Deligne–Kazhdan–Vignéras and Badulescu: equality of
the characteristic polynomial of `g` and the reduced characteristic
polynomial of `g'`.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open _root_.Polynomial
open Langlands.CentralSimple

universe u

section GeneralLinear

variable {F : Type u} [Field F] {n : ℕ}

/-- An element of `GL_n(F)` is regular semisimple when its characteristic polynomial is
separable. -/
def IsRegularSemisimple (g : GeneralLinear n F) : Prop :=
  (g : Matrix (Fin n) (Fin n) F).charpoly.Separable

/-- An element of `GL_n(F)` is regular elliptic when its characteristic polynomial is separable
and irreducible over `F`. -/
def IsRegularElliptic (g : GeneralLinear n F) : Prop :=
  IsRegularSemisimple g ∧ Irreducible (g : Matrix (Fin n) (Fin n) F).charpoly

theorem IsRegularElliptic.isRegularSemisimple {g : GeneralLinear n F}
    (h : IsRegularElliptic g) : IsRegularSemisimple g :=
  h.1

/-- A monic polynomial of degree `n` with nonzero constant term is the characteristic
polynomial of an element of `GL_n(F)`: multiplication by the class of `X` on `F[X]/(p)`,
in the power basis. -/
theorem exists_generalLinear_charpoly_eq (p : F[X]) (hpm : p.Monic) (hn : p.natDegree = n)
    (h0 : p.coeff 0 ≠ 0) :
    ∃ g : GeneralLinear n F, (g : Matrix (Fin n) (Fin n) F).charpoly = p := by
  subst hn
  have hp0 : p ≠ 0 := hpm.ne_zero
  let M : Matrix (Fin p.natDegree) (Fin p.natDegree) F :=
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis hp0).basis (AdjoinRoot.powerBasis hp0).gen
  have hM : M.charpoly = p :=
    (charpoly_leftMulMatrix _).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hpm)
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

end GeneralLinear

section Division

variable (F : Type u) [Field F] (D : Type u) [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

/-- A unit of the central division algebra `D` is regular (semisimple) when its reduced
characteristic polynomial is separable. -/
def IsRegular (g' : Dˣ) : Prop :=
  (reducedCharpoly F D (g' : D)).Separable

/-- The correspondence `g ↔ g'` between a regular elliptic element of `GL_n(F)` and a regular
unit of `D`: the characteristic polynomial of `g` equals the reduced characteristic polynomial
of `g'`. -/
def Corresponds {n : ℕ} (g : GeneralLinear n F) (g' : Dˣ) : Prop :=
  IsRegularElliptic g ∧ IsRegular F D g' ∧
    (g : Matrix (Fin n) (Fin n) F).charpoly = reducedCharpoly F D (g' : D)

/-- A separable reduced characteristic polynomial of an element of a central division algebra
is its minimal polynomial. -/
theorem reducedCharpoly_eq_minpoly_of_separable (a : D)
    (hsep : (reducedCharpoly F D a).Separable) :
    reducedCharpoly F D a = minpoly F a := by
  set p := reducedCharpoly F D a with hp
  set q := minpoly F a with hq
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  have hqp : q ∣ p := minpoly.dvd F a (CentralDivision.aeval_reducedCharpoly F D a)
  have hqm : q.Monic := minpoly.monic hint
  have hpm : p.Monic := reducedCharpoly_monic F D a
  suffices hpq : p ∣ q from
    Polynomial.eq_of_monic_of_associated hpm hqm (associated_of_dvd_dvd hpq hqp)
  let Ω := AlgebraicClosure F
  let φ : F →+* Ω := algebraMap F Ω
  let b := Module.finBasis F D
  let M := Algebra.leftMulMatrix b a
  have : Nonempty (Fin (Module.finrank F D)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hchar : M.charpoly = p ^ reducedDegree F D :=
    charpoly_leftMulMatrix_eq_reducedCharpoly_pow F D b a
  have hMq : aeval M q = 0 := by
    change aeval (Algebra.leftMulMatrix b a) q = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  let M' : Matrix (Fin (Module.finrank F D)) (Fin (Module.finrank F D)) Ω := M.map φ
  have hM'q : aeval M' (q.map φ) = 0 := by
    have h1 : aeval M' (q.map φ) = (aeval M q).map φ := by
      rw [Polynomial.aeval_map_algebraMap]
      exact Polynomial.aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId F Ω)) M q
    rw [h1, hMq, Matrix.map_zero _ (map_zero φ)]
  have hroots : ∀ x ∈ (p.map φ).roots, x ∈ (q.map φ).roots := by
    intro x hx
    have hp0 : p.map φ ≠ 0 := (hpm.map φ).ne_zero
    have hxroot : (p.map φ).IsRoot x := (mem_roots hp0).1 hx
    have hcharroot : M'.charpoly.IsRoot x := by
      rw [Matrix.charpoly_map, hchar, Polynomial.map_pow]
      rw [Polynomial.IsRoot, eval_pow, hxroot.eq_zero,
        zero_pow (reducedDegree_pos F D).ne']
    have hspec : x ∈ spectrum Ω M' := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hcharroot
    have hmem := spectrum.subset_polynomial_aeval M' (q.map φ) ⟨x, hspec, rfl⟩
    rw [hM'q, spectrum.zero_eq] at hmem
    exact (mem_roots (hqm.map φ).ne_zero).2 hmem
  have hsplit : p.map φ = ((p.map φ).roots.map fun x => X - C x).prod :=
    (IsAlgClosed.splits (p.map φ)).eq_prod_roots_of_monic (hpm.map φ)
  have hnodup : (p.map φ).roots.Nodup := nodup_roots (hsep.map)
  have hle : (p.map φ).roots ≤ (q.map φ).roots :=
    (Multiset.le_iff_subset hnodup).2 hroots
  have hdvd : p.map φ ∣ q.map φ := by
    rw [hsplit]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots (hqm.map φ).ne_zero _).2 hle
  exact (Polynomial.map_dvd_map' φ).1 hdvd

/-- A separable reduced characteristic polynomial of an element of a central division algebra
is irreducible. -/
theorem irreducible_reducedCharpoly_of_separable (a : D)
    (hsep : (reducedCharpoly F D a).Separable) :
    Irreducible (reducedCharpoly F D a) := by
  rw [reducedCharpoly_eq_minpoly_of_separable F D a hsep]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a)

/-- Badulescu's form of the correspondence: `g` and `g'` are regular semisimple with equal
characteristic polynomials. Ellipticity of `g` is then automatic. -/
theorem corresponds_iff {n : ℕ} (g : GeneralLinear n F) (g' : Dˣ) :
    Corresponds F D g g' ↔
      IsRegularSemisimple g ∧ IsRegular F D g' ∧
        (g : Matrix (Fin n) (Fin n) F).charpoly = reducedCharpoly F D (g' : D) := by
  constructor
  · rintro ⟨hg, hg', heq⟩
    exact ⟨hg.1, hg', heq⟩
  · rintro ⟨hg, hg', heq⟩
    refine ⟨⟨hg, ?_⟩, hg', heq⟩
    rw [heq]
    exact irreducible_reducedCharpoly_of_separable F D _ hg'

/-- Corresponding elements only exist in the reduced degree of `D`. -/
theorem Corresponds.eq_reducedDegree {n : ℕ} {g : GeneralLinear n F} {g' : Dˣ}
    (h : Corresponds F D g g') : n = reducedDegree F D := by
  have h1 := congrArg Polynomial.natDegree h.2.2
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, reducedCharpoly_natDegree] at h1
  exact h1

/-- Every regular unit of `D` corresponds to a regular elliptic element of `GL_d(F)`,
`d` the reduced degree of `D`. -/
theorem exists_corresponds (g' : Dˣ) (hg' : IsRegular F D g') :
    ∃ g : GeneralLinear (reducedDegree F D) F, Corresponds F D g g' := by
  have hpq := reducedCharpoly_eq_minpoly_of_separable F D (g' : D) hg'
  have h0 : (reducedCharpoly F D (g' : D)).coeff 0 ≠ 0 := by
    rw [hpq]
    exact minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) g'.ne_zero
  obtain ⟨g, hg⟩ := exists_generalLinear_charpoly_eq (reducedCharpoly F D (g' : D))
    (reducedCharpoly_monic F D _) (reducedCharpoly_natDegree F D _) h0
  refine ⟨g, (corresponds_iff F D g g').2 ⟨?_, hg', hg⟩⟩
  unfold IsRegularSemisimple
  rw [hg]
  exact hg'

end Division

section Self

variable (F : Type u) [Field F]

/-- The field itself has reduced degree one. -/
theorem reducedDegree_self : reducedDegree F F = 1 := by
  simp [reducedDegree]

/-- Every unit of `F`, viewed as a central division algebra over itself, is regular. -/
theorem isRegular_self (a : Fˣ) : IsRegular F F a := by
  have hm := reducedCharpoly_monic F F (a : F)
  have hd : (reducedCharpoly F F (a : F)).natDegree = 1 := by
    rw [reducedCharpoly_natDegree, reducedDegree_self]
  have hx := hm.eq_X_add_C hd
  have h0 := CentralDivision.aeval_reducedCharpoly F F (a : F)
  rw [hx] at h0
  simp only [map_add, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] at h0
  have hc : (reducedCharpoly F F (a : F)).coeff 0 = -(a : F) := eq_neg_of_add_eq_zero_right h0
  unfold IsRegular
  rw [hx, hc, map_neg, ← sub_eq_add_neg]
  exact separable_X_sub_C

/-- Nonvacuity on concrete data: for `D = F` every unit of `F` corresponds to an element of
`GL_1(F)`. -/
theorem exists_corresponds_self (a : Fˣ) :
    ∃ g : GeneralLinear 1 F, Corresponds F F g a := by
  obtain ⟨g, hg⟩ := exists_corresponds F F a (isRegular_self F a)
  have hd := reducedDegree_self F
  revert g
  rw [hd]
  exact fun g hg => ⟨g, hg⟩

end Self

end Langlands.JacquetLanglands
