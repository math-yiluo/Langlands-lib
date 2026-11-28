import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Integral quadratic forms and bisectors of split cocharacter lattices -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Covering.BrylinskiDeligne

section Integral

variable {Y : Type*} [AddCommGroup Y]

/-- The integral polarization `B_Q(x,y) = Q(x+y) - Q(x) - Q(y)`. -/
def polarization (Q : QuadraticForm ℤ Y) : LinearMap.BilinForm ℤ Y :=
  Q.polarBilin

theorem polarization_apply (Q : QuadraticForm ℤ Y) (x y : Y) :
    polarization Q x y = Q (x + y) - Q x - Q y :=
  rfl

theorem polarization_comm (Q : QuadraticForm ℤ Y) (x y : Y) :
    polarization Q x y = polarization Q y x :=
  QuadraticMap.polar_comm Q x y

theorem polarization_self (Q : QuadraticForm ℤ Y) (y : Y) :
    polarization Q y y = 2 * Q y := by
  change QuadraticMap.polar Q y y = _
  simpa only [two_nsmul, two_mul] using Q.polar_self y

/-- A bisector of `Q` is an integral bilinear form with diagonal `Q`. -/
structure Bisector (Q : QuadraticForm ℤ Y) where
  form : LinearMap.BilinForm ℤ Y
  diagonal : ∀ y, form y y = Q y

namespace Bisector

variable {Q : QuadraticForm ℤ Y}

theorem polarization_eq (D : Bisector Q) :
    polarization Q = D.form + D.form.flip := by
  have h : D.form.toQuadraticMap = Q := QuadraticMap.ext D.diagonal
  exact (congrArg polarization h.symm).trans
    (LinearMap.BilinMap.polarBilin_toQuadraticMap (B := D.form))

variable {I : Type*} [Fintype I] [LinearOrder I]

private def triangularForm (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y) :
    LinearMap.BilinForm ℤ Y :=
  Matrix.toBilin e (Matrix.of fun i j =>
    if i = j then Q (e i) else if i < j then polarization Q (e i) (e j) else 0)

private theorem triangularForm_apply_basis (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y)
    (i j : I) :
    triangularForm Q e (e i) (e j) =
      if i = j then Q (e i) else if i < j then polarization Q (e i) (e j) else 0 := by
  rw [← LinearMap.BilinForm.toMatrix_apply e (triangularForm Q e) i j,
    triangularForm, LinearMap.BilinForm.toMatrix_toBilin, Matrix.of_apply]

private theorem triangularForm_add_flip (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y) :
    triangularForm Q e + (triangularForm Q e).flip = polarization Q := by
  apply (LinearMap.BilinForm.toMatrix e).injective
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply]
  change triangularForm Q e (e i) (e j) + triangularForm Q e (e j) (e i) =
    polarization Q (e i) (e j)
  rw [triangularForm_apply_basis Q e i j, triangularForm_apply_basis Q e j i]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [ne_of_lt hij, ne_of_gt hij, hij, not_lt_of_gt hij]
  · simp [polarization_self, two_mul]
  · simp [ne_of_gt hji, ne_of_lt hji, hji, not_lt_of_gt hji, polarization_comm Q (e j) (e i)]

/-- The bisector with diagonal `Q(eᵢ)`, entries `B_Q(eᵢ,eⱼ)` for `i < j`,
and zero entries for `j < i` in the given ordered basis. -/
def ofBasis (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y) : Bisector Q where
  form := triangularForm Q e
  diagonal y := by
    have h := congrArg (fun B : LinearMap.BilinForm ℤ Y => B y y) (triangularForm_add_flip Q e)
    change triangularForm Q e y y + triangularForm Q e y y = polarization Q y y at h
    rw [← two_mul, polarization_self] at h
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h

@[simp] theorem ofBasis_apply_diag (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y) (i : I) :
    (ofBasis Q e).form (e i) (e i) = Q (e i) :=
  (ofBasis Q e).diagonal _

theorem ofBasis_apply_of_lt (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y)
    {i j : I} (h : i < j) :
    (ofBasis Q e).form (e i) (e j) = polarization Q (e i) (e j) := by
  simp only [ofBasis, triangularForm_apply_basis, ite_eq_right (ne_of_lt h), ite_eq_left h]

theorem ofBasis_apply_of_gt (Q : QuadraticForm ℤ Y) (e : Module.Basis I ℤ Y)
    {i j : I} (h : j < i) :
    (ofBasis Q e).form (e i) (e j) = 0 := by
  simp only [ofBasis, triangularForm_apply_basis, ite_eq_right (ne_of_gt h),
    ite_eq_right (not_lt_of_gt h)]

end Bisector

end Integral

section Split

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Invariance under the full coweight representation of the Weyl group of the pinning. -/
def IsWeylInvariant (p : SplitPinning G) (Q : QuadraticForm ℤ (cocharacterLattice p.torus)) : Prop :=
  ∀ (w : p.rootDatum.weylGroup.op) (y : cocharacterLattice p.torus),
    Q (p.rootDatum.weylGroupCorootRep w y) = Q y

/-- The integral quadratic datum on the actual cocharacter lattice of a split pinning. -/
structure WeylInvariantQuadraticForm (p : SplitPinning G) where
  form : QuadraticForm ℤ (cocharacterLattice p.torus)
  weyl_invariant : IsWeylInvariant p form

theorem IsWeylInvariant.polarization_invariant {p : SplitPinning G}
    {Q : QuadraticForm ℤ (cocharacterLattice p.torus)} (hQ : IsWeylInvariant p Q)
    (w : p.rootDatum.weylGroup.op) (x y : cocharacterLattice p.torus) :
    polarization Q (p.rootDatum.weylGroupCorootRep w x) (p.rootDatum.weylGroupCorootRep w y) =
      polarization Q x y := by
  rw [polarization_apply, ← map_add, hQ w (x + y), hQ w x, hQ w y, polarization_apply]

theorem isWeylInvariant_iff_coreflection (p : SplitPinning G)
    (Q : QuadraticForm ℤ (cocharacterLattice p.torus)) :
    IsWeylInvariant p Q ↔ ∀ (i : p.rootIndex) (y : cocharacterLattice p.torus),
      Q (p.rootDatum.coreflection i y) = Q y := by
  let P := p.rootDatum
  let ρ := P.weylGroupCorootRep
  have hreflect (i : p.rootIndex) (y : cocharacterLattice p.torus) :
      ρ ⟨MulOpposite.op (RootPairing.Equiv.reflection P i), P.reflection_mem_weylGroup i⟩ y =
        P.coreflection i y :=
    DFunLike.congr_fun (RootPairing.Equiv.reflection_coweightEquiv P i) y
  constructor
  · intro h i y
    rw [← hreflect i y]
    exact h ⟨MulOpposite.op (RootPairing.Equiv.reflection P i), P.reflection_mem_weylGroup i⟩ y
  · intro h w
    refine RootPairing.weylGroup.induction P
      (pred := fun g hg => ∀ y, Q (ρ ⟨MulOpposite.op g, hg⟩ y) = Q y)
      ?_ ?_ ?_ w.property
    · intro i y
      rw [hreflect]
      exact h i y
    · intro y
      change Q (ρ 1 y) = Q y
      simp
    · intro g g' hg hg' h₁ h₂ y
      change Q (ρ ((⟨MulOpposite.op g', hg'⟩ : P.weylGroup.op) * ⟨MulOpposite.op g, hg⟩) y) = Q y
      rw [map_mul, Module.End.mul_apply, h₂, h₁]

/-- Transport the standard basis of the split coordinates back to the actual cocharacter lattice. -/
def cocharacterBasisOfSplitting (p : SplitPinning G) {I : Type u} [Fintype I]
    (e : p.torus.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) :
    Module.Basis I ℤ (cocharacterLattice p.torus) :=
  (Pi.basisFun ℤ I).map
    ((cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso e)).trans
      (splitTorus.cocharacterLatticeEquiv k I)).toIntLinearEquiv.symm

/-- Every split pinning has a cocharacter basis indexed by a finite linear order. -/
theorem exists_orderedCocharacterBasis (p : SplitPinning G) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (cocharacterLattice p.torus)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := p.isSplitTorus
  let _ : Fintype I := Fintype.ofFinite I
  exact ⟨Fintype.card I, ⟨(cocharacterBasisOfSplitting p e).reindex (Fintype.equivFin I)⟩⟩

namespace WeylInvariantQuadraticForm

variable {p : SplitPinning G} (Q : WeylInvariantQuadraticForm p)

/-- Choose a bisector using an actual splitting of the pinned torus with ordered factors. -/
def bisectorOfSplitting {I : Type u} [Fintype I] [LinearOrder I]
    (e : p.torus.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) : Bisector Q.form :=
  Bisector.ofBasis Q.form (cocharacterBasisOfSplitting p e)

theorem nonempty_bisector : Nonempty (Bisector Q.form) := by
  obtain ⟨_, ⟨e⟩⟩ := exists_orderedCocharacterBasis p
  exact ⟨Bisector.ofBasis Q.form e⟩

end WeylInvariantQuadraticForm

end Split

end Langlands.Covering.BrylinskiDeligne
