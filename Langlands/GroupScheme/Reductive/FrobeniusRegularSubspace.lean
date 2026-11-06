import Langlands.GroupScheme.Reductive.CovariantProducts
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Mathlib.FieldTheory.Perfect

/-! # Frobenius powers of finite regular coordinate subspaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module TensorProduct
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Algebra

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
  (p : ℕ) [ExpChar k p] (e : ℕ) (V : Submodule k B)

/-- The linear span of characteristic-power coordinates of a subspace. -/
def frobeniusCoordinateSpan : Submodule k B :=
  Submodule.span k (Set.range fun v : V => (v : B) ^ p ^ e)

omit [ExpChar k p] in
theorem pow_mem_frobeniusCoordinateSpan {v : B} (hv : v ∈ V) :
    v ^ p ^ e ∈ frobeniusCoordinateSpan p e V :=
  Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩

variable {d : ℕ} (b : Basis (Fin d) k V)

theorem pow_eq_sum_basis {v : B} (hv : v ∈ V) :
    v ^ p ^ e = ∑ i, (extendedCoord V b i v) ^ p ^ e • (b i : B) ^ p ^ e := by
  conv_lhs => rw [← basis_expand V b hv]
  change characteristicPowerMap k p B e _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [characteristicPowerMap_apply, Algebra.smul_def, mul_pow, map_pow]

theorem frobeniusCoordinateSpan_eq_span_basis :
    frobeniusCoordinateSpan p e V =
      Submodule.span k (Set.range fun i => (b i : B) ^ p ^ e) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change (v : B) ^ p ^ e ∈ _
    rw [pow_eq_sum_basis p e V b v.2]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact pow_mem_frobeniusCoordinateSpan p e V (b i).2

theorem finite_frobeniusCoordinateSpan [Module.Finite k V] :
    Module.Finite k (frobeniusCoordinateSpan p e V) := by
  rw [frobeniusCoordinateSpan_eq_span_basis p e V (Module.finBasis k V)]
  exact Module.Finite.span_of_finite k (Set.finite_range _)

variable [PerfectRing k p] [IsReduced B]

theorem linearIndependent_pow_basis :
    LinearIndependent k (fun i => (b i : B) ^ p ^ e) := by
  have hli : LinearIndependent k (fun i => (b i : B)) :=
    b.linearIndependent.map' V.subtype V.ker_subtype
  exact hli.map_of_surjective_injective
    (iterateFrobenius k p e) (characteristicPowerMap k p B e).toAddMonoidHom
    (bijective_iterateFrobenius k p e).2
    (fun v hv => IsReduced.eq_zero v ⟨p ^ e, hv⟩)
    (fun a v => by
      change (a • v) ^ p ^ e = a ^ p ^ e • v ^ p ^ e
      simp only [Algebra.smul_def, mul_pow, map_pow])

/-- The powers of the original basis form a basis of the characteristic-power
span over a perfect field in a reduced coordinate algebra. -/
def frobeniusCoordinateBasis : Basis (Fin d) k (frobeniusCoordinateSpan p e V) :=
  (Basis.span (linearIndependent_pow_basis p e V b)).map
    (LinearEquiv.ofEq _ _ (frobeniusCoordinateSpan_eq_span_basis p e V b).symm)

@[simp]
theorem frobeniusCoordinateBasis_apply (i : Fin d) :
    (frobeniusCoordinateBasis p e V b i : B) = (b i : B) ^ p ^ e := by
  simp [frobeniusCoordinateBasis, Basis.map_apply]

end Algebra

section Bialgebra

variable {k B : Type u} [Field k] [CommRing B] [Bialgebra k B]
  (p : ℕ) [ExpChar k p] (e : ℕ) (V : Submodule k B)
  {d : ℕ} (b : Basis (Fin d) k V)
  (hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)

include hV in
/-- The coaction of a characteristic power is the power of the original coaction. -/
theorem comul_basis_pow (j : Fin d) :
    Coalgebra.comul (R := k) ((b j : B) ^ p ^ e) =
      ∑ i, ((b i : B) ^ p ^ e) ⊗ₜ[k] ((subspaceMatrix V b i j) ^ p ^ e) := by
  rw [Bialgebra.comul_pow, comul_basis V b hV]
  change characteristicPowerMap k p (B ⊗[k] B) e _ = _
  rw [map_sum]
  simp only [characteristicPowerMap_apply, Algebra.TensorProduct.tmul_pow]

include hV in
/-- Contraction of the powered coaction is a combination of powered basis coordinates. -/
theorem rightAct_basis_pow (f : Module.Dual k B) (j : Fin d) :
    rightAct f ((b j : B) ^ p ^ e) =
      ∑ i, f ((subspaceMatrix V b i j) ^ p ^ e) • (b i : B) ^ p ^ e := by
  rw [rightAct_apply, comul_basis_pow p e V b hV, map_sum, map_sum]
  simp

include b hV in
/-- The characteristic-power span of a finite regular subspace is regular. -/
theorem rightAct_mem_frobeniusCoordinateSpan (f : Module.Dual k B) {v : B}
    (hv : v ∈ frobeniusCoordinateSpan p e V) :
    rightAct f v ∈ frobeniusCoordinateSpan p e V := by
  have hle : frobeniusCoordinateSpan p e V ≤
      (frobeniusCoordinateSpan p e V).comap (rightAct f) := by
    conv_lhs => rw [frobeniusCoordinateSpan_eq_span_basis p e V b]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change rightAct f ((b j : B) ^ p ^ e) ∈ frobeniusCoordinateSpan p e V
    rw [rightAct_basis_pow p e V b hV]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (pow_mem_frobeniusCoordinateSpan p e V (b i).2)
  exact hle hv

variable [PerfectRing k p] [IsReduced B]

include hV in
/-- In the powered basis, the regular coefficient matrix is powered entry by entry. -/
theorem subspaceMatrix_frobeniusCoordinateBasis (i j : Fin d) :
    subspaceMatrix (frobeniusCoordinateSpan p e V)
      (frobeniusCoordinateBasis p e V b) i j = (subspaceMatrix V b i j) ^ p ^ e := by
  classical
  change leftAct (extendedCoord (frobeniusCoordinateSpan p e V)
    (frobeniusCoordinateBasis p e V b) i)
    (frobeniusCoordinateBasis p e V b j : B) = _
  rw [frobeniusCoordinateBasis_apply, leftAct_apply, comul_basis_pow p e V b hV,
    map_sum, map_sum]
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  simp only [← frobeniusCoordinateBasis_apply p e V b, extendedCoord_basis]
  simp [Matrix.one_apply]

end Bialgebra

section Covariant

variable {k B C : Type u} [Field k] [CommRing B] [Bialgebra k B]
  [CommRing C] [Algebra k C]

/-- Powers of covariant coordinates have the corresponding power covariance weight. -/
theorem pow_mem_leftCovariantSubspace (r : B →ₐ[k] C) (χ : C) (n : ℕ)
    {v : B} (hv : v ∈ leftCovariantSubspace r.toLinearMap χ) :
    v ^ n ∈ leftCovariantSubspace r.toLinearMap (χ ^ n) := by
  rw [mem_leftCovariantSubspace] at hv ⊢
  rw [Bialgebra.comul_pow]
  change (Algebra.TensorProduct.map r (AlgHom.id k B)) _ = _
  change (Algebra.TensorProduct.map r (AlgHom.id k B)) (Coalgebra.comul v) = _ at hv
  rw [map_pow, hv, Algebra.TensorProduct.tmul_pow]

/-- The span of characteristic powers retains the powered covariance weight. -/
theorem frobeniusCoordinateSpan_le_leftCovariantSubspace
    (p e : ℕ) (r : B →ₐ[k] C) (χ : C) {V : Submodule k B}
    (hV : V ≤ leftCovariantSubspace r.toLinearMap χ) :
    frobeniusCoordinateSpan p e V ≤ leftCovariantSubspace r.toLinearMap (χ ^ p ^ e) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  exact pow_mem_leftCovariantSubspace r χ (p ^ e) (hV v.2)

end Covariant

section Actual

variable {k : Type u} [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} [IsReduced B]
  (c : (F ⋙ forget GrpCat).CorepresentableBy B)
  (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra c).toCoalgebra
    ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)

/-- The actual regular representation on the characteristic-power coordinate span. -/
def frobeniusRegularRepresentation (e : ℕ) :
    MatrixRepresentation (Corepresented.groupScheme F c) (Fin d) := by
  let := bialgebra c
  exact regularRepresentation c (Field.toIsField k)
    (frobeniusCoordinateSpan p e V) (frobeniusCoordinateBasis p e V b)
    (fun f _ hv => rightAct_mem_frobeniusCoordinateSpan p e V b hV f hv)

/-- The universal matrix is the entrywise characteristic power of the original matrix. -/
theorem frobeniusRegularRepresentation_universalMatrix (e : ℕ) :
    letI := (bialgebra c).toCoalgebra
    Unipotent.universalMatrix c (frobeniusRegularRepresentation p c V b hV e) =
      (subspaceMatrix V b).map (characteristicPowerMap k p B e) := by
  let := bialgebra c
  rw [frobeniusRegularRepresentation, regularRepresentation_universalMatrix]
  ext i j
  exact subspaceMatrix_frobeniusCoordinateBasis p e V b hV i j

/-- The identity matrix intertwines the actual Frobenius power with the regular
representation on powered coordinates, on every affine test algebra. -/
theorem intertwines_frobeniusRegularRepresentation (e : ℕ) :
    Intertwines ((regularRepresentation c (Field.toIsField k) V b hV).frobeniusPower p e)
      (frobeniusRegularRepresentation p c V b hV e) (1 : Matrix (Fin d) (Fin d) k) := by
  let := bialgebra c
  apply intertwines_of_universalMatrix c
  have hF : Unipotent.universalMatrix c
      ((regularRepresentation c (Field.toIsField k) V b hV).frobeniusPower p e) =
      (subspaceMatrix V b).map (characteristicPowerMap k p B e) := by
    ext i j
    change ((regularRepresentation c (Field.toIsField k) V b hV).frobeniusPower p e).affineMatrix
      B (𝟙 _) i j = _
    erw [frobeniusPower_affineMatrix]
    change (Unipotent.universalMatrix c
      (regularRepresentation c (Field.toIsField k) V b hV) i j) ^ p ^ e = _
    rw [regularRepresentation_universalMatrix]
    rfl
  rw [hF, frobeniusRegularRepresentation_universalMatrix]
  simp

end Actual

section Affine

variable {k : Type u} [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] [IsReduced G.X.left]
  (V : Submodule k (AffineCoordinates.algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
      v ∈ V → rightAct f v ∈ V)

local instance affineFrobeniusReducedAlgebra : _root_.IsReduced (AffineCoordinates.algebra G) := by
  have : IsIso (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (AffineCoordinates.groupSchemeIso G))).hom)
  have h := isReduced_of_isOpenImmersion (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left
  exact (affine_isReduced_iff (CommRingCat.of (AffineCoordinates.algebra G))).mp h

/-- The powered-coordinate regular representation of an actual affine reduced group. -/
def affineFrobeniusRegularRepresentation (e : ℕ) : MatrixRepresentation G (Fin d) :=
  (frobeniusRegularRepresentation p (AffineCoordinates.corepresentation G) V b hV e).restrict
    (AffineCoordinates.groupSchemeIso G).inv

/-- Transport to the original group preserves the identity intertwiner. -/
theorem intertwines_affineFrobeniusRegularRepresentation (e : ℕ) :
    Intertwines ((affineRegularRepresentation G V b hV).frobeniusPower p e)
      (affineFrobeniusRegularRepresentation p G V b hV e)
      (1 : Matrix (Fin d) (Fin d) k) := by
  have h := (intertwines_frobeniusRegularRepresentation p
    (AffineCoordinates.corepresentation G) V b hV e).restrict
      (AffineCoordinates.groupSchemeIso G).inv
  rw [← frobeniusPower_restrict] at h
  exact h

/-- On every affine test, the powered-coordinate representation has the entrywise
characteristic-power matrix of the original regular representation. -/
theorem affineFrobeniusRegularRepresentation_affineMatrix (e : ℕ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    (affineFrobeniusRegularRepresentation p G V b hV e).affineMatrix A x =
      Matrix.GeneralLinearGroup.map (characteristicPowerMap k p A e)
        ((affineRegularRepresentation G V b hV).affineMatrix A x) := by
  rw [← frobeniusPower_affineMatrix]
  apply Units.ext
  have h := intertwines_affineFrobeniusRegularRepresentation p G V b hV e A x
  have hm : (1 : Matrix (Fin d) (Fin d) k).map (algebraMap k A) = 1 := by
    ext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  simpa only [hm, Matrix.one_mul, Matrix.mul_one] using h.symm

end Affine

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.AffineCoordinates

open AffineLinearEmbedding

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance frobeniusRegularInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance frobeniusRegularInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

set_option backward.isDefEq.respectTransparency false in
/-- The characteristic-power span has the powered covariance coordinate for an
actual affine group morphism. -/
theorem frobeniusCoordinateSpan_le_leftCovariantSubspace (p e : ℕ) (i : H ⟶ G)
    (χ : algebra H) {V : Submodule k (algebra G)} (hV : V ≤ leftCovariantSubspace i χ) :
    Chevalley.frobeniusCoordinateSpan p e V ≤ leftCovariantSubspace i (χ ^ p ^ e) := by
  let := bialgebra (corepresentation G)
  exact Chevalley.frobeniusCoordinateSpan_le_leftCovariantSubspace
    (k := k) (B := algebra G) (C := algebra H) p e
    (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom χ hV

end Langlands.GroupScheme.AffineCoordinates
