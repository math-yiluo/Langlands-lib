import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.Conjugation
import Langlands.GroupScheme.OrthogonalMatrix.Reductive
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Reductive.PinnedRigidityProof
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Automorphisms of `SO_{2n}` fixing the diagonal torus

An automorphism `β` of the split special orthogonal group `SO_{2n}` (`n ≥ 2`) that is the
identity on the diagonal torus is conjugation by a diagonal similitude. We pin `SO_{2n}` along
the diagonal torus (`SplitPinning.ofRootDatum`). The differential of `β` scales each simple root
vector by a unit `s_a`. The simple roots form a `ℤ`-basis of the root lattice, so there is a
homomorphism `H` from the root lattice to `kˣ` with `H(α_a) = s_a⁻¹`. The diagonal matrix
`d_x = H(w(x) - w(inl i₀))` is a similitude, and conjugation by it scales the root space of `χ`
by `H(χ)`. Then `β` followed by conjugation by `d` fixes the pinning, so it is the identity by
pinned rigidity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (weightCoord weightCoord_inl weightCoord_inr)

variable {l : Type} [Fintype l] [DecidableEq l]

section Diagonal

variable {A : Type*} [CommRing A]

/-- The invertible diagonal matrix with the units `d x` on the diagonal. -/
def diagonalUnits (d : l ⊕ l → Aˣ) : GL (l ⊕ l) A where
  val := Matrix.diagonal fun x => (d x : A)
  inv := Matrix.diagonal fun x => (((d x)⁻¹ : Aˣ) : A)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] theorem coe_diagonalUnits (d : l ⊕ l → Aˣ) :
    ((diagonalUnits d : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      Matrix.diagonal fun x => (d x : A) := rfl

@[simp] theorem coe_diagonalUnits_inv (d : l ⊕ l → Aˣ) :
    (↑(diagonalUnits d)⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) =
      Matrix.diagonal fun x => (((d x)⁻¹ : Aˣ) : A) := rfl

/-- A diagonal matrix whose entries at `inl a` and `inr a` multiply to `c` for every `a` is a
similitude with multiplier `c`. -/
theorem isSimilitude_diagonalUnits (d : l ⊕ l → Aˣ) (c : A)
    (hd : ∀ a, (d (Sum.inl a) : A) * d (Sum.inr a) = c) :
    IsSimilitude ((diagonalUnits d : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A) c := by
  have h : ((diagonalUnits d : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A) * formMatrix l A *
      ((diagonalUnits d : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A)ᵀ -
        c • formMatrix l A = 0 := by
    rw [coe_diagonalUnits, Matrix.diagonal_transpose]
    ext x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        formMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.one_apply, smul_eq_mul, mul_zero, zero_mul, sub_zero]
    split_ifs with hab
    · subst hab
      rw [mul_one, mul_one, hd, sub_self]
    · rw [mul_zero, zero_mul, mul_zero, sub_zero]
  unfold IsSimilitude
  rw [h]
  exact isAlt_zero

end Diagonal

/-- `lieMatrix` commutes with scalar multiplication. -/
theorem lieMatrix_smul {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A] (c : A)
    (X : Additive (lieKernel (groupScheme l R) A)) :
    lieMatrix (c • X) = c • lieMatrix X :=
  map_smul _ _ _

section Field

variable {k : Type u} [Field k]

/-- The commutative group structure of the Lie kernel of `SO_{2n}`, restated so that instance
search finds it directly. -/
local instance soKernelCommGroup :
    CommGroup (lieKernel (identityComponent (groupScheme l (CommRingCat.of k)))
      (CommRingCat.of k)) :=
  lieKernelCommGroup _

/-- The `k`-module structure of the Lie algebra of `SO_{2n}`, restated so that instance search
finds it directly. -/
local instance soKernelModule :
    Module k (Additive (lieKernel (identityComponent (groupScheme l (CommRingCat.of k)))
      (CommRingCat.of k))) :=
  lieKernelModule _

/-- The commutative group structure of the Lie kernel of `O_{2n}`, restated so that instance
search finds it directly. -/
local instance oKernelCommGroup :
    CommGroup (lieKernel (groupScheme l (CommRingCat.of k)) (CommRingCat.of k)) :=
  lieKernelCommGroup _

/-- The `k`-module structure of the Lie algebra of `O_{2n}`, restated so that instance search
finds it directly. -/
local instance oKernelModule :
    Module k (Additive (lieKernel (groupScheme l (CommRingCat.of k)) (CommRingCat.of k))) :=
  lieKernelModule _

/-- Conjugation by an invertible diagonal similitude fixes the diagonal torus pointwise. -/
theorem identityTorus_comp_specialConjIso (d : l ⊕ l → kˣ) (c : kˣ)
    (hd : IsSimilitude ((diagonalUnits d : GL (l ⊕ l) k) : Matrix (l ⊕ l) (l ⊕ l) k) (c : k)) :
    identityTorus l k ≫ (specialConjIso (diagonalUnits d) c hd).hom = identityTorus l k := by
  rw [← cancel_mono (identityComponentι (groupScheme l (CommRingCat.of k))), Category.assoc,
    specialConjIso_hom_identityComponentι, identityTorus_comp_assoc, identityTorus_comp]
  apply hom_ext_points
  intro T x
  apply (pointsEquiv l (CommRingCat.of k) T).injective
  apply Subtype.ext
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_conjMap, pointsEquiv_diagonalTorus,
    coe_leviHom, SymplecticMatrix.levi_diagonalTorusUnits, coe_diagonalUnits,
    coe_diagonalUnits_inv, Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [mul_comm (scalarMap T (d x : k)), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

set_option maxHeartbeats 800000 in
/-- On a weight space of the diagonal torus, the differential of conjugation by a diagonal
similitude `d` is multiplication by `e`, provided `d x / d y = e` at every matrix position
`(x, y)` of that weight. -/
theorem targetMapLinear_specialConjIso_diagonalUnits (d : l ⊕ l → kˣ) (c : kˣ)
    (hd : IsSimilitude ((diagonalUnits d : GL (l ⊕ l) k) : Matrix (l ⊕ l) (l ⊕ l) k) (c : k))
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)))
    (e : k)
    (he : ∀ x y : l ⊕ l, GeneralLinear.characterCoordEquiv l k χ =
      weightCoord l x - weightCoord l y → (d x : k) * ((d y)⁻¹ : kˣ) = e)
    {X : Additive (lieKernel (identityComponent (groupScheme l (CommRingCat.of k)))
      (CommRingCat.of k))}
    (hX : X ∈ weightSpace (identityTorus l k) χ) :
    Lie.targetMapLinear (specialConjIso (diagonalUnits d) c hd).hom (CommRingCat.of k) X =
      e • X := by
  have hX' := lieKernelHomLinear_mem_weightSpace
    (identityComponentι (groupScheme l (CommRingCat.of k))) (identityTorus l k) χ hX
  rw [identityTorus_comp] at hX'
  apply Lie.targetMapLinear_injective (identityComponentι (groupScheme l (CommRingCat.of k)))
    (CommRingCat.of k)
  apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
  erw [lieMatrix_targetMapLinear_specialConjIso]
  rw [map_smul]
  set Y := Lie.targetMapLinear (identityComponentι (groupScheme l (CommRingCat.of k)))
    (CommRingCat.of k) X with hY
  rw [show lieMatrix (e • Y) = e • lieMatrix Y from lieMatrix_smul (R := CommRingCat.of k) e Y]
  ext x y
  rw [coe_diagonalUnits, coe_diagonalUnits_inv, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : lieMatrix Y x y = 0
  · rw [hxy, mul_zero, zero_mul, mul_zero]
  · have hc := (mem_weightSpace_diagonalTorus_iff_support _ χ).mp hX' x y hxy
    rw [← he x y hc]
    ring

/-- **Root scaling.** An automorphism of `SO_{2n}`, `n ≥ 2`, that is the identity on the diagonal
torus is conjugation by a (diagonal) similitude. -/
theorem isSimilitudeConj_of_comp_identityTorus {n : ℕ} (hn : 2 ≤ n)
    (β : identityComponent (groupScheme (Fin n) (CommRingCat.of k)) ≅
      identityComponent (groupScheme (Fin n) (CommRingCat.of k)))
    (hβ : identityTorus (Fin n) k ≫ β.hom = identityTorus (Fin n) k) :
    IsSimilitudeConj β := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hG := isConnectedReductive_identityComponent (Fin n) k
  have hT := SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k
  have hi := isMaximalTorus_identityTorus (Fin n) k
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k _ hG _ hT (identityTorus (Fin n) k) hi
  have := hJ
  let p : SplitPinning (identityComponent (groupScheme (Fin n) (CommRingCat.of k))) :=
    SplitPinning.ofRootDatum hG hT (identityTorus (Fin n) k) hi P hP hred
      (splitRootLieLine k _ hG _ hT (identityTorus (Fin n) k) hi)
  have hβ' : p.inclusion ≫ β.hom = p.inclusion := hβ
  -- The differential of `β` scales each simple root vector by a nonzero scalar `s a`.
  have hw (a : p.base.support) :
      Lie.targetMapLinear β.hom (CommRingCat.of k) (p.pinning.rootVector a) ∈
        weightSpace p.inclusion (p.rootDatum.root a) := by
    have h := lieKernelHomLinear_mem_weightSpace β.hom p.inclusion (p.rootDatum.root a)
      (p.pinning.rootVector_mem a)
    rwa [hβ'] at h
  let s : p.base.support → k := fun a => (p.pinning.trivialization a).symm ⟨_, hw a⟩
  have hs (a : p.base.support) :
      Lie.targetMapLinear β.hom (CommRingCat.of k) (p.pinning.rootVector a) =
        s a • p.pinning.rootVector a := by
    rw [← p.pinning.trivialization_apply_val]
    simp only [s, LinearEquiv.apply_symm_apply]
  have hs0 (a : p.base.support) : s a ≠ 0 := by
    intro h0
    have h := hs a
    rw [h0, zero_smul] at h
    apply p.pinning.rootVector_ne_zero a
    have h' := congrArg (Lie.targetMapLinear β.inv (CommRingCat.of k)) h
    rwa [Lie.targetMapLinear_hom_inv, map_zero] at h'
  -- The homomorphism `H` on the root lattice with `H(α_a) = s_a⁻¹` on simple roots.
  let H : p.rootDatum.rootSpan ℤ →ₗ[ℤ] Additive kˣ :=
    p.base.toWeightBasisInt.constr ℤ fun a => Additive.ofMul (Units.mk0 (s a) (hs0 a))⁻¹
  -- Weight differences, as characters, lie in the root lattice.
  let χ : Fin n ⊕ Fin n → Fin n ⊕ Fin n →
      characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))) :=
    fun x y => (GeneralLinear.characterCoordEquiv (Fin n) k).symm
      (weightCoord (Fin n) x - weightCoord (Fin n) y)
  have hroot (x y : Fin n ⊕ Fin n) (hxy : index x ≠ index y) :
      χ x y ∈ p.rootDatum.rootSpan ℤ := by
    apply Submodule.subset_span
    rw [p.isRootDatum.2.1]
    change χ x y ∈ roots (identityTorus (Fin n) k)
    rw [roots_identityTorus, mem_roots_iff]
    exact ⟨x, y, hxy, LinearEquiv.apply_symm_apply _ _⟩
  have hmem (x y : Fin n ⊕ Fin n) : χ x y ∈ p.rootDatum.rootSpan ℤ := by
    by_cases hxy : index x = index y
    · obtain ⟨j, hj⟩ := exists_ne (index x)
      have e : χ x y = χ x (Sum.inl j) + χ (Sum.inl j) y := by
        simp only [χ, ← map_add]
        congr 1
        abel
      rw [e]
      refine add_mem (hroot _ _ ?_) (hroot _ _ ?_)
      · rw [index_inl]
        exact hj.symm
      · rw [index_inl, ← hxy]
        exact hj
    · exact hroot x y hxy
  -- The diagonal similitude.
  let i0 : Fin n := ⟨0, by omega⟩
  let dv : Fin n ⊕ Fin n → kˣ := fun x => Additive.toMul (H ⟨χ x (Sum.inl i0), hmem _ _⟩)
  have hdiv (x y : Fin n ⊕ Fin n) :
      (dv x : k) * ((dv y)⁻¹ : kˣ) = ((Additive.toMul (H ⟨χ x y, hmem x y⟩) : kˣ) : k) := by
    have e : (⟨χ x y, hmem x y⟩ : p.rootDatum.rootSpan ℤ) =
        ⟨χ x (Sum.inl i0), hmem _ _⟩ - ⟨χ y (Sum.inl i0), hmem _ _⟩ := by
      apply Subtype.ext
      show (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ =
        (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ -
          (GeneralLinear.characterCoordEquiv (Fin n) k).symm _
      rw [← map_sub]
      congr 1
      abel
    rw [e, map_sub, toMul_sub, div_eq_mul_inv, Units.val_mul]
  let c : kˣ := dv (Sum.inl i0) * dv (Sum.inr i0)
  have hc (a : Fin n) : (dv (Sum.inl a) : k) * dv (Sum.inr a) = c := by
    have hsum : (⟨χ (Sum.inl a) (Sum.inl i0), hmem _ _⟩ : p.rootDatum.rootSpan ℤ) +
        ⟨χ (Sum.inr a) (Sum.inl i0), hmem _ _⟩ =
        ⟨χ (Sum.inl i0) (Sum.inl i0), hmem _ _⟩ + ⟨χ (Sum.inr i0) (Sum.inl i0), hmem _ _⟩ := by
      apply Subtype.ext
      show (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ +
          (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ =
        (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ +
          (GeneralLinear.characterCoordEquiv (Fin n) k).symm _
      rw [← map_add, ← map_add]
      congr 1
      simp only [weightCoord_inl, weightCoord_inr, Pi.single_neg]
      abel
    have h := congrArg (fun z => ((Additive.toMul (H z) : kˣ) : k)) hsum
    simpa only [map_add, toMul_add, Units.val_mul, c, dv] using h
  have hD := isSimilitude_diagonalUnits dv (c : k) hc
  -- Conjugation by the diagonal similitude scales the simple root vectors by `s a⁻¹`.
  have hLie (a : p.base.support) :
      Lie.targetMapLinear (specialConjIso (diagonalUnits dv) c hD).hom (CommRingCat.of k)
        (p.pinning.rootVector a) = (s a)⁻¹ • p.pinning.rootVector a := by
    refine targetMapLinear_specialConjIso_diagonalUnits dv c hD (p.rootDatum.root a) (s a)⁻¹
      ?_ (p.pinning.rootVector_mem a)
    intro x y hxy
    have e1 : (⟨χ x y, hmem x y⟩ : p.rootDatum.rootSpan ℤ) = p.base.toWeightBasisInt a := by
      apply Subtype.ext
      rw [RootPairing.Base.coe_toWeightBasisInt_apply]
      change (GeneralLinear.characterCoordEquiv (Fin n) k).symm _ = _
      rw [← hxy, LinearEquiv.symm_apply_apply]
    rw [hdiv, e1, Module.Basis.constr_basis]
    simp
  -- The composite fixes the pinning, hence is the identity.
  have h1 : p.inclusion ≫ (β ≪≫ specialConjIso (diagonalUnits dv) c hD).hom = p.inclusion := by
    change identityTorus (Fin n) k ≫ β.hom ≫ (specialConjIso (diagonalUnits dv) c hD).hom =
      identityTorus (Fin n) k
    rw [← Category.assoc, hβ, identityTorus_comp_specialConjIso]
  have h2 (a : p.base.support) :
      Lie.targetMapLinear (β ≪≫ specialConjIso (diagonalUnits dv) c hD).hom (CommRingCat.of k)
        (p.pinning.rootVector a) = p.pinning.rootVector a := by
    change Lie.targetMapLinear (β.hom ≫ (specialConjIso (diagonalUnits dv) c hD).hom)
      (CommRingCat.of k) (p.pinning.rootVector a) = _
    rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, hs a, map_smul, hLie a, smul_smul,
      mul_inv_cancel₀ (hs0 a), one_smul]
  have hr := pinnedAutomorphismRigidity k _ p _ h1 h2
  refine IsSimilitudeConj.of_trans ?_ (isSimilitudeConj_specialConjIso (diagonalUnits dv) c hD)
  rw [hr]
  exact isSimilitudeConj_refl

end Field

end Langlands.GroupScheme.OrthogonalMatrix
