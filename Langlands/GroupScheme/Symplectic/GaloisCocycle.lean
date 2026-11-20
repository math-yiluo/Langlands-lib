import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Symplectic.Basic
import Langlands.GroupScheme.SymplecticMatrix.GaloisCoboundary

/-! # Galois cocycles of the split symplectic group scheme -/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace Langlands.GroupScheme.Symplectic

variable (K : Type u) [Field K] (n : ℕ)

local notation "I" => Fin n ⊕ Fin n
local notation "A" => Matrix I I K
local notation "B" => Module.finBasis K A
local notation "U" => FiniteAlgebraUnits.groupScheme B
local notation "Rₐ" R => CommAlgCat.of K R

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

/-- Affine points of the ambient units are invertible matrices over the test algebra. -/
def affineMatrixEquiv (R : Type u) [CommRing R] [Algebra K R] :
    (U).affinePoints (Rₐ R) ≃* GL I R :=
  (FiniteAlgebraUnits.affinePointsEquiv B (Rₐ R)).trans
    (Units.mapEquiv (coefficientEquiv (s := I) K R).toMulEquiv)

private theorem coefficientEquiv_map (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    coefficientEquiv K S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      (coefficientEquiv K R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    ext i j
    simp [coefficientEquiv_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (Matrix.map_add f (map_add f) _ _).symm

/-- The affine matrix comparison follows actual coefficient maps. -/
theorem affineMatrixEquiv_naturality (f : R →ₐ[K] S) (x : (U).affinePoints (Rₐ R)) :
    affineMatrixEquiv K n S ((U).affinePointMap (CommAlgCat.ofHom f) x) =
      GeneralLinearGroup.map f.toRingHom (affineMatrixEquiv K n R x) := by
  apply Units.ext
  change coefficientEquiv K S (FiniteAlgebraUnits.affinePointsEquiv B (Rₐ S)
    (((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) ≫ x)).val =
      (coefficientEquiv K R (FiniteAlgebraUnits.affinePointsEquiv B (Rₐ R) x).val).map f
  rw [FiniteAlgebraUnits.affinePointsEquiv_naturality]
  exact coefficientEquiv_map K n f _

/-- The represented range at an affine algebra is exactly the symplectic condition. -/
theorem mem_range_inclusion_affine_iff (x : (U).affinePoints (Rₐ R)) :
    x ∈ (SubgroupFunctor.range (inclusion K n)).carrier
      ((algSpec (CommRingCat.of K)).obj (op (Rₐ R))) ↔
    (affineMatrixEquiv K n R x : Matrix I I R) ∈ Matrix.symplecticGroup (Fin n) R := by
  let T := (algSpec (CommRingCat.of K)).obj (op (Rₐ R))
  let S := ((algΓ (CommRingCat.of K)).obj T).unop
  let e := Corepresented.affineSectionsIso (R := CommRingCat.of K) (Rₐ R)
  let f : S →ₐ[K] R := e.hom.hom
  have hf : Function.Injective f := (ConcreteCategory.bijective_of_isIso e.hom).1
  let m : Matrix I I S := (ambientPointsEquiv K n T x).val
  have hm : (affineMatrixEquiv K n R x).val = m.map f := by
    have h := Corepresented.map_affineSectionsIso_pointsEquiv
      (FiniteAlgebraUnits.functor K A) (FiniteAlgebraUnits.corepresentableBy B) (Rₐ R) x
    have h' := congrArg Units.val h
    change Algebra.TensorProduct.map f (AlgHom.id K A)
        (FiniteAlgebraUnits.pointsEquiv B T x).val =
      (FiniteAlgebraUnits.affinePointsEquiv B (Rₐ R) x).val at h'
    change coefficientEquiv K R (FiniteAlgebraUnits.affinePointsEquiv B (Rₐ R) x).val = _
    rw [← h', coefficientEquiv_map]
    rfl
  rw [mem_range_inclusion_iff, hm, SymplecticGroup.mem_iff, SymplecticGroup.mem_iff]
  have hmap : (m * J (Fin n) S * mᵀ).map f = m.map f * J (Fin n) R * (m.map f)ᵀ := by
    simp only [Matrix.map_mul, Matrix.map_J, Matrix.transpose_map]
  rw [← hmap, ← Matrix.map_J (R := S) (Fin n) f]
  exact ⟨congrArg (fun m : Matrix I I S => m.map f), fun h => by
    ext i j
    exact hf (congrArg (fun m : Matrix I I R => m i j) h)⟩

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every cocycle of the actual split symplectic group on the finite Galois cover is trivial. -/
theorem isTrivial_galoisCocycle (ξ : Cocycle (groupScheme K n) (GaloisCocycle.cover K L)) :
    ξ.IsTrivial := by
  let G := groupScheme K n
  let incl := inclusion K n
  let E := affineMatrixEquiv K n L
  let j := G.affinePointsTarget incl (Rₐ L)
  let e := E.toMonoidHom.comp j
  have : IsClosedImmersion incl.hom.hom.left := isClosedSubgroup_inclusion K n
  have : Mono incl.hom.hom := Over.mono_of_mono_left _
  have he : Function.Injective e := by
    intro a b hab
    exact (cancel_mono incl.hom.hom).mp (E.injective hab)
  have hact (σ : L ≃ₐ[K] L) (x : G.affinePoints (Rₐ L)) :
      e (GaloisPoint.conjugate K L G σ x) = GeneralLinearGroup.map σ.toRingHom (e x) := by
    change E ((GaloisCocycle.arrow K L σ ≫ x) ≫ incl.hom.hom) = _
    rw [Category.assoc]
    exact affineMatrixEquiv_naturality K n σ.toAlgHom (j x)
  let c (σ : L ≃ₐ[K] L) := e (GaloisCocycle.value ξ σ)
  have hc (σ τ : L ≃ₐ[K] L) : c (σ * τ) = c σ * GeneralLinearGroup.map σ.toRingHom (c τ) := by
    change e (GaloisCocycle.value ξ (σ * τ)) = _
    rw [GaloisCocycle.value_mul, map_mul, hact]
  have hs (σ : L ≃ₐ[K] L) :
      (c σ : Matrix I I L) ∈ Matrix.symplecticGroup (Fin n) L :=
    (mem_range_inclusion_affine_iff K n (j (GaloisCocycle.value ξ σ))).mp ⟨_, rfl⟩
  obtain ⟨b, hb, hcob⟩ := SymplecticMatrix.exists_symplectic_coboundary c hc hs
  have hx : E.symm b ∈ (SubgroupFunctor.range incl).carrier (GaloisCocycle.cover K L) := by
    apply (mem_range_inclusion_affine_iff K n (E.symm b)).mpr
    change (E (E.symm b) : Matrix I I L) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hb
  change ∃ a : G.affinePoints (Rₐ L), a ≫ incl.hom.hom = E.symm b at hx
  obtain ⟨a, ha⟩ := hx
  have hab : e a = b := by
    change E (a ≫ incl.hom.hom) = b
    rw [ha, MulEquiv.apply_symm_apply]
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨a, fun σ => he ?_⟩
  change c σ = e (a * (GaloisPoint.conjugate K L G σ a)⁻¹)
  rw [map_mul, map_inv, hact, hab]
  exact eq_mul_inv_of_mul_eq (hcob σ)

/-- The split symplectic group has trivial finite Galois cocycles. -/
def SplitSymplecticGaloisCocycleStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (ξ : Cocycle (groupScheme K n) (GaloisCocycle.cover K L)), ξ.IsTrivial

/-- Hilbert 90 for the actual split symplectic group scheme. -/
theorem splitSymplecticGaloisCocycle : SplitSymplecticGaloisCocycleStatement.{u} := by
  intro K L _ _ _ _ _ n ξ
  exact isTrivial_galoisCocycle K n ξ

end Langlands.GroupScheme.Symplectic
