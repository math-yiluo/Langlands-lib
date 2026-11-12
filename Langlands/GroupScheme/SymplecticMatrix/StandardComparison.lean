import Langlands.GroupScheme.SymplecticMatrix.Reductive
import Langlands.GroupScheme.Symplectic.AlgebraicModel
import Langlands.GroupScheme.Quaternionic.SymplecticReductive
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Comparison with the standard symplectic model

The Library's standard symplectic group `Symplectic.groupScheme K n` is the unitary group of the
standard alternating matrix `J` inside the unit group of `M_{2n}(K)`. This module identifies it
with the coordinate model `SymplecticMatrix.groupScheme (Fin n) K` (`comparisonIso`); both have
the symplectic matrices `Matrix.symplecticGroup (Fin n) Γ(T, ⊤)` as points on every test
scheme. Consequently `Symplectic.groupScheme K n` is connected reductive
(`Symplectic.isConnectedReductive_groupScheme`), and the quaternionic symplectic group
`σ.symplecticGroup H` has a standard symplectic model of size `card n` over a finite Galois
extension (`FirstKindInvolution.nonempty_algebraicModel`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Symplectic

variable (K : Type u) [Field K]

/-- The scalar-extension isomorphism `R ⊗[K] M_s(K) ≃ M_s(R)` commutes with coefficient
changes. -/
theorem coefficientEquiv_naturality {s : Type} [Fintype s] [DecidableEq s] {R R' : Type u}
    [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (f : R →ₐ[K] R')
    (x : R ⊗[K] Matrix s s K) :
    coefficientEquiv K R' (Algebra.TensorProduct.map f (AlgHom.id K _) x) =
      (coefficientEquiv K R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coefficientEquiv_tmul, Matrix.map_apply,
      coefficientEquiv_tmul, _root_.map_mul, AlgHom.commutes]
  | add x y hx hy =>
    rw [_root_.map_add, _root_.map_add, hx, hy, _root_.map_add, Matrix.map_add _ (_root_.map_add f)]

variable (n : ℕ)

/-- Points of the standard model as symplectic matrices. -/
def standardPointsHom (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme K n).X) →*
      Matrix.symplecticGroup (Fin n) ((algΓ (CommRingCat.of K)).obj T).unop :=
  ((Units.coeHom _).comp ((ambientPointsEquiv K n T).toMonoidHom.comp
      ((yonedaGrp.map (inclusion K n)).app (Opposite.op T)).hom)).codRestrict
    (Matrix.symplecticGroup (Fin n) ((algΓ (CommRingCat.of K)).obj T).unop)
    (fun x => (mem_range_inclusion_iff K n _).1 (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩))

theorem standardPointsHom_apply (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme K n).X) :
    (standardPointsHom K n T x :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ((algΓ (CommRingCat.of K)).obj T).unop) =
      (ambientPointsEquiv K n T (x ≫ (inclusion K n).hom.hom) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ((algΓ (CommRingCat.of K)).obj T).unop) :=
  rfl

theorem standardPointsHom_bijective (T : Over (Spec (CommRingCat.of K))) :
    Function.Bijective (standardPointsHom K n T) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [standardPointsHom_apply, standardPointsHom_apply] at h1
    have h2 := (ambientPointsEquiv K n T).injective (Units.ext h1)
    have := (isClosedSubgroup_inclusion K n).mono_overHom
    exact (cancel_mono _).1 h2
  · intro g
    set y := (ambientPointsEquiv K n T).symm (SymplecticMatrix.toGL g)
    have hy : y ∈ (SubgroupFunctor.range (inclusion K n)).carrier T := by
      rw [mem_range_inclusion_iff, MulEquiv.apply_symm_apply]
      exact g.2
    obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.1 hy
    refine ⟨x, Subtype.ext ?_⟩
    rw [standardPointsHom_apply, hx, MulEquiv.apply_symm_apply]
    rfl

/-- Points of the standard model are symplectic matrices over the global sections. -/
def standardPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme K n).X) ≃* Matrix.symplecticGroup (Fin n) Γ(T.left, ⊤) :=
  MulEquiv.ofBijective (standardPointsHom K n T) (standardPointsHom_bijective K n T)

theorem ambientPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (y : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))).X) :
    (ambientPointsEquiv K n T' (a ≫ y) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ((algΓ (CommRingCat.of K)).obj T').unop) =
      (ambientPointsEquiv K n T y :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ((algΓ (CommRingCat.of K)).obj T).unop).map
        ((algΓ (CommRingCat.of K)).map a).unop.hom := by
  have h := FiniteAlgebraUnits.pointsEquiv_naturality
    (Module.finBasis K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) a y
  have h' := congrArg (fun u : (((algΓ (CommRingCat.of K)).obj T').unop ⊗[K]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ˣ =>
    coefficientEquiv (s := Fin n ⊕ Fin n) K ((algΓ (CommRingCat.of K)).obj T').unop
      (u : ((algΓ (CommRingCat.of K)).obj T').unop ⊗[K] _)) h
  exact h'.trans (coefficientEquiv_naturality K ((algΓ (CommRingCat.of K)).map a).unop.hom _)

theorem standardPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme K n).X) :
    standardPointsEquiv K n T' (a ≫ x) =
      SymplecticMatrix.map (Fin n) a.left.appTop.hom (standardPointsEquiv K n T x) := by
  apply Subtype.ext
  have h := ambientPointsEquiv_naturality K n a (x ≫ (inclusion K n).hom.hom)
  rw [← Category.assoc] at h
  exact h

end Symplectic

namespace SymplecticMatrix

variable (K : Type u) [Field K] (n : ℕ)

/-- The coordinate model and the standard model of `Sp_{2n}` are isomorphic. -/
def comparisonIso :
    groupScheme (Fin n) (CommRingCat.of K) ≅ Symplectic.groupScheme K n :=
  isoOfPointModels (fun T => Matrix.symplecticGroup (Fin n) Γ(T.left, ⊤))
    (fun a => map (Fin n) a.left.appTop.hom)
    (pointsEquiv (Fin n) (CommRingCat.of K)) (Symplectic.standardPointsEquiv K n)
    (fun a x => pointsEquiv_naturality a x) (Symplectic.standardPointsEquiv_naturality K n)

end SymplecticMatrix

namespace Symplectic

variable (K : Type u) [Field K] (n : ℕ)

/-- The standard symplectic group over a field is connected reductive. -/
theorem isConnectedReductive_groupScheme : IsConnectedReductive (groupScheme K n) :=
  IsConnectedReductive.of_iso (SymplecticMatrix.comparisonIso K n).symm
    (SymplecticMatrix.isConnectedReductive (Fin n) K)

end Symplectic

namespace Quaternionic.FirstKindInvolution

/-- The quaternionic symplectic group has a standard symplectic model of size `card n` over a
finite Galois splitting field of `D`. -/
theorem nonempty_algebraicModel {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (hD : finrank K D = 4)
    (σ : FirstKindInvolution K D) (hσ : finrank K σ.symmetricSubspace = 3) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (H : Matrix n n D) (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) :
    Nonempty (Symplectic.AlgebraicModel (σ.symplecticGroup H) (Fintype.card n)) := by
  let L := CentralSimple.finiteGaloisSplittingField K D
  let e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L :=
    (CentralSimple.finiteGaloisSplittingChart K D).trans
      (Matrix.reindexAlgEquiv L L (finCongr (reducedDegree_eq_two hD)))
  obtain ⟨k, P, P', hPP', hP'P, hPC⟩ := SymplecticMatrix.exists_mul_mul_transpose_eq_J
    (σ.splitGram e H) (σ.transpose_splitGram e hσ hH) (σ.splitGram_diag e hσ hH)
    (σ.det_splitGram_ne_zero e hu)
  have hk : k = Fintype.card n := by
    have h := card_eq_of_mul_eq_one hPP' hP'P
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at h
    omega
  exact ⟨{ extension := L
           isAlgebraic := inferInstance
           iso := (σ.splittingIso e H P P' hPP' hP'P hPC) ≪≫
             SymplecticMatrix.comparisonIso L k ≪≫ eqToIso (by rw [hk]) }⟩

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
