import Langlands.GroupScheme.SymplecticInnerForm.InvolutionModel
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.CentralSimpleNormOneTransport

/-! # Transport from involution isometries to division-form symplectic groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {K A B : Type u} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
  [FiniteDimensional K A] [FiniteDimensional K B]

/-- Tensor transport of units, expressed in the canonical coordinates on every test. -/
def algEquivPointIso (e : A ≃ₐ[K] B) (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme (Module.finBasis K A)).X) ≃*
      (T ⟶ (groupScheme (Module.finBasis K B)).X) :=
  ((pointsEquiv (Module.finBasis K A) T).trans
    (Units.mapEquiv (Algebra.TensorProduct.congr
      (AlgEquiv.refl : ((algΓ (CommRingCat.of K)).obj T).unop ≃ₐ[
        ((algΓ (CommRingCat.of K)).obj T).unop]
          ((algΓ (CommRingCat.of K)).obj T).unop) e).toMulEquiv)).trans
    (pointsEquiv (Module.finBasis K B) T).symm

theorem pointsEquiv_algEquivPointIso (e : A ≃ₐ[K] B)
    (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (Module.finBasis K A)).X) :
    pointsEquiv (Module.finBasis K B) T (algEquivPointIso e T x) =
      Units.map (Algebra.TensorProduct.map
        (AlgHom.id ((algΓ (CommRingCat.of K)).obj T).unop
          ((algΓ (CommRingCat.of K)).obj T).unop) e.toAlgHom).toMonoidHom
        (pointsEquiv (Module.finBasis K A) T x) :=
  MulEquiv.apply_symm_apply _ _

/-- Tensor transport commutes with restriction along any relative test morphism. -/
theorem algEquivPointIso_naturality (e : A ≃ₐ[K] B)
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme (Module.finBasis K A)).X) :
    algEquivPointIso e T' (a ≫ x) = a ≫ algEquivPointIso e T x := by
  apply (pointsEquiv (Module.finBasis K B) T').injective
  rw [pointsEquiv_algEquivPointIso, pointsEquiv_naturality,
    pointsEquiv_naturality, pointsEquiv_algEquivPointIso]
  apply Units.ext
  change Algebra.TensorProduct.map (AlgHom.id _ _) e.toAlgHom
      (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
        (AlgHom.id K A) _) =
    Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
      (AlgHom.id K B) (Algebra.TensorProduct.map (AlgHom.id _ _) e.toAlgHom _)
  induction (pointsEquiv (Module.finBasis K A) T x).val using TensorProduct.inductionOn with
  | tmul r z => rfl
  | add z z' hz hz' => simp only [_root_.map_add, hz, hz']

/-- An algebra equivalence induces an actual isomorphism of algebra-unit group schemes. -/
def algEquivIso (e : A ≃ₐ[K] B) :
    groupScheme (Module.finBasis K A) ≅ groupScheme (Module.finBasis K B) :=
  isoOfPoints (algEquivPointIso e) (algEquivPointIso_naturality e)

theorem pointsEquiv_comp_algEquivIso_hom (e : A ≃ₐ[K] B)
    (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (Module.finBasis K A)).X) :
    pointsEquiv (Module.finBasis K B) T (x ≫ (algEquivIso e).hom.hom.hom) =
      Units.map (Algebra.TensorProduct.map
        (AlgHom.id ((algΓ (CommRingCat.of K)).obj T).unop
          ((algΓ (CommRingCat.of K)).obj T).unop) e.toAlgHom).toMonoidHom
        (pointsEquiv (Module.finBasis K A) T x) := by
  rw [algEquivIso, comp_isoOfPoints_hom, pointsEquiv_algEquivPointIso]

end Langlands.GroupScheme.FiniteAlgebraUnits

namespace Langlands.GroupScheme.CentralSimpleUnits

variable {K A B : Type u} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]

/-- The actual reduced-norm characters commute with algebra transport. -/
theorem algEquivIso_comp_reducedNormHom (e : A ≃ₐ[K] B) :
    (FiniteAlgebraUnits.algEquivIso e).hom ≫ reducedNormHom K B =
      reducedNormHom K A := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, reducedNormHom_points,
    FiniteAlgebraUnits.pointsEquiv_comp_algEquivIso_hom,
    Langlands.CentralSimple.reducedNormUnits_algEquiv, reducedNormHom_points]

end Langlands.GroupScheme.CentralSimpleUnits

namespace Langlands.GroupScheme.SymplecticInnerForm

open Quaternionic

section Algebra

variable {K A B : Type u} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
  (τ : FirstKindInvolution K A) (ν : FirstKindInvolution K B)
  (e : A ≃ₐ[K] B) (H : B)
  (he : ∀ x, e (τ x) * H = H * ν (e x))
  (R : Type u) [CommRing R] [Algebra K R]

include he

/-- An adjoint compatibility identity persists after arbitrary scalar extension. -/
theorem tensor_adjoint_compatibility (x : R ⊗[K] A) :
    Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom (τ.baseChange R x) *
        ((1 : R) ⊗ₜ[K] H) =
      ((1 : R) ⊗ₜ[K] H) * ν.baseChange R
        (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simpa only [FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul] using
      congrArg (fun b : B => r ⊗ₜ[K] b) (he a)
  | add x y hx hy =>
    simp only [_root_.map_add, add_mul, mul_add, hx, hy]

/-- Invertibility of the Gram element identifies the two isometry equations over every
coefficient algebra. -/
theorem tensor_isometry_iff (hH : IsUnit H) (x : R ⊗[K] A) :
    Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom x *
        ((1 : R) ⊗ₜ[K] H) *
        ν.baseChange R (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom x) =
      ((1 : R) ⊗ₜ[K] H) ↔
        x * τ.baseChange R x = 1 := by
  rw [mul_assoc, ← tensor_adjoint_compatibility τ ν e H he R x, ← mul_assoc,
    ← _root_.map_mul]
  have hHR : IsUnit ((1 : R) ⊗ₜ[K] H) :=
    hH.map (Algebra.TensorProduct.includeRight : B →ₐ[K] R ⊗[K] B).toMonoidHom
  rw [hHR.mul_eq_right]
  let eR := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e
  change eR (x * τ.baseChange R x) = 1 ↔ x * τ.baseChange R x = 1
  constructor
  · intro h
    apply eR.injective
    simpa only [_root_.map_one] using h
  · intro h
    rw [h, _root_.map_one]

end Algebra

section GroupScheme

variable {K A D : Type u} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [Algebra.IsCentral K D]
  (τ : FirstKindInvolution K A) (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  (e : A ≃ₐ[K] Matrix n n D) (H : Matrix n n D) (hH : IsUnit H)
  (he : ∀ x, e (τ x) * H = H * σ.matrix n (e x))

include hH he

/-- The ambient algebra-unit comparison identifies the full subgroup functors, including
the reduced-norm-one conditions, on every relative test scheme. -/
theorem comap_algEquivIso :
    (SubgroupFunctor.range (σ.symplecticAmbientι H)).comap
        (FiniteAlgebraUnits.algEquivIso e).hom =
      SubgroupFunctor.range (normOneAmbientι τ) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.mem_comap, FirstKindInvolution.mem_range_symplecticAmbientι_iff,
    mem_range_normOneAmbientι_iff]
  refine and_congr ?_ ?_
  · rw [FirstKindInvolution.mem_range_unitaryGroupι_iff, mem_range_isometryι_iff,
      FiniteAlgebraUnits.pointsEquiv_comp_algEquivIso_hom]
    exact tensor_isometry_iff τ (σ.matrix n) e H he _ hH _
  · rw [Category.assoc, ← Grp.comp_hom_hom,
      CentralSimpleUnits.algEquivIso_comp_reducedNormHom]

/-- A compatible division-form algebra model gives the actual symplectic group scheme. -/
def normOneGroupAlgEquivIso : normOneGroup τ ≅ σ.symplecticGroup H :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap (isRepresentedBy_normOneAmbientι τ)
    (σ.isRepresentedBy_symplecticAmbientι H) (FiniteAlgebraUnits.algEquivIso e)
    (comap_algEquivIso τ σ e H hH he)

/-- The comparison intertwines the two ambient inclusions with the original algebra map. -/
@[reassoc] theorem normOneGroupAlgEquivIso_hom_comp :
    (normOneGroupAlgEquivIso τ σ e H hH he).hom ≫ σ.symplecticAmbientι H =
      normOneAmbientι τ ≫ (FiniteAlgebraUnits.algEquivIso e).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp _ _ _ _

end GroupScheme

end Langlands.GroupScheme.SymplecticInnerForm
