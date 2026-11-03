import Langlands.GroupScheme.Rational.KernelCentralizerLie
import Langlands.GroupScheme.Lie.ActionDifferential

/-! # Tangents of all-test fixed subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}}
    {A : Type u} [CommRing A] [Algebra R A]

/-- Specializing epsilon to any square-zero element is an actual algebra map. -/
def epsilonSpecialization (e : A) (he : e * e = 0) : DualNumber A →ₐ[R] A :=
  (TrivSqZeroExt.liftEquivOfComm
    ⟨e • (LinearMap.id : A →ₗ[A] A), by
      intro x y
      change (e * x) * (e * y) = 0
      calc
        (e * x) * (e * y) = (e * e) * (x * y) := by ring
        _ = 0 := by rw [he, zero_mul]⟩).restrictScalars R

@[simp] theorem epsilonSpecialization_apply (e : A) (he : e * e = 0)
    (z : DualNumber A) :
    epsilonSpecialization (R := R) e he z = z.fst + e * z.snd := rfl

@[simp] theorem epsilonSpecialization_comp_inl (e : A) (he : e * e = 0) :
    (epsilonSpecialization (R := R) e he).comp (TrivSqZeroExt.inlAlgHom R A A) =
      AlgHom.id R A := by
  ext z
  simp

/-- The epsilon image of any dual-number algebra map is square zero. -/
theorem epsilon_image_square_zero (f : DualNumber R →ₐ[R] A) :
    f (TrivSqZeroExt.inr (1 : R)) * f (TrivSqZeroExt.inr (1 : R)) = 0 := by
  rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

/-- Any map from the base dual numbers is coefficient change followed by specialization. -/
theorem epsilonSpecialization_comp_coefficients (f : DualNumber R →ₐ[R] A) :
    (epsilonSpecialization (f (TrivSqZeroExt.inr (1 : R)))
      (epsilon_image_square_zero f)).comp
        (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) = f := by
  apply TrivSqZeroExt.algHom_ext
  intro r
  simp only [AlgHom.comp_apply, epsilonSpecialization_apply]
  change algebraMap R A 0 + f (TrivSqZeroExt.inr (1 : R)) * algebraMap R A r =
    f (TrivSqZeroExt.inr r)
  rw [map_zero, zero_add]
  have hr : TrivSqZeroExt.inr r =
      r • (TrivSqZeroExt.inr (1 : R) : DualNumber R) := by
    simp
  rw [hr, map_smul]
  simp [Algebra.smul_def, mul_comm]

end Lie

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (a : AutomorphicAction H G)

/-- Invariance on every affine refinement implies invariance on every scheme refinement. -/
theorem isFixed_of_affine {T : Over (Spec R)} (g : T ⟶ G.X)
    (h : ∀ (A : CommAlgCat.{u} R)
      (b : (algSpec R).obj (op A) ⟶ T)
      (c : (algSpec R).obj (op A) ⟶ H.X), a.act c (b ≫ g) = b ≫ g) :
    a.IsFixed g := by
  intro V b c
  apply Over.OverMorphism.ext
  apply V.left.affineCover.hom_ext
  intro j
  let W : Over (Spec R) := Over.mk (V.left.affineCover.f j ≫ V.hom)
  let : IsAffine W.left := inferInstanceAs (IsAffine (V.left.affineCover.X j))
  let jW : W ⟶ V := Over.homMk (V.left.affineCover.f j)
  obtain ⟨D, ⟨e⟩⟩ := (essImage_algSpec (G := W)).mpr inferInstance
  have hh : jW ≫ a.act c (b ≫ g) = jW ≫ b ≫ g := by
    apply (cancel_epi e.hom).mp
    simpa only [a.naturality, Category.assoc] using
      h D.unop (e.hom ≫ jW ≫ b) (e.hom ≫ jW ≫ c)
  exact congrArg (fun f => f.left) hh

variable [IsAffineHom G.X.hom]

/-- The submodule fixed by all pointwise differentials over all coefficient algebras. -/
def lieInvariants : Submodule R (Additive (lieKernel G R)) where
  carrier := {X | ∀ (A : Type u) [CommRing A] [Algebra R A]
    (h : Lie.AffinePoints H A),
      a.differential h (lieKernelMapLinear G (Algebra.ofId R A) X) =
        lieKernelMapLinear G (Algebra.ofId R A) X}
  zero_mem' := by
    intro A _ _ h
    simp only [map_zero]
  add_mem' := by
    intro X Y hX hY A _ _ h
    simp only [map_add, hX A h, hY A h]
  smul_mem' := by
    intro r X hX A _ _ h
    rw [LinearMap.map_smulₛₗ, LinearEquiv.map_smul, hX A h]

/-- All-refinement tangent invariance equals differential invariance over all algebras. -/
theorem isFixed_iff_mem_lieInvariants (X : Additive (lieKernel G R)) :
    a.IsFixed X.toMul.val ↔ X ∈ a.lieInvariants := by
  constructor
  · intro hX A _ _ h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hX _ ((algSpec R).map (CommAlgCat.ofHom
      (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A))).op)
        (Lie.constant H h)
  · intro hX
    apply a.isFixed_of_affine
    intro B b h
    let f : DualNumber R →ₐ[R] B := (algSpec.fullyFaithful.preimage b).unop.hom
    let q : DualNumber B →ₐ[R] B :=
      Lie.epsilonSpecialization (f (TrivSqZeroExt.inr (1 : R)))
        (Lie.epsilon_image_square_zero f)
    have hb : (algSpec R).map (CommAlgCat.ofHom f).op = b :=
      algSpec.fullyFaithful.map_preimage b
    have hc : Lie.affineMap H q (Lie.constant H h) = h := by
      simp only [Lie.constant, ← Lie.affineMap_comp, q,
        Lie.epsilonSpecialization_comp_inl, Lie.affineMap_id]
    have hz : Lie.affineMap G q
        (lieKernelMapLinear G (Algebra.ofId R B) X).toMul.val = b ≫ X.toMul.val := by
      change Lie.affineMap G q (Lie.affineMap G
        (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R B)) X.toMul.val) = _
      rw [← Lie.affineMap_comp, Lie.epsilonSpecialization_comp_coefficients]
      rw [Lie.affineMap_apply, hb]
    have hi := congrArg (fun Y : Additive (lieKernel G B) =>
      Lie.affineMap G q Y.toMul.val) (hX B h)
    rw [a.differential_val, a.affineAct_naturality, hc, hz] at hi
    exact hi

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Differentiating the restricted conjugation action gives the actual kernel invariants. -/
theorem lieInvariants_kernelConjugation (i : T.toGrp ⟶ G) (a : characterLattice T) :
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a)).lieInvariants =
      kernelLieInvariants i a := by
  ext X
  constructor
  · intro hX B _ _ c
    simpa only [AutomorphicAction.differential_restrict,
      AutomorphicAction.differential_conjugation, Grp.comp_hom_hom,
      Category.assoc] using hX B c
  · intro hX B _ _ c
    simpa only [AutomorphicAction.differential_restrict,
      AutomorphicAction.differential_conjugation, Grp.comp_hom_hom,
      Category.assoc] using hX B c

/-- The actual all-test kernel centralizer has exactly the invariant tangent image. -/
theorem kernelCentralizer_hasLieImage (i : T.toGrp ⟶ G) (a : characterLattice T) :
    HasLieImage (kernelCentralizer i a) (kernelLieInvariants i a) := by
  intro X
  change ((AutomorphicAction.conjugation i).restrict (characterKernelι a)).IsFixed
    X.toMul.val ↔ _
  rw [AutomorphicAction.isFixed_iff_mem_lieInvariants, lieInvariants_kernelConjugation]

end RelativeRoot

end Langlands.GroupScheme
