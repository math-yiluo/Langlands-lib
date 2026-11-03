import Langlands.GroupScheme.Lie.SubgroupTangent
import Langlands.GroupScheme.Lie.Adjoint

/-! # The actual adjoint stabilizer of a Lie element -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A B C : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

@[simp] theorem lieKernelMap_id (x : lieKernel G A) :
    lieKernelMap G (AlgHom.id R A) x = x := by
  apply Subtype.ext
  change Lie.affineMap G _ x.val = x.val
  have h : GeneralLinear.DualNumber.coefficientAlgMap (AlgHom.id R A) =
      AlgHom.id R (DualNumber A) := by
    ext z <;> rfl
  rw [h, Lie.affineMap_id]

/-- Composition of coefficient maps agrees with actual restriction of points. -/
theorem lieKernelMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (x : lieKernel G A) :
    lieKernelMap G (g.comp f) x = lieKernelMap G g (lieKernelMap G f x) := by
  apply Subtype.ext
  simp only [lieKernelMap_val, ← Lie.affineMap_comp]
  rfl

namespace Lie

/-- A point belongs to the Lie-element centralizer when, on every affine
refinement, its constant dual-number lift commutes with the extended tangent
point. This is the all-test adjoint stabilizer of the actual Lie element. -/
def elementCentralizer (X : lieKernel G R) : SubgroupFunctor G where
  carrier U :=
    { carrier := {g | ∀ (A : Type u) [CommRing A] [Algebra R A]
          (a : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ U),
        Commute (constant G (a ≫ g)) (lieKernelMap G (Algebra.ofId R A) X).val}
      one_mem' := by
        intro A _ _ a
        simp only [MonObj.comp_one, map_one, Commute.one_left]
      mul_mem' := by
        intro g h hg hh A _ _ a
        simpa only [MonObj.comp_mul, map_mul] using (hg A a).mul_left (hh A a)
      inv_mem' := by
        intro g hg A _ _ a
        simpa only [GrpObj.comp_inv, map_inv] using (hg A a).inv_left }
  comp_mem := by
    intro U V a g hg A _ _ b
    simpa only [Category.assoc] using hg A (b ≫ a)

/-- The defining condition involves every affine refinement of the test. -/
theorem mem_elementCentralizer {X : lieKernel G R} {U : Over (Spec R)}
    {g : U ⟶ G.X} :
    g ∈ (elementCentralizer G X).carrier U ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A]
        (a : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ U),
        Commute (constant G (a ≫ g)) (lieKernelMap G (Algebra.ofId R A) X).val :=
  Iff.rfl

/-- Commuting with a tangent point is equivalent to fixing it by conjugation. -/
theorem commute_constant_iff (g : AffinePoints G A) (X : lieKernel G A) :
    Commute (constant G g) X.val ↔ lieKernelConjugation G g X = X := by
  constructor
  · intro h
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.2 h.eq
  · intro h
    exact (commute_iff_eq _ _).2 (mul_inv_eq_iff_eq_mul.1 (congrArg Subtype.val h))

/-- On an affine test, it suffices to check the actual adjoint equation on that
test: its validity on all refinements follows from coefficient naturality. -/
theorem mem_elementCentralizer_affine_iff (X : lieKernel G R) (g : AffinePoints G A) :
    g ∈ (elementCentralizer G X).carrier
        ((algSpec R).obj (op (CommAlgCat.of R A))) ↔
      lieKernelConjugation G g (lieKernelMap G (Algebra.ofId R A) X) =
        lieKernelMap G (Algebra.ofId R A) X := by
  constructor
  · intro h
    apply (commute_constant_iff G g _).1
    simpa only [Category.id_comp] using h A (𝟙 _)
  · intro h B _ _ a
    let f : A →ₐ[R] B := (algSpec.fullyFaithful.preimage a).unop.hom
    have ha : (algSpec R).map (CommAlgCat.ofHom f).op = a :=
      algSpec.fullyFaithful.map_preimage a
    have hf : f.comp (Algebra.ofId R A) = Algebra.ofId R B := by
      exact Subsingleton.elim _ _
    have hn := congrArg (lieKernelMap G f) h
    rw [lieKernelConjugation_naturality, ← lieKernelMap_comp, hf] at hn
    apply (commute_constant_iff G (a ≫ g) _).2
    simpa only [affineMap_apply, ha] using hn

/-- In an affine group the stabilizer equation is literally the published
linear adjoint action fixing the scalar extension of the tangent vector. -/
theorem mem_elementCentralizer_adjoint_iff [IsAffineHom G.X.hom]
    (X : lieKernel G R) (g : AffinePoints G A) :
    g ∈ (elementCentralizer G X).carrier
        ((algSpec R).obj (op (CommAlgCat.of R A))) ↔
      adjoint G A g (lieKernelMapLinear G (Algebra.ofId R A) (Additive.ofMul X)) =
        lieKernelMapLinear G (Algebra.ofId R A) (Additive.ofMul X) := by
  rw [mem_elementCentralizer_affine_iff]
  exact Additive.ofMul.injective.eq_iff.symm

/-- The tangent submodule of the actual Lie-element centralizer. -/
def elementCentralizerLie [IsAffineHom G.X.hom] (X : lieKernel G R) :
    Submodule R (Additive (lieKernel G R)) := (elementCentralizer G X).lie R

end Lie

end Langlands.GroupScheme
