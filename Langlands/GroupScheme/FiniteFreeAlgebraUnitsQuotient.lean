import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.FiniteFreeAlgebraUnits
import Langlands.GroupScheme.Multiplicative

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! # Fppf quotients by kernels of split homomorphisms, and unit groups of split algebra maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SectionQuotient

section General

variable {S : Scheme.{u}} {G H : GroupScheme S} (q : G ⟶ H) (s : H ⟶ G) (hs : s ≫ q = 𝟙 H)

/-- A homomorphism with a section splits its source, as a scheme over the target, into the
product of the kernel and the target. -/
def decompIso : G.X ≅ (kernel q).X ⊗ H.X where
  hom := lift (SplitKernelRetract.retraction q (𝟙 H) q s (Category.comp_id q) hs) q.hom.hom
  inv := (fst _ _ ≫ (kernelι q).hom.hom) * (snd _ _ ≫ s.hom.hom)
  hom_inv_id := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd,
      SplitKernelRetract.retraction_ι, SplitKernelRetract.adjustment, _root_.mul_assoc,
      inv_mul_cancel, _root_.mul_one]
  inv_hom_id := by
    have hs' : s.hom.hom ≫ q.hom.hom = 𝟙 H.X := by
      rw [← Grp.comp_hom_hom, hs]; rfl
    have hq : ((fst (kernel q).X H.X ≫ (kernelι q).hom.hom) * (snd _ _ ≫ s.hom.hom)) ≫
        q.hom.hom = snd (kernel q).X H.X := by
      have hk : (kernelι q).hom.hom ≫ q.hom.hom = 1 := by
        rw [(kernel_isPullback q).w]; rfl
      rw [MonObj.mul_comp, Category.assoc, hk, Category.assoc, hs', Category.comp_id,
        MonObj.comp_one, _root_.one_mul]
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono (kernelι q).hom.hom).mp
      simp only [Category.assoc, Category.id_comp, lift_fst_assoc]
      rw [SplitKernelRetract.retraction_ι, SplitKernelRetract.adjustment, MonObj.comp_mul,
        Category.comp_id, GrpObj.comp_inv,
        ← Category.assoc, hq, _root_.mul_assoc, mul_inv_cancel, _root_.mul_one]
    · rw [Category.assoc, lift_snd, hq, Category.id_comp]

theorem decompIso_hom_snd : (decompIso q s hs).hom ≫ snd _ _ = q.hom.hom :=
  lift_snd _ _

end General

section Field

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ H) (s : H ⟶ G) (hs : s ≫ q = 𝟙 H)

theorem kernel_surjective : Surjective (kernel q).X.hom := by
  have h : η[(kernel q).X].left ≫ (kernel q).X.hom = 𝟙 _ := η[(kernel q).X].w
  have : Surjective (η[(kernel q).X].left ≫ (kernel q).X.hom) := by
    rw [h]; infer_instance
  exact Surjective.of_comp (f := η[(kernel q).X].left) (g := (kernel q).X.hom)

include hs in
/-- Over a field, a homomorphism of group schemes with a homomorphic section, from a group
scheme locally of finite type to a separated one, is an fppf quotient by its kernel. -/
theorem isFppfQuotient_of_section [LocallyOfFiniteType G.X.hom] [IsSeparated H.X.hom] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q := by
  have hq : q.hom.hom.left = (decompIso q s hs).hom.left ≫ (snd (kernel q).X H.X).left := by
    rw [← Over.comp_left, decompIso_hom_snd]
  have : LocallyOfFiniteType (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : Flat (kernel q).X.hom := inferInstance
  have : Surjective (kernel q).X.hom := kernel_surjective q
  have : Flat (snd (kernel q).X H.X).left := by
    change Flat (pullback.snd _ _)
    infer_instance
  have : Surjective (snd (kernel q).X H.X).left := by
    change Surjective (pullback.snd _ _)
    infer_instance
  have : LocallyOfFinitePresentation (snd (kernel q).X H.X).left := by
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [hq]; infer_instance
  · rw [hq]; infer_instance
  · rw [hq]; infer_instance

end Field

end Langlands.GroupScheme.SectionQuotient

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A]
  {A' : Type u} [Ring A'] [Algebra R A']
  {n m : ℕ} (b : Module.Basis (Fin n) R A) (b' : Module.Basis (Fin m) R A')
  (f : A →ₐ[R] A')

/-- On `T`-points, an algebra homomorphism induces the unit map of `Γ(T) ⊗[R] A → Γ(T) ⊗[R] A'`. -/
def mapPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme b).X) →* (T ⟶ (groupScheme b').X) :=
  ((pointsEquiv b' T).symm.toMonoidHom.comp
    (Units.map (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) f).toMonoidHom)).comp
    (pointsEquiv b T).toMonoidHom

theorem pointsEquiv_mapPoints (T : Over (Spec R)) (x : T ⟶ (groupScheme b).X) :
    pointsEquiv b' T (mapPoints b b' f T x) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) f).toMonoidHom
        (pointsEquiv b T x) := by
  rw [mapPoints, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (pointsEquiv b' T).apply_symm_apply _

theorem mapPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ (groupScheme b).X) :
    mapPoints b b' f T' (a ≫ x) = a ≫ mapPoints b b' f T x := by
  apply (pointsEquiv b' T').injective
  rw [pointsEquiv_mapPoints, pointsEquiv_naturality, pointsEquiv_naturality, pointsEquiv_mapPoints]
  have key : (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T').unop) f).comp
        (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom (AlgHom.id R A)) =
      (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom (AlgHom.id R A')).comp
        (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) f) := by
    ext <;> simp
  apply Units.ext
  exact congrArg (fun φ : ((algΓ R).obj T).unop ⊗[R] A →ₐ[R] ((algΓ R).obj T').unop ⊗[R] A' =>
    φ (pointsEquiv b T x : ((algΓ R).obj T).unop ⊗[R] A)) key

/-- The homomorphism of unit group schemes induced by an algebra homomorphism. -/
def map : groupScheme b ⟶ groupScheme b' :=
  homOfPoints (mapPoints b b' f) (fun a x => mapPoints_naturality b b' f a x)

theorem pointsEquiv_map (T : Over (Spec R)) (x : T ⟶ (groupScheme b).X) :
    pointsEquiv b' T (x ≫ (map b b' f).hom.hom) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) f).toMonoidHom
        (pointsEquiv b T x) := by
  rw [map, comp_homOfPoints, pointsEquiv_mapPoints]

theorem map_id : map b b (AlgHom.id R A) = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv b T).injective
  rw [pointsEquiv_map]
  apply Units.ext
  simp only [Units.coe_map]
  rw [Algebra.TensorProduct.map_id]
  rfl

variable {A'' : Type u} [Ring A''] [Algebra R A''] {l : ℕ} (b'' : Module.Basis (Fin l) R A'')
  (g : A' →ₐ[R] A'')

theorem map_comp : map b b' f ≫ map b' b'' g = map b b'' (g.comp f) := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv b'' T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_map, pointsEquiv_map, pointsEquiv_map]
  have key : (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) g).comp
        (Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) f) =
      Algebra.TensorProduct.map (AlgHom.id R ((algΓ R).obj T).unop) (g.comp f) := by
    ext <;> simp
  apply Units.ext
  exact congrArg (fun φ : ((algΓ R).obj T).unop ⊗[R] A →ₐ[R] ((algΓ R).obj T).unop ⊗[R] A'' =>
    φ (pointsEquiv b T x : ((algΓ R).obj T).unop ⊗[R] A)) key

end Langlands.GroupScheme.FiniteFreeAlgebraUnits

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  {A' : Type u} [Ring A'] [Algebra k A']
  {n m : ℕ} (b : Module.Basis (Fin n) (CommRingCat.of k) A)
  (b' : Module.Basis (Fin m) (CommRingCat.of k) A')
  (f : A →ₐ[k] A') (g : A' →ₐ[k] A) (hfg : f.comp g = AlgHom.id k A')

include hfg in
/-- Over a field, the unit-group map of an algebra homomorphism with an algebra section is an
fppf quotient by its kernel. -/
theorem isFppfQuotient_map_of_section :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι (map b b' f)))
      (map b b' f) := by
  have := groupScheme_locallyOfFiniteType b
  have := groupScheme_isAffineHom b'
  refine SectionQuotient.isFppfQuotient_of_section (map b b' f) (map b' b g) ?_
  rw [map_comp, hfg, map_id]

end Langlands.GroupScheme.FiniteFreeAlgebraUnits
