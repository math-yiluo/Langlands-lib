/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Stalk tensor coordinates for a scheme pullback comparison

Source: Stacks Project, Tag 08IB, local affine tensor comparison, and Tag 0098,
stalks of module pullback (blueprint: def-pc-pullback-stalk-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.PullbackStalkTensor

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- The base points of a pullback point agree. Source: Stacks, Tag 01JX.
Proof: apply the underlying point map to `pullback.condition`.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem point_eq (z : ↥(Limits.pullback f g)) :
    f ((pullback.fst f g) z) = g ((pullback.snd f g) z) := by
  exact congrArg (fun h : Limits.pullback f g ⟶ S ↦ h z) (pullback.condition (f := f) (g := g))

/-- Base stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev R (z : ↥(Limits.pullback f g)) := S.presheaf.stalk (f ((pullback.fst f g) z))

/-- Left stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev A (z : ↥(Limits.pullback f g)) := X.presheaf.stalk ((pullback.fst f g) z)

/-- Right stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev B (z : ↥(Limits.pullback f g)) := T.presheaf.stalk ((pullback.snd f g) z)

/-- Pullback stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev C (z : ↥(Limits.pullback f g)) := (Limits.pullback f g).presheaf.stalk z

/-- The left scalar structure is the actual scheme stalk map. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev leftAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (A f g z) :=
  (f.stalkMap ((pullback.fst f g) z)).hom.toAlgebra

/-- The right scalar structure transports the base point along the square. Source:
Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev rightAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (B f g z) :=
  ((S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
    g.stalkMap ((pullback.snd f g) z)).hom.toAlgebra

attribute [local instance] leftAlgebra rightAlgebra

/-- The projection stalk maps agree on the base stalk. Source: Stacks, Tag 01JX.
Proof: expand the stalk maps of both composites in the pullback square; use
`pullback.condition` to identify these composites and transport their base point.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem stalk_square (z : ↥(Limits.pullback f g)) :
    f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z =
      (S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
        g.stalkMap ((pullback.snd f g) z) ≫ (pullback.snd f g).stalkMap z := by
  simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using
    Scheme.Hom.stalkMap_congr_hom
      (pullback.fst f g ≫ f) (pullback.snd f g ≫ g) (pullback.condition (f := f) (g := g)) z

/-- The scalar structure on the pullback stalk is the composite left stalk map.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev stalkAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (R f g z) (C f g z) :=
  (f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z).hom.toAlgebra

attribute [local instance] stalkAlgebra

/-- The left projection stalk map as an algebra homomorphism. Source: Stacks,
Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def leftStalkHom (z : ↥(Limits.pullback f g)) :
    A f g z →ₐ[R f g z] C f g z :=
  { ((pullback.fst f g).stalkMap z).hom with commutes' := fun _ ↦ rfl }

/-- The right projection respects base scalars. Source: Stacks, Tags 01JX and 08IB.
Proof: evaluate the stalk square at a base-stalk element and reverse its equality.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem rightStalkHom_commutes (z : ↥(Limits.pullback f g)) (r : R f g z) :
    ((pullback.snd f g).stalkMap z).hom (algebraMap (R f g z) (B f g z) r) =
      algebraMap (R f g z) (C f g z) r := by
  exact (congrArg (fun h ↦ h.hom r) (stalk_square f g z)).symm

/-- The right projection stalk map as an algebra homomorphism. Source: Stacks,
Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def rightStalkHom (z : ↥(Limits.pullback f g)) :
    B f g z →ₐ[R f g z] C f g z :=
  { ((pullback.snd f g).stalkMap z).hom with
    commutes' := rightStalkHom_commutes f g z }

/-- The canonical tensor-to-stalk map constructed by the tensor-product lift.
On a pure tensor it multiplies the images under the two projection stalk maps.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  (Algebra.TensorProduct.lift (leftStalkHom f g z) (rightStalkHom f g z)
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The pure-tensor formula for the explicit comparison. Source: Stacks, Tag 08IB.
Proof: the tensor-product lift is defined on pure tensors by multiplication.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem tensorToStalk_tmul (z : ↥(Limits.pullback f g)) (a : A f g z) (b : B f g z) :
    tensorToStalk f g z (a ⊗ₜ[R f g z] b) =
      ((pullback.fst f g).stalkMap z).hom a * ((pullback.snd f g).stalkMap z).hom b := by
  rfl

/-- The explicit comparison has the two prescribed restrictions.
Source: Stacks, Tags 01JX and 08IB.
Proof: evaluate the lift on a tensor with one factor equal to one, and apply
preservation of one by the corresponding projection stalk map.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem tensorToStalk_spec (z : ↥(Limits.pullback f g)) :
    (tensorToStalk f g z).comp
        (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
      ((pullback.fst f g).stalkMap z).hom ∧
    (tensorToStalk f g z).comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap z).hom := by
  constructor
  · ext a
    simp [tensorToStalk, leftStalkHom, rightStalkHom]
  · ext b
    simp [tensorToStalk, leftStalkHom, rightStalkHom]

/-- The restrictions uniquely characterize the explicit comparison.
Source: Stacks, Tag 08IB.
Proof: tensor-product ring homomorphisms agreeing on both inclusions agree on
pure tensors, hence on all tensors by additivity.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem tensorToStalk_unique (z : ↥(Limits.pullback f g))
    (φ : A f g z ⊗[R f g z] B f g z →+* C f g z)
    (hleft : φ.comp (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
      ((pullback.fst f g).stalkMap z).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap z).hom) : φ = tensorToStalk f g z := by
  apply Algebra.TensorProduct.ringHom_ext
  · exact hleft.trans (tensorToStalk_spec f g z).1.symm
  · exact hright.trans (tensorToStalk_spec f g z).2.symm

/-- The tensor-to-stalk ring map exists with the two prescribed restrictions.
Source: Stacks, Tag 01JX and Tag 08IB.
Proof: use the explicit tensor-product lift. On the left inclusion its formula
is p(a)q(1)=p(a); on the right inclusion it is p(1)q(b)=q(b).
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem exists_tensorToStalk (z : ↥(Limits.pullback f g)) :
    ∃ φ : A f g z ⊗[R f g z] B f g z →+* C f g z,
      φ.comp (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
        ((pullback.fst f g).stalkMap z).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap z).hom := by
  exact ⟨tensorToStalk f g z, tensorToStalk_spec f g z⟩

/-- The pullback stalk is an algebra over the tensor of the two original stalks.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev tensorAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (A f g z ⊗[R f g z] B f g z) (C f g z) :=
  (tensorToStalk f g z).toAlgebra

attribute [local instance] tensorAlgebra

/-- Stalkwise Tor independence includes every pair over the same base point,
not merely a selected family of points in the pullback. The transport identifies
O_{S,f(x)} with O_{S,g(t)}. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def IsTorIndependent : Prop :=
  ∀ (x : X) (t : T) (h : f x = g t),
    letI := (f.stalkMap x).hom.toAlgebra
    letI := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
    ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} (S.presheaf.stalk (f x))) i).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x))).obj
          (ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)))

/-- A representative's stalk complex. Source: Stacks, Tag 0098
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev stalkComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K

/-- The existing algebraic model applied to a representative's stalk.
Source: Stacks, Tags 08IB and 06Y6
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def cohomologyModel (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ModuleCat.baseDerivedTensorCohomologyModel (R f g z) (A f g z) (B f g z)
    (stalkComplex f g z K) (C f g z)

/-- Ordinary scalar extension of a representative's stalk along the canonical
A -> A tensor-over-R B -> C map. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def stalkTensorComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (ModuleCat.{u} (C f g z)) ℤ :=
  ((ModuleCat.extendScalars ((tensorToStalk f g z).comp
    (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)))).mapHomologicalComplex
      (.up ℤ)).obj
    (((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K)

/-- Invertibility of the canonical stalk comparison, in K-flat coordinates.
For every K-flat representative K of P, use its stalk Q, the existing derived
cohomology model T_i = H^i(Q tensor-derived-over-R B), and its specified comparison
c_i : C tensor-over-(A tensor-over-R B) T_i -> H^i(Q tensor-over-A C).
The target is identified with the stalk of H^i(Lg_X^*P). Requiring an identification
and invertibility after EVERY such identification is precisely invertibility of
c_i under the canonical identification: postcomposition by an isomorphism neither
creates nor destroys invertibility. This does not quantify over arbitrary maps
out of T_i; c_i is fixed by the equations of BaseDerivedTensorCohomologyModel.
K-flat representatives exist, so the universal quantification is not vacuous.
Source: Stacks, Tags 08IB, 0098 and 06YJ
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def IsComparisonIso
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (P : schemeDerivedCategory X) (z : ↥(Limits.pullback f g)) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    K.IsKFlatTensor → Nonempty (DerivedCategory.Q.obj K ≅ P) →
    ∀ i : ℤ,
      Nonempty
        ((stalkTensorComplex f g z K).homology i ≅
          (RingedSpace.moduleStalkFunctor (Limits.pullback f g).toRingedSpace z).obj
            ((DerivedCategory.homologyFunctor _ i).obj
              ((derivedPullback (pullback.fst f g)).obj P))) ∧
      ∀ e :
        (stalkTensorComplex f g z K).homology i ≅
          (RingedSpace.moduleStalkFunctor (Limits.pullback f g).toRingedSpace z).obj
            ((DerivedCategory.homologyFunctor _ i).obj
              ((derivedPullback (pullback.fst f g)).obj P)),
        IsIso ((cohomologyModel f g z K).localizedComparison i ≫ e.hom)

end AlgebraicGeometry.PullbackStalkTensor

end
