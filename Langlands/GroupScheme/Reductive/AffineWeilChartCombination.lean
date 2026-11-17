import Langlands.GroupScheme.Descent.DisjointGroupAssembly
import Langlands.GroupScheme.AffineWeilEmbeddingProductComparison
import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.AffineWeilUnit
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.RelativeLevi.GeometricFiberComparison
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Flat

/-! # Combining Weil-restriction presentations on finitely many charts -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.AffineWeil.ChartCombination

section Algebra

variable {I : Type u} (R : I → Type u) [∀ i, CommRing (R i)]
  (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (R i) (B i)]

/-- A factor of a finite product, as an algebra over the product through evaluation. -/
@[instance_reducible]
def evalAlgebra (i : I) : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra

/-- A coefficient algebra of one factor, as an algebra over the product base. -/
@[instance_reducible]
def factorAlgebra (i : I) : Algebra (∀ j, R j) (B i) :=
  Algebra.compHom (B i) (Pi.evalRingHom R i)

/-- The product of the coefficient algebras, with the componentwise action of the
product of the base rings. -/
@[instance_reducible]
def coefficientAlgebra : Algebra (∀ j, R j) (∀ j, B j) := by
  letI (i : I) : Algebra (∀ j, R j) (B i) := factorAlgebra R B i
  infer_instance

@[simp] theorem coefficientAlgebra_algebraMap_apply (r : ∀ j, R j) (i : I) :
    (@algebraMap (∀ j, R j) (∀ j, B j) _ _ (coefficientAlgebra R B) r) i =
      algebraMap (R i) (B i) (r i) :=
  rfl

theorem coefficient_smul_apply (r : ∀ j, R j) (c : ∀ j, B j) (i : I) :
    (@HSMul.hSMul (∀ j, R j) (∀ j, B j) (∀ j, B j)
      (@instHSMul _ _ (coefficientAlgebra R B).toSMul) r c) i = r i • c i :=
  rfl

/-- Each evaluation of a finite product is the localization away from the idempotent
supported at that factor. -/
theorem isLocalization_away [DecidableEq I] (i : I) :
    letI := evalAlgebra R i
    IsLocalization.Away (Pi.single i 1 : ∀ j, R j) (R i) := by
  classical
  letI := evalAlgebra R i
  refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom R i)
    (Function.surjective_eval i)
  simp [IsIdempotentElem, ← Pi.single_mul_left]

variable [Finite I]

/-- Componentwise finite coefficient algebras give a finite product algebra. -/
theorem coefficient_finite [∀ i, Module.Finite (R i) (B i)] :
    letI := coefficientAlgebra R B
    Module.Finite (∀ j, R j) (∀ j, B j) := by
  letI (i : I) : Algebra (∀ j, R j) (R i) := evalAlgebra R i
  letI (i : I) : Algebra (∀ j, R j) (B i) := factorAlgebra R B i
  haveI (i : I) : IsScalarTower (∀ j, R j) (R i) (B i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : I) : Module.Finite (∀ j, R j) (R i) :=
    Module.Finite.of_surjective (Algebra.linearMap (∀ j, R j) (R i))
      (Function.surjective_eval i)
  haveI (i : I) : Module.Finite (∀ j, R j) (B i) := Module.Finite.trans (R i) (B i)
  have h : Module.Finite (∀ j, R j) (∀ j, B j) := inferInstance
  exact h

/-- Componentwise étale coefficient algebras give an étale product algebra. -/
theorem coefficient_etale [∀ i, Algebra.Etale (R i) (B i)] :
    letI := coefficientAlgebra R B
    Algebra.Etale (∀ j, R j) (∀ j, B j) := by
  classical
  letI (i : I) : Algebra (∀ j, R j) (R i) := evalAlgebra R i
  letI (i : I) : Algebra (∀ j, R j) (B i) := factorAlgebra R B i
  haveI (i : I) : IsScalarTower (∀ j, R j) (R i) (B i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : I) : IsLocalization.Away (Pi.single i 1 : ∀ j, R j) (R i) :=
    isLocalization_away R i
  haveI (i : I) : Algebra.Etale (∀ j, R j) (R i) :=
    Algebra.Etale.of_isLocalizationAway (Pi.single i 1)
  haveI (i : I) : Algebra.Etale (∀ j, R j) (B i) :=
    Algebra.Etale.comp (R := ∀ j, R j) (A := R i) (B := B i)
  have h : Algebra.Etale (∀ j, R j) (∀ j, B j) := inferInstance
  exact h

/-- Finite étale coefficient algebras give a projective product algebra. -/
theorem coefficient_projective [∀ i, Module.Finite (R i) (B i)]
    [∀ i, Algebra.Etale (R i) (B i)] :
    letI := coefficientAlgebra R B
    Module.Projective (∀ j, R j) (∀ j, B j) := by
  letI := coefficientAlgebra R B
  haveI := coefficient_finite R B
  haveI := coefficient_etale R B
  haveI : Module.FinitePresentation (∀ j, R j) (∀ j, B j) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

end Algebra

section Group

variable {I : Type u} [Finite I] (B : I → Type u) [∀ i, CommRing (B i)]

/-- The spectrum of a factor inside the spectrum of a finite product of rings. -/
abbrev component (i : I) :
    Spec (CommRingCat.of (B i)) ⟶ Spec (CommRingCat.of (∀ j, B j)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom B i))

instance : IsIso (Sigma.desc (component B)) := by
  change IsIso (sigmaSpec (fun i => CommRingCat.of (B i)))
  infer_instance

variable (H : ∀ i, GroupScheme (Spec (CommRingCat.of (B i))))

/-- The group scheme over the spectrum of the product ring assembled from the family. -/
abbrev group : GroupScheme (Spec (CommRingCat.of (∀ j, B j))) :=
  Descent.DisjointGroupAssembly.group (component B) H

/-- Restriction of the assembled group to a factor recovers the original group. -/
def componentIso (i : I) : (baseChange (component B i)).obj (group B H) ≅ H i :=
  Descent.DisjointGroupAssembly.componentIso (component B) H i

/-- The underlying relative scheme is the disjoint union over the product base. -/
def underlyingIso : (group B H).X ≅
    Over.mk (Sigma.desc fun i => (H i).X.hom ≫ component B i) :=
  Descent.DisjointGroupAssembly.underlyingIso (component B) H

instance [∀ i, IsAffine (H i).X.left] : IsAffine (group B H).X.left :=
  inferInstanceAs (IsAffine
    (Descent.DisjointGroupAssembly.group (component B) H).X.left)

instance [∀ i, LocallyOfFiniteType (H i).X.hom] :
    LocallyOfFiniteType (group B H).X.hom := by
  have : LocallyOfFiniteType (Sigma.desc fun i => (H i).X.hom ≫ component B i) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  rw [← Over.w (underlyingIso B H).hom]
  change LocallyOfFiniteType ((underlyingIso B H).hom.left ≫
    Sigma.desc fun i => (H i).X.hom ≫ component B i)
  let : IsIso (underlyingIso B H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (underlyingIso B H).hom))
  infer_instance

/-- Smoothness of the structure map follows componentwise. -/
theorem smooth (hH : ∀ i, Smooth (H i).X.hom) : Smooth (group B H).X.hom := by
  let : ∀ i, Smooth (H i).X.hom := hH
  have : Smooth (Sigma.desc fun i => (H i).X.hom ≫ component B i) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  rw [← Over.w (underlyingIso B H).hom]
  change Smooth ((underlyingIso B H).hom.left ≫
    Sigma.desc fun i => (H i).X.hom ≫ component B i)
  let : IsIso (underlyingIso B H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (underlyingIso B H).hom))
  infer_instance

/-- Any field-group property invariant under isomorphism and reflected by field
extension passes from the geometric fibres of the family to the assembled group. -/
theorem geometricFiber_property
    (P : ∀ (k : Type u) [Field k], GroupScheme (Spec (CommRingCat.of k)) → Prop)
    (hIso : ∀ (k : Type u) [Field k]
      {G G' : GroupScheme (Spec (CommRingCat.of k))}, (G ≅ G') → P k G' → P k G)
    (hField : ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
      (G : GroupScheme (Spec (CommRingCat.of k))),
      P K ((baseChange (algebraBaseMap k K)).obj G) → P k G)
    (hH : ∀ i, ∀ s : Spec (CommRingCat.of (B i)), P _ (geometricFiber (H i) s)) :
    ∀ s : Spec (CommRingCat.of (∀ j, B j)), P _ (geometricFiber (group B H) s) := by
  intro s
  obtain ⟨i, t, rfl⟩ := Descent.DisjointComponents.component_covers (component B) s
  let b := component B i
  let k := (Spec (CommRingCat.of (∀ j, B j))).residueField (b t)
  let K := (Spec (CommRingCat.of (B i))).residueField t
  let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have hlocal : P _ (geometricFiber ((baseChange b).obj (group B H)) t) :=
    hIso _ ((baseChange (geometricPoint _ t)).mapIso (componentIso B H i)) (hH i t)
  have hext : P _ ((baseChange (algebraBaseMap (AlgebraicClosure k)
      (AlgebraicClosure K))).obj (geometricFiber (group B H) (b t))) :=
    hIso _ ((RelativeLevi.geometricFiberBaseChangeIso b t).app (group B H)) hlocal
  exact hField _ _ _ hext

/-- Reductivity is inherited from all the component groups. -/
theorem isReductive (hH : ∀ i, IsReductive (H i)) : IsReductive (group B H) := by
  let : ∀ i, IsAffine (H i).X.left :=
    fun i => @isAffine_of_isAffineHom _ _ (H i).X.hom (hH i).isAffineHom inferInstance
  refine ⟨smooth B H (fun i => (hH i).smooth), inferInstance, ?_⟩
  intro s
  have hc := geometricFiber_property B H
    (fun _ _ G => IsConnectedReductive G)
    (fun _ _ _ _ e h => h.of_iso e)
    (fun _ _ _ _ _ _ h => IsConnectedReductive.of_fieldExtension h)
    (fun i t => ((hH i).geometricFiber t).isConnectedReductive_of_isAlgClosed) s
  exact hc.isPseudoReductive

/-- Almost simple geometric fibres are inherited from the component groups. -/
theorem isAlmostSimple_geometricFiber
    (hH : ∀ i, ∀ s : Spec (CommRingCat.of (B i)), IsAlmostSimple (geometricFiber (H i) s)) :
    ∀ s : Spec (CommRingCat.of (∀ j, B j)), IsAlmostSimple (geometricFiber (group B H) s) :=
  geometricFiber_property B H (fun _ _ G => IsAlmostSimple G)
    (fun _ _ _ _ e h => h.of_iso e)
    (fun _ _ _ _ _ _ h => IsAlmostSimple.of_fieldExtension h) hH

end Group

section TensorFactor

variable {I : Type u} [DecidableEq I] (R : I → Type u) [∀ i, CommRing (R i)]
  (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (R i) (B i)]
  (i : I)

/-- A test algebra over one factor, as an algebra over the product base. -/
@[instance_reducible]
def testAlgebra (T : Type u) [CommRing T] [Algebra (R i) T] : Algebra (∀ j, R j) T :=
  Algebra.compHom T (Pi.evalRingHom R i)

omit [DecidableEq I] in
theorem testAlgebra_isScalarTower (T : Type u) [CommRing T] [Algebra (R i) T] :
    letI := evalAlgebra R i
    letI := testAlgebra R i T
    IsScalarTower (∀ j, R j) (R i) T :=
  letI := evalAlgebra R i
  letI := testAlgebra R i T
  IsScalarTower.of_algebraMap_eq' rfl

variable (T : Type u) [CommRing T] [Algebra (R i) T]

/-- The factor tensor product, as an algebra over the product of coefficient algebras. -/
@[instance_reducible]
def factorTensorAlgebra : Algebra (∀ j, B j) (B i ⊗[R i] T) :=
  Algebra.compHom (B i ⊗[R i] T) (Pi.evalRingHom B i)

attribute [local instance] evalAlgebra coefficientAlgebra factorTensorAlgebra

/-- The factor tensor product, as an algebra over the product base through
evaluation. -/
@[instance_reducible]
def factorTensorBaseAlgebra : Algebra (∀ j, R j) (B i ⊗[R i] T) :=
  Algebra.compHom (B i ⊗[R i] T) (Pi.evalRingHom R i)

attribute [local instance] factorTensorBaseAlgebra

omit [DecidableEq I] in
theorem factorTensor_isScalarTower_factor :
    IsScalarTower (∀ j, R j) (R i) (B i ⊗[R i] T) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] factorTensor_isScalarTower_factor

omit [DecidableEq I] in
theorem factorTensor_isScalarTower :
    IsScalarTower (∀ j, R j) (∀ j, B j) (B i ⊗[R i] T) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap (R i) (B i ⊗[R i] T) (a i) =
      algebraMap (B i) (B i ⊗[R i] T) (algebraMap (R i) (B i) (a i))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    rfl)

attribute [local instance] factorTensor_isScalarTower

variable [Algebra (∀ j, R j) T] [IsScalarTower (∀ j, R j) (R i) T]

omit [DecidableEq I] in
theorem smul_test (a : ∀ j, R j) (t : T) : a • t = a i • t := by
  rw [← algebraMap_smul (R i) a t]
  rfl

/-- The right inclusion of a test algebra into the factor tensor product, as a map of
algebras over the product base. -/
def includeTest : T →ₐ[∀ j, R j] B i ⊗[R i] T :=
  (Algebra.TensorProduct.includeRight : T →ₐ[R i] B i ⊗[R i] T).restrictScalars (∀ j, R j)

omit [DecidableEq I] in
@[simp] theorem includeTest_apply (t : T) : includeTest R B i T t = (1 : B i) ⊗ₜ t :=
  rfl

/-- Restriction of the product tensor product to one factor. -/
def toFactor : (∀ j, B j) ⊗[∀ j, R j] T →ₐ[∀ j, B j] B i ⊗[R i] T :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (includeTest R B i T)
    (fun _ _ => Commute.all _ _)

omit [DecidableEq I] in
@[simp] theorem toFactor_tmul (c : ∀ j, B j) (t : T) :
    toFactor R B i T (c ⊗ₜ t) = c i ⊗ₜ t := by
  rw [toFactor, Algebra.TensorProduct.lift_tmul, includeTest_apply, Algebra.ofId_apply]
  change algebraMap (B i) (B i ⊗[R i] T) (c i) * _ = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]
  rfl

/-- Extension by zero from one factor, additively. -/
def fromFactor : B i ⊗[R i] T →+ (∀ j, B j) ⊗[∀ j, R j] T :=
  TensorProduct.liftAddHom
    { toFun := fun b =>
        (TensorProduct.mk (∀ j, R j) (∀ j, B j) T (Pi.single i b)).toAddMonoidHom
      map_zero' := by
        refine AddMonoidHom.ext fun t => ?_
        simp
      map_add' := fun b b' => by
        refine AddMonoidHom.ext fun t => ?_
        simp [Pi.single_add] }
    (fun r b t => by
      change Pi.single i (r • b) ⊗ₜ[∀ j, R j] t = Pi.single i b ⊗ₜ[∀ j, R j] (r • t)
      have hb : (Pi.single i (r • b) : ∀ j, B j) =
          (Pi.single i r : ∀ j, R j) • Pi.single i b := by
        funext j
        rw [coefficient_smul_apply]
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj]
      have ht : (Pi.single i r : ∀ j, R j) • t = r • t := by
        rw [smul_test R i T]
        simp
      rw [hb, TensorProduct.smul_tmul, ht])

@[simp] theorem fromFactor_tmul (b : B i) (t : T) :
    fromFactor R B i T (b ⊗ₜ t) = Pi.single i b ⊗ₜ t :=
  rfl

theorem fromFactor_toFactor (x : (∀ j, B j) ⊗[∀ j, R j] T) :
    fromFactor R B i T (toFactor R B i T x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c t =>
    rw [toFactor_tmul, fromFactor_tmul]
    have hc : (Pi.single i (c i) : ∀ j, B j) = (Pi.single i 1 : ∀ j, R j) • c := by
      funext j
      rw [coefficient_smul_apply]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    have ht : (Pi.single i 1 : ∀ j, R j) • t = t := by
      rw [smul_test R i T]
      simp
    rw [hc, TensorProduct.smul_tmul, ht]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem toFactor_fromFactor (y : B i ⊗[R i] T) :
    toFactor R B i T (fromFactor R B i T y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul b t => rw [fromFactor_tmul, toFactor_tmul, Pi.single_eq_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The tensor product over the product base with a test algebra of one factor is the
tensor product of that factor's coefficient algebra with the test algebra. -/
def tensorFactorEquiv : (∀ j, B j) ⊗[∀ j, R j] T ≃ₐ[∀ j, B j] B i ⊗[R i] T :=
  AlgEquiv.ofBijective (toFactor R B i T)
    ⟨Function.LeftInverse.injective (fromFactor_toFactor R B i T),
      Function.RightInverse.surjective (toFactor_fromFactor R B i T)⟩

@[simp] theorem tensorFactorEquiv_tmul (c : ∀ j, B j) (t : T) :
    tensorFactorEquiv R B i T (c ⊗ₜ t) = c i ⊗ₜ t :=
  toFactor_tmul R B i T c t

/-- The factor tensor isomorphism is natural in the test algebra. -/
theorem tensorFactorEquiv_naturality {T' : Type u} [CommRing T'] [Algebra (R i) T']
    [Algebra (∀ j, R j) T'] [IsScalarTower (∀ j, R j) (R i) T'] (f : T →ₐ[R i] T')
    (x : (∀ j, B j) ⊗[∀ j, R j] T) :
    tensorFactorEquiv R B i T' (Algebra.TensorProduct.lTensor (S := ∀ j, B j) (∀ j, B j)
        (f.restrictScalars (∀ j, R j)) x) =
      Algebra.TensorProduct.lTensor (S := B i) (B i) f (tensorFactorEquiv R B i T x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul c t =>
    rw [Algebra.TensorProduct.map_tmul, tensorFactorEquiv_tmul, tensorFactorEquiv_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end TensorFactor

section Points

/-- A group-scheme isomorphism identifies the affine points of its source and target. -/
def affinePointsIsoEquiv {S : CommRingCat.{u}} {G G' : GroupScheme (Spec S)} (e : G ≅ G')
    (X : CommAlgCat.{u} S) : G.affinePoints X ≃* G'.affinePoints X where
  toFun := G.affinePointsTarget e.hom X
  invFun := G'.affinePointsTarget e.inv X
  left_inv p := by
    change (p ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = p
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
    rfl
  right_inv p := by
    change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    rfl
  map_mul' := map_mul (G.affinePointsTarget e.hom X)

/-- An isomorphism of test algebras identifies the affine points of a group scheme. -/
def affinePointsAlgEquiv {S : CommRingCat.{u}} (G : GroupScheme (Spec S))
    {Y Y' : CommAlgCat.{u} S} (e : Y ≅ Y') : G.affinePoints Y ≃* G.affinePoints Y' where
  toFun := G.affinePointMap e.hom
  invFun := G.affinePointMap e.inv
  left_inv p := by
    rw [← MonoidHom.comp_apply, ← affinePointMap_comp, e.hom_inv_id, affinePointMap_id]
    rfl
  right_inv p := by
    rw [← MonoidHom.comp_apply, ← affinePointMap_comp, e.inv_hom_id, affinePointMap_id]
    rfl
  map_mul' := map_mul (G.affinePointMap e.hom)

variable {I : Type u} [DecidableEq I] [Finite I] (R : I → Type u) [∀ i, CommRing (R i)]
  (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (R i) (B i)]
  [∀ i, Module.Finite (R i) (B i)] [∀ i, Module.Projective (R i) (B i)]
  [∀ i, Algebra.Etale (R i) (B i)]
  (H : ∀ i, GroupScheme (Spec (CommRingCat.of (B i))))
  [∀ i, IsAffine (H i).X.left] [∀ i, LocallyOfFiniteType (H i).X.hom]

attribute [local instance] evalAlgebra coefficientAlgebra factorTensorAlgebra
  factorTensorBaseAlgebra factorTensor_isScalarTower_factor factorTensor_isScalarTower

instance : Module.Finite (∀ j, R j) (∀ j, B j) := coefficient_finite R B
instance : Module.Projective (∀ j, R j) (∀ j, B j) := coefficient_projective R B

/-- The Weil restriction of the assembled group along the product of the coefficient
algebras, over the product of the base rings. -/
abbrev weil : GroupScheme (Spec (CommRingCat.of (∀ j, R j))) :=
  AffineWeil.groupScheme (∀ j, R j) (∀ j, B j) (group B H)

variable (i : I)

section Generic

variable (T : Type u) [CommRing T] [Algebra (R i) T] [Algebra (∀ j, R j) T]
  [IsScalarTower (∀ j, R j) (R i) T]

/-- The factor tensor isomorphism as an isomorphism of test algebras. -/
abbrev tensorFactorIso :
    CommAlgCat.of (CommRingCat.of (∀ j, B j)) ((∀ j, B j) ⊗[∀ j, R j] T) ≅
      CommAlgCat.of (CommRingCat.of (∀ j, B j)) (B i ⊗[R i] T) :=
  CommAlgCat.isoMk (tensorFactorEquiv R B i T)

/-- Points of the restricted combined Weil restriction on a test algebra of one factor
are the points of that factor's Weil restriction, for any compatible action of the
product base on the test algebra. -/
def factorPointsEquivOf :
    ((baseChange (component R i)).obj (weil R B H)).affinePoints
        (CommAlgCat.of (CommRingCat.of (R i)) T) ≃*
      (AffineWeil.groupScheme (R i) (B i) (H i)).affinePoints
        (CommAlgCat.of (CommRingCat.of (R i)) T) :=
  (affinePointsBaseChangeMulEquiv (∀ j, R j) (R i) T (weil R B H)).symm.trans <|
    (AffineWeil.pointsEquiv (∀ j, R j) (∀ j, B j) (group B H) T).trans <|
      (affinePointsAlgEquiv (group B H) (tensorFactorIso R B i T)).trans <|
        (affinePointsBaseChangeMulEquiv (∀ j, B j) (B i) (B i ⊗[R i] T) (group B H)).trans <|
          (affinePointsIsoEquiv (componentIso B H i) _).trans
            (AffineWeil.pointsEquiv (R i) (B i) (H i) T).symm

/-- The factor-point comparison is natural in the test algebra. -/
theorem factorPointsEquivOf_naturality (T' : Type u) [CommRing T'] [Algebra (R i) T']
    [Algebra (∀ j, R j) T'] [IsScalarTower (∀ j, R j) (R i) T'] (f : T →ₐ[R i] T')
    (p : ((baseChange (component R i)).obj (weil R B H)).affinePoints
      (CommAlgCat.of (CommRingCat.of (R i)) T)) :
    factorPointsEquivOf R B H i T'
        (((baseChange (component R i)).obj (weil R B H)).affinePointMap (CommAlgCat.ofHom f) p) =
      (AffineWeil.groupScheme (R i) (B i) (H i)).affinePointMap (CommAlgCat.ofHom f)
        (factorPointsEquivOf R B H i T p) := by
  -- step 1: base change from the product base to one factor
  set q := (affinePointsBaseChangeMulEquiv (∀ j, R j) (R i) T (weil R B H)).symm p with hq
  have h1 : (affinePointsBaseChangeMulEquiv (∀ j, R j) (R i) T' (weil R B H)).symm
      (((baseChange (component R i)).obj (weil R B H)).affinePointMap (CommAlgCat.ofHom f) p) =
      (weil R B H).affinePointMap (CommAlgCat.ofHom (f.restrictScalars (∀ j, R j))) q := by
    apply (affinePointsBaseChangeMulEquiv (∀ j, R j) (R i) T' (weil R B H)).injective
    rw [MulEquiv.apply_symm_apply, ← affinePointsBaseChangeMulEquiv_naturality, hq,
      MulEquiv.apply_symm_apply]
    rfl
  -- step 2: Weil points over the product base
  have h2 := AffineWeil.pointsEquiv_naturality (∀ j, R j) (∀ j, B j) (group B H)
    (f.restrictScalars (∀ j, R j)) q
  set y := AffineWeil.pointsEquiv (∀ j, R j) (∀ j, B j) (group B H) T q with hy
  -- step 3: the factor tensor isomorphism
  have hcomm : CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := ∀ j, B j) (∀ j, B j)
        (f.restrictScalars (∀ j, R j))) ≫ (tensorFactorIso R B i T').hom =
      (tensorFactorIso R B i T).hom ≫ CommAlgCat.ofHom
        ((Algebra.TensorProduct.lTensor (S := B i) (B i) f).restrictScalars (∀ j, B j)) := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact tensorFactorEquiv_naturality R B i T f x
  have h3 : affinePointsAlgEquiv (group B H) (tensorFactorIso R B i T')
      ((group B H).affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor
        (S := ∀ j, B j) (∀ j, B j) (f.restrictScalars (∀ j, R j)))) y) =
      (group B H).affinePointMap (CommAlgCat.ofHom
          ((Algebra.TensorProduct.lTensor (S := B i) (B i) f).restrictScalars (∀ j, B j)))
        (affinePointsAlgEquiv (group B H) (tensorFactorIso R B i T) y) := by
    change (group B H).affinePointMap (tensorFactorIso R B i T').hom
        ((group B H).affinePointMap _ y) =
      (group B H).affinePointMap _
        ((group B H).affinePointMap (tensorFactorIso R B i T).hom y)
    rw [← MonoidHom.comp_apply, ← affinePointMap_comp, hcomm, affinePointMap_comp,
      MonoidHom.comp_apply]
  -- step 4: base change from the product of coefficient algebras to one factor
  have h4 := affinePointsBaseChangeMulEquiv_naturality (∀ j, B j) (B i) (B i ⊗[R i] T)
    (B i ⊗[R i] T') (group B H) (Algebra.TensorProduct.lTensor (S := B i) (B i) f)
    (affinePointsAlgEquiv (group B H) (tensorFactorIso R B i T) y)
  -- step 5: the component isomorphism
  have h5 := DFunLike.congr_fun (GroupScheme.affinePointsTarget_naturality
    ((baseChange (component B i)).obj (group B H)) (componentIso B H i).hom
      (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := B i) (B i) f)))
    (affinePointsBaseChangeMulEquiv (∀ j, B j) (B i)
      (B i ⊗[R i] T) (group B H) (affinePointsAlgEquiv (group B H)
        (tensorFactorIso R B i T) y))
  -- step 6: Weil points over the factor
  apply (AffineWeil.pointsEquiv (R i) (B i) (H i) T').injective
  rw [AffineWeil.pointsEquiv_naturality]
  simp only [factorPointsEquivOf, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  erw [h1]
  rw [h2]
  change _ = (H i).affinePointMap _ (affinePointsIsoEquiv (componentIso B H i) _
    (affinePointsBaseChangeMulEquiv (∀ j, B j) (B i) (B i ⊗[R i] T) (group B H)
      (affinePointsAlgEquiv (group B H) (tensorFactorIso R B i T) y)))
  rw [h3]
  erw [← h4]
  exact h5.symm

end Generic

variable (X : CommAlgCat.{u} (CommRingCat.of (R i)))

/-- Points of the restricted combined Weil restriction on a test algebra of one factor
are the points of that factor's Weil restriction. -/
def factorPointsEquiv :
    ((baseChange (component R i)).obj (weil R B H)).affinePoints X ≃*
      (AffineWeil.groupScheme (R i) (B i) (H i)).affinePoints X :=
  @factorPointsEquivOf _ _ _ R _ B _ _ _ _ _ H _ _ i X _ _ (testAlgebra R i X)
    (testAlgebra_isScalarTower R i X)

/-- The factor-point comparison is natural in the test algebra. -/
theorem factorPointsEquiv_naturality {X X' : CommAlgCat.{u} (CommRingCat.of (R i))}
    (f : X ⟶ X') (p : ((baseChange (component R i)).obj (weil R B H)).affinePoints X) :
    factorPointsEquiv R B H i X'
        (((baseChange (component R i)).obj (weil R B H)).affinePointMap f p) =
      (AffineWeil.groupScheme (R i) (B i) (H i)).affinePointMap f
        (factorPointsEquiv R B H i X p) :=
  @factorPointsEquivOf_naturality _ _ _ R _ B _ _ _ _ _ H _ _ i X _ _ (testAlgebra R i X)
    (testAlgebra_isScalarTower R i X) X' _ _ (testAlgebra R i X')
    (testAlgebra_isScalarTower R i X') f.hom p

/-- The natural isomorphism of affine point functors over one factor. -/
def factorAffinePointIso :
    ((baseChange (component R i)).obj (weil R B H)).affinePointFunctor ≅
      (AffineWeil.groupScheme (R i) (B i) (H i)).affinePointFunctor :=
  NatIso.ofComponents (fun X => (factorPointsEquiv R B H i X).toGrpIso) (by
    intro X X' f
    ext p
    exact factorPointsEquiv_naturality R B H i f p)

instance : IsAffine ((baseChange (component R i)).obj (weil R B H)).X.left :=
  inferInstanceAs (IsAffine (pullback (weil R B H).X.hom (component R i)))

/-- The restriction of the combined Weil restriction to one factor of the product base is
that factor's Weil restriction. -/
def factorIso :
    (baseChange (component R i)).obj (weil R B H) ≅
      AffineWeil.groupScheme (R i) (B i) (H i) :=
  AffinePointComparison.iso (factorAffinePointIso R B H i)

end Points

section Combination

variable {A : Type u} [CommRing A] {I : Type u} [DecidableEq I] [Finite I]
  (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
  (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (R i) (B i)]
  [∀ i, Module.Finite (R i) (B i)] [∀ i, Module.Projective (R i) (B i)]
  [∀ i, Algebra.Etale (R i) (B i)]
  (H : ∀ i, GroupScheme (Spec (CommRingCat.of (B i))))
  [∀ i, IsAffine (H i).X.left] [∀ i, LocallyOfFiniteType (H i).X.hom]
  (G : GroupScheme (Spec (CommRingCat.of A)))

omit [DecidableEq I] [Finite I] in
/-- Each factor of the product chart maps to the base through its own structure map. -/
theorem component_comp_baseMap (i : I) :
    component R i ≫ Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, R j))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (R i))) := by
  rw [← Spec.map_comp]
  rfl

/-- The restriction to one factor of the base change of `G` to the product chart is the
base change of `G` to that factor. -/
def componentBaseChangeIso (i : I) :
    (baseChange (component R i)).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, R j))))).obj G) ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))).obj G :=
  (baseChangeCompIso (Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, R j))))
      (component R i) G).symm ≪≫
    eqToIso (congrArg (fun e => (baseChange e).obj G) (component_comp_baseMap R i))

omit [DecidableEq I] [Finite I] in
/-- If the charts jointly cover `Spec A`, so does the product chart. -/
theorem surjective_baseMap
    (hcov : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, R j)))) := by
  constructor
  intro s
  obtain ⟨i, t, rfl⟩ := hcov s
  refine ⟨component R i t, ?_⟩
  rw [← Scheme.Hom.comp_apply, component_comp_baseMap]

attribute [local instance] evalAlgebra coefficientAlgebra

/-- **Combination of chart presentations.** Weil-restriction presentations of `G` on finitely
many charts `R i` combine to one on the product chart `∏ R i`, with coefficient algebra
`∏ B i` and the group assembled from the `H i`. -/
def combinedIso
    (φ : ∀ i, (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))).obj G ≅
      AffineWeil.groupScheme (R i) (B i) (H i)) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, R j))))).obj G ≅
      weil R B H :=
  Descent.DisjointComponents.groupIso (component R) fun i =>
    componentBaseChangeIso R G i ≪≫ φ i ≪≫ (factorIso R B H i).symm

end Combination

end Langlands.GroupScheme.AffineWeil.ChartCombination
