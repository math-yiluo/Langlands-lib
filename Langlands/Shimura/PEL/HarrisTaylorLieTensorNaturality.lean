import Langlands.Shimura.PEL.HarrisTaylorLieTensorFactor

/-! # Full algebra actions and rational naturality on actual Lie tensor factors -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L]
  {K : Type} [Field K] [NumberField K] [Algebra L K]
  {S : AlgebraicGeometry.Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
  (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- The full actual rational algebra acts on the original-order Lie tensor factor. -/
def lieTensorAction (conjugate : Bool) :
    A →+* End (lieTensorSheaf L s B i conjugate) where
  toFun a := (lieTensorSheafIso L s B i conjugate).hom ≫
    lieEigensheafAction L s B i conjugate a ≫ (lieTensorSheafIso L s B i conjugate).inv
  map_one' := by
    change (_ ≫ lieEigensheafAction L s B i conjugate 1 ≫ _) = _
    rw [map_one]
    simp
  map_mul' a b := by
    change (_ ≫ lieEigensheafAction L s B i conjugate (a * b) ≫ _) = _
    rw [map_mul]
    simp [End.mul_def, Category.assoc]
  map_zero' := by
    change (_ ≫ lieEigensheafAction L s B i conjugate 0 ≫ _) = _
    rw [map_zero]
    simp
  map_add' a b := by
    change (_ ≫ lieEigensheafAction L s B i conjugate (a + b) ≫ _) = _
    rw [map_add]
    change ((lieTensorSheafIso L s B i conjugate).hom ≫
      (lieEigensheafAction L s B i conjugate a + lieEigensheafAction L s B i conjugate b :
        lieEigensheaf L s B i conjugate ⟶ lieEigensheaf L s B i conjugate) ≫
      (lieTensorSheafIso L s B i conjugate).inv) =
      ((lieTensorSheafIso L s B i conjugate).hom ≫
        lieEigensheafAction L s B i conjugate a ≫ (lieTensorSheafIso L s B i conjugate).inv) +
      ((lieTensorSheafIso L s B i conjugate).hom ≫
        lieEigensheafAction L s B i conjugate b ≫ (lieTensorSheafIso L s B i conjugate).inv)
    exact (congrArg (fun h => (lieTensorSheafIso L s B i conjugate).hom ≫ h)
      (Preadditive.add_comp _ _ _ (lieEigensheafAction L s B i conjugate a)
        (lieEigensheafAction L s B i conjugate b)
        (lieTensorSheafIso L s B i conjugate).inv)).trans
      (Preadditive.comp_add _ _ _ (lieTensorSheafIso L s B i conjugate).hom
        (lieEigensheafAction L s B i conjugate a ≫ (lieTensorSheafIso L s B i conjugate).inv)
        (lieEigensheafAction L s B i conjugate b ≫ (lieTensorSheafIso L s B i conjugate).inv))

@[reassoc (attr := simp)]
theorem lieTensorAction_comparison (conjugate : Bool) (a : A) :
    lieTensorAction L s B i conjugate a ≫ (lieTensorSheafIso L s B i conjugate).hom =
      (lieTensorSheafIso L s B i conjugate).hom ≫ lieEigensheafAction L s B i conjugate a := by
  simp [lieTensorAction, Category.assoc]

/-- The canonical tensor projection intertwines the full differentiated algebra action. -/
theorem lieTensorProjection_intertwines (conjugate : Bool) (a : A) :
    lieRationalOrderAction s B i.toRingHom a ≫ lieTensorProjection L s B i conjugate =
      lieTensorProjection L s B i conjugate ≫ lieTensorAction L s B i conjugate a := by
  simpa [lieTensorProjection, lieTensorAction, Category.assoc] using
    congrArg (fun f => f ≫ (lieTensorSheafIso L s B i conjugate).inv)
      (lieEigenProjection_intertwines L s B i conjugate a)

/-- The actual Lie tensor splitting intertwines the full rational algebra action. -/
theorem lieTensorSplitting_intertwines (a : A) :
    lieRationalOrderAction s B i.toRingHom a ≫ (lieTensorSplitting L s B i).hom =
      (lieTensorSplitting L s B i).hom ≫
        prod.map (lieTensorAction L s B i false a) (lieTensorAction L s B i true a) := by
  apply prod.hom_ext
  · simpa only [lieTensorSplitting_hom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using
      lieTensorProjection_intertwines L s B i false a
  · simpa only [lieTensorSplitting_hom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using
      lieTensorProjection_intertwines L s B i true a

variable {B} {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
  (f : Hom0 B B')
  (hf : ∀ a : A, comp0 B B B' (i a) f = comp0 B B' B' f (i' a))

/-- The actual rational differential induces a map of the two Lie tensor factors. -/
def lieTensorMap (conjugate : Bool) :
    lieTensorSheaf L s B i conjugate ⟶ lieTensorSheaf L s B' i' conjugate :=
  (lieTensorSheafIso L s B i conjugate).hom ≫
    lieEigensheafMap L s i i' f hf conjugate ≫ (lieTensorSheafIso L s B' i' conjugate).inv

@[reassoc (attr := simp)]
theorem lieTensorMap_comparison (conjugate : Bool) :
    lieTensorMap L s i i' f hf conjugate ≫ (lieTensorSheafIso L s B' i' conjugate).hom =
      (lieTensorSheafIso L s B i conjugate).hom ≫ lieEigensheafMap L s i i' f hf conjugate := by
  simp [lieTensorMap, Category.assoc]

/-- Canonical tensor projections commute with actual equivariant rational differentials. -/
theorem lieTensorProjection_naturality (conjugate : Bool) :
    lieMap0 s f ≫ lieTensorProjection L s B' i' conjugate =
      lieTensorProjection L s B i conjugate ≫ lieTensorMap L s i i' f hf conjugate := by
  simpa [lieTensorProjection, lieTensorMap, Category.assoc] using
    congrArg (fun g => g ≫ (lieTensorSheafIso L s B' i' conjugate).inv)
      (lieEigenProjection_naturality L s i i' f hf conjugate)

/-- Tensor maps intertwine the full actual rational algebra actions. -/
theorem lieTensorMap_intertwines (conjugate : Bool) (a : A) :
    lieTensorAction L s B i conjugate a ≫ lieTensorMap L s i i' f hf conjugate =
      lieTensorMap L s i i' f hf conjugate ≫ lieTensorAction L s B' i' conjugate a := by
  simpa [lieTensorAction, lieTensorMap, Category.assoc] using
    congrArg (fun g => (lieTensorSheafIso L s B i conjugate).hom ≫ g ≫
      (lieTensorSheafIso L s B' i' conjugate).inv)
      (lieEigensheafMap_intertwines L s i i' f hf conjugate a)

/-- Identity rational maps induce identity tensor maps. -/
@[simp]
theorem lieTensorMap_id (conjugate : Bool) :
    lieTensorMap L s i i (id0 B) (fun _ => by simp) conjugate =
      𝟙 (lieTensorSheaf L s B i conjugate) := by
  simp [lieTensorMap]

/-- Tensor maps preserve actual rational composition. -/
theorem lieTensorMap_comp {B'' : AbelianScheme S}
    (i'' : A →ₐ[ℚ] End0 B'') (g : Hom0 B' B'')
    (hg : ∀ a : A, comp0 B' B' B'' (i' a) g = comp0 B' B'' B'' g (i'' a))
    (conjugate : Bool) :
    lieTensorMap L s i i'' (comp0 B B' B'' f g)
        (fun a => by
          rw [← comp0_assoc, hf a, comp0_assoc, hg a, ← comp0_assoc]) conjugate =
      lieTensorMap L s i i' f hf conjugate ≫ lieTensorMap L s i' i'' g hg conjugate := by
  simpa [lieTensorMap, Category.assoc] using
    congrArg (fun h => (lieTensorSheafIso L s B i conjugate).hom ≫ h ≫
      (lieTensorSheafIso L s B'' i'' conjugate).inv)
      (lieEigensheafMap_comp L s i i' f hf i'' g hg conjugate)

/-- The actual tensor splitting is natural for equivariant rational homomorphisms. -/
theorem lieTensorSplitting_naturality :
    lieMap0 s f ≫ (lieTensorSplitting L s B' i').hom =
      (lieTensorSplitting L s B i).hom ≫
        prod.map (lieTensorMap L s i i' f hf false) (lieTensorMap L s i i' f hf true) := by
  apply prod.hom_ext
  · simpa only [lieTensorSplitting_hom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using
      lieTensorProjection_naturality L s i i' f hf false
  · simpa only [lieTensorSplitting_hom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using
      lieTensorProjection_naturality L s i i' f hf true

/-- An actual equivariant rational isomorphism gives actual tensor-factor isomorphisms. -/
def lieTensorIso (conjugate : Bool)
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    lieTensorSheaf L s B i conjugate ≅ lieTensorSheaf L s B' i' conjugate :=
  lieTensorSheafIso L s B i conjugate ≪≫
    lieEigensheafIso L s i i' conjugate e he ≪≫ (lieTensorSheafIso L s B' i' conjugate).symm

@[simp]
theorem lieTensorIso_hom (conjugate : Bool)
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    (lieTensorIso L s i i' conjugate e he).hom =
      lieTensorMap L s i i' e.hom he conjugate := by
  rfl

end Langlands.Shimura.HarrisTaylor
