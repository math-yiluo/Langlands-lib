import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatPullbackDescent
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessPullback

/-! # Descent of actual relative stalk flatness -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

/-- The ordinary pullback inverse image of relative flatness on the new source. -/
def pullbackIsFlatOver {X P T : Scheme.{u}} (a : P ⟶ X) (p : P ⟶ T) :
    ObjectProperty X.Modules :=
  fun M => IsFlatOver p ((Scheme.Modules.pullback a).obj M)

namespace RelativeFlatnessDescent

/-- A faithful extension over the source algebra reflects flatness over any base ring. -/
lemma flat_of_faithfullyFlat_tensor
    (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.FaithfullyFlat A B] [Module.Flat R (B ⊗[A] M)] :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let F : M ⊗[R] N →ₗ[A] M ⊗[R] P :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : M →ₗ[A] M) f
  suffices Function.Injective F from this
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective A B F).mp
  let eN := (TensorProduct.AlgebraTensorModule.assoc R A B B M N).restrictScalars A
  let eP := (TensorProduct.AlgebraTensorModule.assoc R A B B M P).restrictScalars A
  let G : (B ⊗[A] M) ⊗[R] N →ₗ[B] (B ⊗[A] M) ⊗[R] P :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : B ⊗[A] M →ₗ[B] B ⊗[A] M) f
  have hcomm : F.lTensor B =
      eP.toLinearMap ∘ₗ G.restrictScalars A ∘ₗ eN.symm.toLinearMap := by
    ext b m n
    rfl
  rw [hcomm]
  exact eP.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp eN.symm.injective)

end RelativeFlatnessDescent

/-- Relative flatness descends along a flat surjection of the source. -/
lemma isFlatOver_of_pullback_flat_surjective
    {X Y S : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ S) [Flat p] [Surjective p]
    (M : Y.Modules)
    (hM : IsFlatOver (p ≫ f) ((Scheme.Modules.pullback p).obj M)) :
    IsFlatOver f M := by
  intro y
  obtain ⟨x, rfl⟩ := p.surjective y
  let R := S.presheaf.stalk (f (p x))
  let A := Y.presheaf.stalk (p x)
  let B := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap (p x)).hom.toAlgebra
  let : Algebra A B := (p.stalkMap x).hom.toAlgebra
  let : Algebra R B := ((p ≫ f).stalkMap x).hom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp p f x))
  let : Module R (stalk M (p x)) := relativeStalkModule f M (p x)
  have : IsScalarTower R A (stalk M (p x)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let N := (Scheme.Modules.pullback p).obj M
  let : Module R (stalk N x) := relativeStalkModule (p ≫ f) N x
  have : IsScalarTower R B (stalk N x) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat R (stalk N x) := hM x
  have : Module.Flat R (B ⊗[A] stalk M (p x)) :=
    Module.Flat.of_linearEquiv
      ((StalkPullback.pullbackStalkTensorEquiv p x M).symm.restrictScalars R)
  have : Module.FaithfullyFlat A B := faithfullyFlat_stalkMap p x
  exact RelativeFlatnessDescent.flat_of_faithfullyFlat_tensor R A B (stalk M (p x))

/-- Composing the base morphism with a flat morphism preserves relative flatness. -/
lemma isFlatOver_comp_of_flat
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [Flat g]
    (M : X.Modules) (hM : IsFlatOver f M) :
    IsFlatOver (f ≫ g) M := by
  intro x
  let R := S.presheaf.stalk (g (f x))
  let A := Y.presheaf.stalk (f x)
  let : Algebra R A := (g.stalkMap (f x)).hom.toAlgebra
  let : Module A (stalk M x) := relativeStalkModule f M x
  let : Module R (stalk M x) := relativeStalkModule (f ≫ g) M x
  have : IsScalarTower R A (stalk M x) :=
    .of_algebraMap_smul (fun r m => by
      change f.stalkMap x (g.stalkMap (f x) r) • m = (f ≫ g).stalkMap x r • m
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  have : Module.Flat R A := Flat.stalkMap g (f x)
  have : Module.Flat A (stalk M x) := hM x
  exact Module.Flat.trans R A (stalk M x)

/-- Relative flatness is detected after any flat surjective base change. -/
lemma isFlatOver_iff_pullback_of_flat_surjective
    {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T}
    (H : IsPullback a p f g) [Flat g] [Surjective g] (M : X.Modules) :
    IsFlatOver f M ↔ IsFlatOver p ((Scheme.Modules.pullback a).obj M) := by
  constructor
  · exact isFlatOver_pullback_of_isPullback H M
  · intro hM
    have : Flat a := MorphismProperty.of_isPullback H.flip inferInstance
    have : Surjective a := MorphismProperty.of_isPullback H.flip inferInstance
    apply isFlatOver_of_pullback_flat_surjective a f M
    rw [H.w]
    exact isFlatOver_comp_of_flat p g _ hM

/-- Flat surjective base change has exactly the original relative-flatness object property. -/
lemma pullbackIsFlatOver_eq_of_flat_surjective
    {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T}
    (H : IsPullback a p f g) [Flat g] [Surjective g] :
    pullbackIsFlatOver a p = isFlatOver f := by
  funext M
  exact propext (isFlatOver_iff_pullback_of_flat_surjective H M).symm

end Langlands.AlgebraicGeometry.Modules
