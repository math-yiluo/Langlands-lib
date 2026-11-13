import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smooth integral models from actual affine descent data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Descent.Solution

variable {B S : Scheme.{u}} {p : S ⟶ B} {H : GroupScheme S}
  {D : Datum p H} (s : Solution D)
  [Surjective p] [Flat p] [QuasiCompact p]

/-- Smoothness of the actual group descends along its fpqc solution. -/
theorem smooth [Smooth H.X.hom] : Smooth s.obj.X.hom := by
  have : Smooth (pullback.snd s.obj.X.hom p) := by
    change Smooth ((GroupScheme.baseChange p).obj s.obj).X.hom
    rw [← Over.w s.iso.hom.hom.hom]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := s.obj.X.hom) (g := p)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ this

end Langlands.GroupScheme.Descent.Solution

namespace Langlands.GroupScheme.IntegralModel

open Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {A L : Type u} [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {N : IntegralModel A L ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)}
  {D : Datum (Spec.algebraMap R A) N.group}
  (s : Solution D)
  [Surjective (Spec.algebraMap R A)] [Flat (Spec.algebraMap R A)]
  [IsAffine s.obj.X.left]

/-- A smooth affine fpqc solution with its prescribed generic identification is
an actual integral model of that generic group. -/
def ofAffineSolution (hN : N.IsSmooth)
    (e : (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G) :
    IntegralModel R K G := by
  let : Smooth N.group.X.hom := hN
  let : Smooth s.obj.X.hom := s.smooth
  exact
    { group := s.obj
      genericIso := e }

omit [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L] in
theorem isSmooth_ofAffineSolution (hN : N.IsSmooth)
    (e : (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G) :
    (ofAffineSolution s hN e).IsSmooth := by
  let : Smooth N.group.X.hom := hN
  exact s.smooth

/-- When the generic comparison agrees with the supplied one, the solution
isomorphism is an isomorphism of models over the generic identity. -/
def isoOfAffineSolution (hN : N.IsSmooth)
    (e : (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G)
    (he : (GroupScheme.baseChange (Spec.algebraMap A L)).map s.iso.hom ≫
      N.genericIso.hom = ((ofAffineSolution s hN e).baseChangeGenericIso A L).hom) :
    ((ofAffineSolution s hN e).baseChange A L).Iso N
      (CategoryTheory.Iso.refl _) where
  iso := s.iso
  generic_comm := by
    simpa only [baseChange, CategoryTheory.Iso.refl_hom, Category.comp_id] using he

/-- The constructed descended model has exactly the original upstairs
integral-point image after coefficient extension. -/
theorem integralPoints_ofAffineSolution (hN : N.IsSmooth)
    (e : (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G)
    (he : (GroupScheme.baseChange (Spec.algebraMap A L)).map s.iso.hom ≫
      N.genericIso.hom = ((ofAffineSolution s hN e).baseChangeGenericIso A L).hom) :
    ((ofAffineSolution s hN e).baseChange A L).integralPoints = N.integralPoints :=
  (isoOfAffineSolution s hN e he).integralPoints_eq

end Langlands.GroupScheme.IntegralModel
