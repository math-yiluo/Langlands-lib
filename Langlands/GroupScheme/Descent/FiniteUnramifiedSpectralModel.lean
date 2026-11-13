import Langlands.GroupScheme.Descent.FiniteUnramifiedIntegers
import Langlands.GroupScheme.Descent.FiniteUnramifiedCover
import Langlands.GroupScheme.Descent.FiniteUnramifiedDatum

/-! # Finite smooth group models over the actual spectral integer rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance spectralModelNormedField : NontriviallyNormedField F := localNormedField F
local instance spectralModelUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance spectralModelComplete : CompleteSpace F := localNormedField_complete F
local instance spectralModelIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The spectrum comparison between the given and norm-defined base integers. -/
def baseIntegerIso :
    Spec (CommRingCat.of ↥𝒪[F]) ≅ Spec (CommRingCat.of (baseIntegers F)) :=
  Scheme.Spec.mapIso
    (RingEquiv.subringCongr (localNormedField_integer F)).toCommRingCatIso.op

/-- The spectrum comparison from actual spectral integers to their coefficient subring. -/
def coefficientIntegerIso (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) :
    Spec (CommRingCat.of (extensionIntegers F E)) ≅
      Spec (CommRingCat.of (integerCoefficients F E)) :=
  Scheme.Spec.mapIso (integerCoefficientsEquiv F E hE).toCommRingCatIso.op

/-- The actual inclusion of finite spectral integers into maximal-unramified integers. -/
def spectralIntegerInclusion (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) :
    extensionIntegers F E →+* fixedFieldIntegers F :=
  (algebraMap (integerCoefficients F E) (fixedFieldIntegers F)).comp
    (integerCoefficientsEquiv F E hE).symm.toRingHom

@[simp]
theorem spectralIntegerInclusion_coe (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) (x : extensionIntegers F E) :
    ((spectralIntegerInclusion F E hE x : inertiaFixedField F) : SeparableClosure F) =
      (x : E) := rfl

/-- The actual spectrum map from maximal-unramified integers to a finite stage. -/
abbrev spectralIntegerMap (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) :=
  Spec.map (CommRingCat.ofHom (spectralIntegerInclusion F E hE))

@[reassoc (attr := simp)]
theorem spectralIntegerMap_coefficientIntegerIso
    (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) :
    spectralIntegerMap F E hE ≫ (coefficientIntegerIso F E hE).hom =
      Spec.algebraMap (integerCoefficients F E) (fixedFieldIntegers F) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

@[reassoc]
theorem spectralIntegerMap_integerMap
    (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E] (hE : E ≤ inertiaFixedField F) :
    spectralIntegerMap F E hE ≫ integerMap F E =
      Spec.map (CommRingCat.ofHom (integerToFixedField F)) ≫ (baseIntegerIso F).hom := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

/-- A smooth affine finite model on the actual spectral integer ring. -/
structure SpectralGroupModel
    (G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))) where
  field : IntermediateField F (SeparableClosure F)
  finite : FiniteDimensional F field
  galois : IsGalois F field
  inertia : field ≤ inertiaFixedField F
  unramified : ArithmeticUnramified F field
  group : GroupScheme (Spec (CommRingCat.of (extensionIntegers F field)))
  affine : IsAffineHom group.X.hom
  smooth : Smooth group.X.hom
  iso : G ≅ (baseChange (spectralIntegerMap F field inertia)).obj group

/-- Transport a coefficient model to its actual spectral integer ring. -/
def GroupModel.toSpectral
    {G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    (D : GroupModel F G) : SpectralGroupModel F G where
  field := D.field
  finite := D.finite
  galois := D.galois
  inertia := D.inertia
  unramified := D.unramified
  group := (baseChange (coefficientIntegerIso F D.field D.inertia).hom).obj D.group
  affine := by
    let := D.affine
    change IsAffineHom (pullback.snd D.group.X.hom _)
    infer_instance
  smooth := by
    let := D.smooth
    change Smooth (pullback.snd D.group.X.hom _)
    infer_instance
  iso := D.iso ≪≫
    (pullbackComparison (coefficientIntegerIso F D.field D.inertia).hom
      (spectralIntegerMap F D.field D.inertia)
      (Spec.algebraMap (integerCoefficients F D.field) (fixedFieldIntegers F))
      (spectralIntegerMap_coefficientIntegerIso F D.field D.inertia) D.group).symm

/-- Choose a smooth affine group model on a finite Galois unramified integer ring. -/
def spectralGroupModel
    (G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
    [IsAffine G.X.left] [Smooth G.X.hom] : SpectralGroupModel F G :=
  (groupModel F G).toSpectral F

end Langlands.GroupScheme.Descent.FiniteUnramified
