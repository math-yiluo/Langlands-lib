import Langlands.GroupScheme.IntegralModel.FiniteInnerUnramifiedRecovery
import Langlands.GroupScheme.IntegralModel.CommonFiniteInnerRecovery

/-! # All-automorphism compatibility of the recovered inertia comparison -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

/-- A finite comparison compatible with its prescribed semilinear maps
remains compatible after extension through the canonical tower maps. -/
theorem pullbackComparison_transport_semilinear
    {B S T : Scheme.{u}} (b : S ⟶ B) (c : T ⟶ S) (d : T ⟶ B)
    (h : c ≫ b = d) (X Y : GroupScheme B)
    (f : (baseChange b).obj X ≅ (baseChange b).obj Y)
    (a : S ⟶ S) (ha : a ≫ b = b) (v : T ⟶ T) (hv : v ≫ d = d)
    (hvc : v ≫ c = c ≫ a)
    (w : (baseChange a).obj ((baseChange b).obj Y) ⟶ (baseChange b).obj Y)
    (w' : (baseChange v).obj ((baseChange d).obj Y) ⟶ (baseChange d).obj Y)
    (hf : (baseChange a).map f.hom ≫ w =
      (descentBaseChangeIso b a ha X).hom ≫ f.hom)
    (hw : (baseChange v).map (pullbackComparison b c d h Y).hom ≫ w' =
      (squareComparison c v a c hvc ((baseChange b).obj Y)).hom ≫
        (baseChange c).map w ≫ (pullbackComparison b c d h Y).hom) :
    (baseChange v).map
        ((pullbackComparison b c d h X).symm ≪≫
          (baseChange c).mapIso f ≪≫ pullbackComparison b c d h Y).hom ≫ w' =
      (descentBaseChangeIso d v hv X).hom ≫
        ((pullbackComparison b c d h X).symm ≪≫
          (baseChange c).mapIso f ≪≫ pullbackComparison b c d h Y).hom := by
  have hc := congrArg (fun k => k ≫ (pullbackComparison b c d h X).inv)
    (pullbackComparison_semilinear b c d h a ha v hv hvc X)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hw, squareComparison_naturality_assoc]
  rw [← Category.assoc ((baseChange c).map ((baseChange a).map f.hom))
    ((baseChange c).map w) (pullbackComparison b c d h Y).hom,
    ← Functor.map_comp, hf, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
    (squareComparison c v a c hvc ((baseChange b).obj X)).hom
    ((baseChange c).map (descentBaseChangeIso b a ha X).hom), ← hc]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, (baseChange v).map_id]
  simp only [Category.id_comp, Category.assoc]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

/-- Compatibility of an actual generic comparison with the prescribed
inner Galois action on the target. -/
def InnerGaloisCompatible
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (c : (L ≃ₐ[k] L) → rationalPoints (baseChanged k L G))
    (f : baseChanged k L H ≅ baseChanged k L G) : Prop :=
  ∀ τ : L ≃ₐ[k] L,
    (GroupScheme.baseChange (galoisBaseMap k L τ)).map f.hom ≫
        (innerGaloisDescentIso k G τ (c τ)).hom =
      (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L τ)
        (galoisBaseMap_over k L τ) H).hom ≫ f.hom

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance finiteInnerInertiaNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteInnerInertiaUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteInnerInertiaComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance finiteInnerInertiaFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerInertiaFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerInertiaIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerInertiaIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteInnerInertiaGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerInertiaIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E (show E ≤ inertiaFixedField F from hEinertia.out) x
local instance finiteInnerInertiaCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).2.1
local instance finiteInnerInertiaCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).1

local instance finiteInnerInertiaIntegerFlat : Flat (integerMap F E) :=
  (integerMap_fpqc F E).2.1
local instance finiteInnerInertiaIntegerSurjective : Surjective (integerMap F E) :=
  (integerMap_fpqc F E).1

variable [FiniteDimensional F E] [IsGalois F E]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
    (finiteInertiaGenericIso F E G))
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (d : (E ≃ₐ[F] E) → rationalPoints (baseChanged F E G))
  (hrec : ∀ σ : E ≃ₐ[F] E,
    relativeRationalExtend F E (inertiaFixedField F) G (d σ) =
      c (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
  (hP : P.IsSmooth)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints,
      c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈ P.integralPoints)
  (hstable' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints,
      rationalConjugate F (inertiaFixedField F) G σ.symm
        ((c σ)⁻¹ * g * c σ) ∈ P.integralPoints)
  (hd : ∀ σ τ : E ≃ₐ[F] E,
    d (σ * τ) = d σ * rationalConjugate F E G σ (d τ))
  (hUnram : ArithmeticUnramified F E)



omit [FiniteDimensional F E] in
/-- Every upstairs automorphism restricts compatibly with the actual
intermediate-field inclusion on coefficient spectra. -/
theorem galoisBaseMap_restrictNormal_commutes
    (τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    galoisBaseMap F (inertiaFixedField F) τ ≫ baseMap E (inertiaFixedField F) =
      baseMap E (inertiaFixedField F) ≫ galoisBaseMap F E (τ.restrictNormal E) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact (τ.restrictNormal_commutes E x).symm

set_option maxHeartbeats 800000 in
/-- Exact recovery of every upstairs cocycle value extends finite inner
semilinearity to every inertia-field automorphism. -/
theorem finiteInnerInertiaGenericComparison_semilinear
    (hall : ∀ τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      relativeRationalExtend F E (inertiaFixedField F) G (d (τ.restrictNormal E)) = c τ)
    (τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (GroupScheme.baseChange (galoisBaseMap F (inertiaFixedField F) τ)).map
        (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram).hom ≫
      (innerGaloisDescentIso F G τ (c τ)).hom =
    (descentBaseChangeIso (baseMap F (inertiaFixedField F))
      (galoisBaseMap F (inertiaFixedField F) τ)
      (galoisBaseMap_over F (inertiaFixedField F) τ)
      (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram)).hom ≫
        (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram).hom := by
  exact pullbackComparison_transport_semilinear
    (baseMap F E) (baseMap E (inertiaFixedField F))
    (baseMap F (inertiaFixedField F))
    (coefficientSpec_comp (R := F) (A := E) (B := inertiaFixedField F))
    (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) G
    (finiteInnerGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (galoisBaseMap F E (τ.restrictNormal E)) (galoisBaseMap_over F E (τ.restrictNormal E))
    (galoisBaseMap F (inertiaFixedField F) τ) (galoisBaseMap_over F (inertiaFixedField F) τ)
    (galoisBaseMap_restrictNormal_commutes F E τ)
    (innerGaloisDescentIso F G (τ.restrictNormal E) (d (τ.restrictNormal E))).hom
    (innerGaloisDescentIso F G τ (c τ)).hom
    (finiteInnerGenericComparison_semilinear F E G N P e c d hrec hP hstable hstable' hd hUnram
      (τ.restrictNormal E))
    (by
      rw [← hall τ]
      exact pullbackComparison_innerGaloisDescentIso F E (inertiaFixedField F) G
        (coefficientSpec_comp (R := F) (A := E) (B := inertiaFixedField F))
        (τ.restrictNormal E) τ (galoisBaseMap_restrictNormal_commutes F E τ)
        (d (τ.restrictNormal E)))

/-- The entire recovered comparison has the named all-automorphism
inner Galois compatibility property. -/
theorem finiteInnerInertiaGenericComparison_innerGaloisCompatible
    (hall : ∀ τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      relativeRationalExtend F E (inertiaFixedField F) G (d (τ.restrictNormal E)) = c τ) :
    InnerGaloisCompatible F (inertiaFixedField F)
      (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) G c
      (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram) :=
  finiteInnerInertiaGenericComparison_semilinear F E G N P e c d hrec hP hstable hstable' hd hUnram hall

end Langlands.GroupScheme.IntegralModel
