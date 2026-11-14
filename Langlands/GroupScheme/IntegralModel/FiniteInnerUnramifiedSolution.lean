import Langlands.GroupScheme.IntegralModel.FiniteInnerUnramifiedIntegralDatum
import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedSolution

/-! # Smooth effective descent with the prescribed inner generic action -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

variable {B S U V : Scheme.{u}}

/-- Semilinear comparison also permits an arbitrary prescribed target
semilinear map, such as an inner-twisted Galois map. -/
theorem squareSolutionComparison_semilinear_target
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) {X : GroupScheme B} {H : GroupScheme S}
    {G : GroupScheme U} (t : (baseChange b).obj X ≅ H)
    (n : (baseChange c).obj H ≅ (baseChange e).obj G)
    (a : S ⟶ S) (ha : a ≫ b = b) (v : V ⟶ V) (hv : v ≫ e = e)
    (hvc : v ≫ c = c ≫ a) (E : (baseChange a).obj H ≅ H)
    (w : (baseChange v).obj ((baseChange e).obj G) ⟶ (baseChange e).obj G)
    (ht : (baseChange a).map t.hom ≫ E.hom =
      (descentBaseChangeIso b a ha X).hom ≫ t.hom)
    (hn : (baseChange v).map n.hom ≫ w =
      (squareComparison c v a c hvc H).hom ≫ (baseChange c).map E.hom ≫ n.hom) :
    (baseChange v).map (squareSolutionComparison b c d e h t n).hom ≫ w =
      (descentBaseChangeIso e v hv ((baseChange d).obj X)).hom ≫
        (squareSolutionComparison b c d e h t n).hom := by
  have hc := congrArg (fun f => f ≫ (squareComparison b c d e h X).inv)
    (squareComparison_semilinear b c d e h a ha v hv hvc X)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  simp only [squareSolutionComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn, squareComparison_naturality_assoc]
  rw [← Category.assoc ((baseChange c).map ((baseChange a).map t.hom))
    ((baseChange c).map E.hom) n.hom, ← Functor.map_comp, ht, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (squareComparison c v a c hvc ((baseChange b).obj X)).hom
    ((baseChange c).map (descentBaseChangeIso b a ha X).hom), ← hc]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id]
  rw [(baseChange v).map_id]
  simp only [Category.id_comp, Category.assoc]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

section GeneralSolution

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

/-- An effective solution recovers the original model over its specified
generic comparison, even when the descended generic group is a form. -/
def solutionModelIso (hN : N.IsSmooth) :
    ((solutionModel s hN).baseChange A L).Iso N (solutionGenericComparison s hN) where
  iso := s.iso
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap A L)).map s.iso.hom ≫
      N.genericIso.hom =
        ((solutionModel s hN).baseChangeGenericIso A L).hom ≫
          (((solutionModel s hN).baseChangeGenericIso A L).inv ≫
            (GroupScheme.baseChange (Spec.algebraMap A L)).map s.iso.hom ≫
              N.genericIso.hom)
    rw [Iso.hom_inv_id_assoc]

/-- A prescribed generic semilinear map is respected by the effective
generic comparison if it is respected by the integral comparison. -/
theorem solutionGenericComparison_semilinear_target (hN : N.IsSmooth)
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
    (ha : a ≫ Spec.algebraMap R A = Spec.algebraMap R A)
    (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
    (hv : v ≫ Spec.algebraMap K L = Spec.algebraMap K L)
    (hvc : v ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a)
    (Uiso : (GroupScheme.baseChange a).obj N.group ≅ N.group)
    (w : (GroupScheme.baseChange v).obj
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G) ⟶
        (GroupScheme.baseChange (Spec.algebraMap K L)).obj G)
    (hs : (GroupScheme.baseChange a).map s.iso.hom ≫ Uiso.hom =
      (descentBaseChangeIso (Spec.algebraMap R A) a ha s.obj).hom ≫ s.iso.hom)
    (hn : (GroupScheme.baseChange v).map N.genericIso.hom ≫ w =
      (squareComparison (Spec.algebraMap A L) v a (Spec.algebraMap A L)
        hvc N.group).hom ≫ (GroupScheme.baseChange (Spec.algebraMap A L)).map Uiso.hom ≫
          N.genericIso.hom) :
    (GroupScheme.baseChange v).map (solutionGenericComparison s hN).hom ≫ w =
      (descentBaseChangeIso (Spec.algebraMap K L) v hv
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj)).hom ≫
          (solutionGenericComparison s hN).hom := by
  rw [solutionGenericComparison_eq_square]
  exact squareSolutionComparison_semilinear_target _ _ _ _ _ s.iso N.genericIso
    a ha v hv hvc Uiso w hs hn

end GeneralSolution

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance finiteInnerSolutionNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteInnerSolutionUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteInnerSolutionComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance finiteInnerSolutionFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerSolutionFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerSolutionIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerSolutionIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteInnerSolutionGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerSolutionIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E (show E ≤ inertiaFixedField F from hEinertia.out) x
local instance finiteInnerSolutionCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).2.1
local instance finiteInnerSolutionCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).1

local instance finiteInnerSolutionIntegerFlat : Flat (integerMap F E) :=
  (integerMap_fpqc F E).2.1
local instance finiteInnerSolutionIntegerSurjective : Surjective (integerMap F E) :=
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

/-- The finite inner integral datum has an actual affine fpqc solution. -/
def finiteInnerIntegralSolution :
    Solution (finiteInnerIntegralDatum F E G N P e c d hrec hP hstable hstable' hd hUnram) := by
  let : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  exact (finiteInnerIntegralDatum F E G N P e c d hrec hP hstable hstable' hd hUnram).affineSolution

instance finiteInnerIntegralSolution_isAffine :
    IsAffine (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).obj.X.left := by
  let : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  exact Datum.affineSolution_isAffine _

/-- Smoothness follows from the supplied model through exact recovery and
then fpqc effectivity. -/
theorem finiteInnerIntegralSolution_smooth :
    Smooth (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).obj.X.hom := by
  let : Smooth N.group.X.hom := isSmooth_of_coefficientIso N P e hP
  exact (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).smooth

/-- The solution comparison intertwines the actual finite integral twist. -/
theorem finiteInnerIntegralSolution_semilinear (σ : E ≃ₐ[F] E) :
    (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))).map
        (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).iso.hom ≫
      (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable' σ).iso.hom =
    (descentBaseChangeIso (integerMap F E)
      (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
      (finiteIntegerBaseAut_over F E σ)
      (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).obj).hom ≫
        (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).iso.hom := by
  obtain ⟨i, rfl⟩ := (galoisIndexEquiv F E).surjective σ
  exact (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).semilinear
    (integerBaseAut F E i) (finiteIntegerBaseAut_over F E (galoisIndexEquiv F E i))
    (integerComponent F E hUnram i) (integerComponent_fst F E hUnram i)
    (integerComponent_snd F E hUnram i)
    (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable'
      (galoisIndexEquiv F E i)).iso
    (pullIso_finiteInnerIntegralDatum F E G N P e c d hrec hP hstable hstable' hd hUnram i)

/-- The descended group has its own actual generic fibre over F. -/
abbrev finiteInnerGenericGroup : GroupScheme (Spec (CommRingCat.of F)) :=
  (GroupScheme.baseChange (Spec.algebraMap (baseIntegers F) F)).obj
    (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram).obj

/-- The descended object is a smooth model of its actual generic fibre. -/
def normFiniteInnerModel :
    IntegralModel (baseIntegers F) F
      (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) :=
  solutionModel (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (isSmooth_of_coefficientIso N P e hP)

theorem normFiniteInnerModel_smooth :
    (normFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).IsSmooth :=
  isSmooth_solutionModel
    (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (isSmooth_of_coefficientIso N P e hP)

/-- Its actual generic comparison over E, without identifying the descended
F-group with the original G. -/
def finiteInnerGenericComparison :
    baseChanged F E
        (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) ≅
      baseChanged F E G :=
  solutionGenericComparison
    (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (isSmooth_of_coefficientIso N P e hP)

/-- Coefficient extension of the descended model recovers N with exactly the
generic comparison supplied by effectivity. -/
def normFiniteInnerModelIso :
    ((normFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).baseChange
      (extensionIntegers F E) E).Iso N
        (finiteInnerGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram) :=
  solutionModelIso
    (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (isSmooth_of_coefficientIso N P e hP)

set_option maxHeartbeats 800000 in
/-- The effective generic comparison carries canonical Galois transport to
the specified inner twist by the recovered finite cocycle. -/
theorem finiteInnerGenericComparison_semilinear (σ : E ≃ₐ[F] E) :
    (GroupScheme.baseChange (galoisBaseMap F E σ)).map
        (finiteInnerGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram).hom ≫
      (innerGaloisDescentIso F G σ (d σ)).hom =
    (descentBaseChangeIso (baseMap F E) (galoisBaseMap F E σ)
      (galoisBaseMap_over F E σ)
      (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram)).hom ≫
        (finiteInnerGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram).hom := by
  exact solutionGenericComparison_semilinear_target
    (finiteInnerIntegralSolution F E G N P e c d hrec hP hstable hstable' hd hUnram)
    (isSmooth_of_coefficientIso N P e hP)
    (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
    (finiteIntegerBaseAut_over F E σ) (galoisBaseMap F E σ) (galoisBaseMap_over F E σ)
    (finiteIntegerBaseAut_generic F E σ)
    (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable' σ).iso
    (innerGaloisDescentIso F G σ (d σ)).hom
    (finiteInnerIntegralSolution_semilinear F E G N P e c d hrec hP hstable hstable' hd hUnram σ)
    (finiteInnerIntegralSemilinearIso_generic F E G N P e c d hrec hP hstable hstable' σ)

end Langlands.GroupScheme.IntegralModel
