import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.GeneralLinearInfiniteAdelicEnveloping
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth

/-! # The deformed enveloping action from real operators on a section carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

namespace Langlands.Global.EisensteinJet

open AdelicGroupPoints InfiniteAdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

section Slices

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "AdelicPoints" => AdelicGroupPoints F G
local notation "SmoothFunctions" => InfinitePlotSmoothFunctions F G
local instance deformedEnvelopeSlicesGroup : AddCommGroup SmoothFunctions := Submodule.addCommGroup _

/-- The realized section functions have smooth infinite slices at every finite argument. -/
def HasSmoothSectionSlices (j : V →ₗ[ℂ] (AdelicPoints → ℂ)) : Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  ∀ (v : V) (b : FiniteAdelicGroupPoints F G),
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => j v (pair F G a b))

/-- Evaluate a realized, parameter-twisted section on a smooth infinite slice. -/
def twistedSectionSlice
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    {K : Subgroup AdelicPoints} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (AdelicPoints → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j)
    (b : FiniteAdelicGroupPoints F G) : V →ₗ[ℂ] SmoothFunctions := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  refine
    { toFun := fun v => ⟨fun a => hK.parameterTwist (j v) lam (pair F G a b), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · rw [show SmoothFunctions = manifoldSmoothFunctions F G hsmooth from
      plotSmoothFunctions_eq_manifoldSmoothFunctions F G hsmooth]
    exact hK.contMDiff_parameterTwist_slice hsmooth hH (j v) lam (hSmooth v) b
  · intro v w
    apply Subtype.ext
    funext a
    change j (v + w) (pair F G a b) * hK.heightPower lam (pair F G a b) = _
    rw [map_add, Pi.add_apply]
    exact add_mul _ _ _
  · intro c v
    apply Subtype.ext
    funext a
    change j (c • v) (pair F G a b) * hK.heightPower lam (pair F G a b) = _
    rw [map_smul, Pi.smul_apply]
    exact smul_mul_assoc _ _ _

private theorem eq_of_twistedSectionSlices
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    {K : Subgroup AdelicPoints} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (AdelicPoints → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j) (hj : Function.Injective j)
    {v w : V} (h : ∀ b, twistedSectionSlice hsmooth hK hH lam j hSmooth b v =
      twistedSectionSlice hsmooth hK hH lam j hSmooth b w) : v = w := by
  apply hj
  funext g
  let a := infinite F G g
  let b := finite F G g
  have hg := congrFun (congrArg Subtype.val (h b)) a
  change j v (pair F G a b) * hK.heightPower lam (pair F G a b) =
    j w (pair F G a b) * hK.heightPower lam (pair F G a b) at hg
  rw [show pair F G a b = g from pair_projections F G g] at hg
  exact mul_right_cancel₀ (hK.heightPower_ne_zero lam g) hg

end Slices

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {V : Type*} [AddCommGroup V] [Module ℂ V]

local notation "GL[" F "," n "]" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local instance deformedEnvelopeGLAffine : IsAffine (GL[F, n]).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GL[F, n]
local notation "Slices" => InfinitePlotSmoothFunctions F GL[F, n]
local notation "FinPts" => FiniteAdelicGroupPoints F GL[F, n]
local notation "RealLie" => ArchimedeanGL.RealLieAlgebra F n
local notation "Enveloping" => ArchimedeanGL.EnvelopingAlgebra F n
local instance deformedEnvelopeGLSlicesGroup : AddCommGroup Slices := Submodule.addCommGroup _

variable {d : ℕ}

local notation "I" => 𝓘(ℝ, smoothModel F d)

local notation "tangent[" h "," X "]" => LinearEquiv.symm (infiniteRealLieAlgebraEquiv F n h) X

/-- Compatibility of a real operator family with the deformed scalar derivatives. -/
def HasDeformedRealSectionOperators
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (D : RealLie → Module.End ℂ V) : Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GL[F, n] hsmooth
  ∀ X v, j (D X v) = hK.parameterDirectionalSection hsmooth lam tangent[hsmooth, X] (j v)

private theorem twistedSectionSlice_intertwines
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j)
    (D : RealLie → Module.End ℂ V)
    (hD : HasDeformedRealSectionOperators F n hsmooth hK lam j D)
    (b : FinPts) (X : RealLie) (v : V) :
    letI := fun w : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F w
    letI := smoothChartedSpace F GL[F, n] hsmooth
    twistedSectionSlice hsmooth hK hH lam j hSmooth b (D X v) =
      plotSmoothDifferential F GL[F, n] hsmooth tangent[hsmooth, X]
        (twistedSectionSlice hsmooth hK hH lam j hSmooth b v) := by
  let := fun w : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F w
  let := smoothChartedSpace F GL[F, n] hsmooth
  apply Subtype.ext
  funext a
  let f := twistedSectionSlice hsmooth hK hH lam j hSmooth b v
  change j (D X v) (pair F GL[F, n] a b) * hK.heightPower lam (pair F GL[F, n] a b) =
    groupDirectionalValue I tangent[hsmooth, X] f.val a
  rw [hD X v]
  change (groupDirectionalValue I tangent[hsmooth, X] (fun c => hK.parameterTwist (j v) lam
      (pair F GL[F, n] c (finite F GL[F, n] (pair F GL[F, n] a b)))) (infinite F GL[F, n] (pair F GL[F, n] a b)) /
        hK.heightPower lam (pair F GL[F, n] a b)) * hK.heightPower lam (pair F GL[F, n] a b) = _
  rw [finite_pair, infinite_pair, div_mul_cancel₀ _ (hK.heightPower_ne_zero lam _)]
  rfl

private def deformedRealLieAction
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j) (hj : Function.Injective j)
    (D : RealLie → Module.End ℂ V)
    (hD : HasDeformedRealSectionOperators F n hsmooth hK lam j D)
    (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth) : RealLie →ₗ⁅ℝ⁆ Module.End ℂ V := by
  let := fun w : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F w
  let := smoothChartedSpace F GL[F, n] hsmooth
  let := smoothLieGroup F GL[F, n] hsmooth
  let : LieGroup I (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F GL[F, n]) := LieGroup.of_le (n := ∞) (by simp)
  let A := (realPlotSmoothLieAction F GL[F, n] hsmooth hcalc).comp
    (infiniteRealLieEquiv F n hsmooth hcalc).symm.toLieHom
  let J := twistedSectionSlice hsmooth hK hH lam j hSmooth
  have hInter (b : FinPts) (X : RealLie) (v : V) : J b (D X v) = A X (J b v) :=
    twistedSectionSlice_intertwines F n hsmooth hK hH lam j hSmooth D hD b X v
  have hEq {v w : V} (h : ∀ b, J b v = J b w) : v = w :=
    eq_of_twistedSectionSlices hsmooth hK hH lam j hSmooth hj h
  refine { toFun := D, map_add' := ?_, map_smul' := ?_, map_lie' := ?_ }
  · intro X Y
    apply LinearMap.ext
    intro v
    apply hEq
    intro b
    simp only [LinearMap.add_apply, map_add, hInter]
  · intro c X
    apply LinearMap.ext
    intro v
    apply hEq
    intro b
    simp only [LinearMap.smul_apply, LinearMap.map_smul_of_tower, hInter, map_smul,
      RingHom.id_apply]
  · intro X Y
    apply LinearMap.ext
    intro v
    apply hEq
    intro b
    change J b (D ⁅X, Y⁆ v) = J b (D X (D Y v) - D Y (D X v))
    simp only [map_sub, hInter, LieHom.map_lie]
    rfl

/-- Real operators with the deformed generator formula extend to an action of
 the original matrix enveloping algebra on the section carrier. -/
def deformedSectionEnvelopingAction
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j) (hj : Function.Injective j)
    (D : RealLie → Module.End ℂ V)
    (hD : HasDeformedRealSectionOperators F n hsmooth hK lam j D)
    (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth) : Enveloping →ₐ[ℂ] Module.End ℂ V :=
  Langlands.Algebra.ComplexLieExtension.enveloping
    (deformedRealLieAction F n hsmooth hK hH lam j hSmooth hj D hD hcalc)

/-- On a real generator the extended action is the given deformed real operator. -/
theorem deformedSectionEnvelopingAction_real_generator
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, n]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (hSmooth : HasSmoothSectionSlices hsmooth j) (hj : Function.Injective j)
    (D : RealLie → Module.End ℂ V)
    (hD : HasDeformedRealSectionOperators F n hsmooth hK lam j D)
    (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth) (X : RealLie) :
    deformedSectionEnvelopingAction F n hsmooth hK hH lam j hSmooth hj D hD hcalc
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) = D X :=
  Langlands.Algebra.ComplexLieExtension.enveloping_real_generator _ X

end Langlands.Global.EisensteinJet
