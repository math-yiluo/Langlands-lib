import Langlands.Representation.Aubert.General.RationalGeometricCompactComparison
import Langlands.Representation.Induction.SplitStagesAmbientHaar

/-! # Ambient Haar characters of the actual rational compact comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 240000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme MeasureTheory MeasureTheory.Measure
open Langlands.AlgebraicGeometry.PointTopology
open Induction
open scoped NNReal

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]

local notation "A" => RationalPoint k G.X
local notation "Q" => parabolic i ν I
local notation "L" => levi i ν I
local notation "U" => unipotent i ν I
local notation "C" => geometricTargetIntersection U (parabolic i ν J) (n : A)
local notation "Kt" => geometricTargetIntersection L (parabolic i ν J) (n : A)
local notation "K" => Subgroup.subgroupOf Kt L
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection Q (parabolic i ν J) (n : A)) Q
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "hker" => geometricSplit_ker_le i ν I J dI n
local notation "rP" => splitStagesRetraction dI.projection s
  (fun m => dI.projection_levi m) P hker
local notation "sP" => MonoidHom.subgroupComap s P
local notation "HP" => Subgroup.subgroupOf H P
local notation "eK" => geometricSplitQuotientEquiv i ν I J dI n
local notation "hSI" => (fun l : Subgroup.comap s P => geometricSplit_section_mem i ν I J dI n l)
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n

/-- The restricted projection kernel is the original radical, with its
original induced topology and the identical ambient group element. -/
def geometricCompactKernelEquiv : N ≃ₜ* U :=
  splitStagesAmbientKernelEquiv dI P hker

@[simp] theorem geometricCompactKernelEquiv_apply (x : N) :
    (geometricCompactKernelEquiv i ν I J dI n x : A) = (((x : P) : Q) : A) :=
  splitStagesAmbientKernelEquiv_apply dI P hker x

/-- The nested kernel intersection is literally the ambient intersection
of the original radical with the conjugated inducing parabolic. -/
def geometricCompactKernelIntersectionEquiv : D ≃ₜ* C :=
  splitStagesAmbientIntersectionEquiv dI P hker
    ((parabolic i ν J).map (MulAut.conj (n : A) : A →* A))

@[simp] theorem geometricCompactKernelIntersectionEquiv_apply (x : D) :
    (geometricCompactKernelIntersectionEquiv i ν I J dI n x : A) =
      ((((x : N) : P) : Q) : A) :=
  splitStagesAmbientIntersectionEquiv_apply dI P hker
    ((parabolic i ν J).map (MulAut.conj (n : A) : A →* A)) x

omit [TopologicalSpace A] in
include dI in
/-- The whole target intersection parabolic normalizes the actual correction
subgroup, using its two literal intersection containments. -/
theorem geometricCompactTarget_normalizes_correction :
    Kt ≤ Subgroup.normalizer (C : Set A) :=
  splitStagesAmbient_normalizes dI
    ((parabolic i ν J).map (MulAut.conj (n : A) : A →* A))

section AmbientHaar

variable [IsTopologicalGroup (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

local notation "hC" => isClosed_geometricTargetIntersection U (parabolic i ν J) hUI hPJ (n : A)
local notation "hKC" => geometricCompactTarget_normalizes_correction i ν I J dI n
local notation "eKt" =>
  Subgroup.subgroupOfEquivOfLe (inf_le_left : Kt ≤ L)

/-- The original radical Haar modulus, restricted to the whole target
intersection parabolic. -/
def geometricCompactRadicalModulus : K →* ℝ≥0ˣ :=
  (HaarModulus.closedRestrictCharacter U hUI L dI.levi_le_normalizer).comp (K).subtype

/-- The ambient correction-subgroup Haar modulus on the same whole parabolic. -/
def geometricCompactCorrectionModulus : K →* ℝ≥0ˣ :=
  (HaarModulus.closedRestrictCharacter C hC Kt hKC).comp (MulEquiv.toMonoidHom eKt)

variable
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernel i ν I J dI n)]
  [BorelSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernelIntersection i ν I J dI n)]
  [BorelSpace (geometricCompactKernelIntersection i ν I J dI n)]

local notation "hHc" => isClosed_geometricStabilizer i ν I J n hPI hPJ
local notation "hHPc" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subgroup.subtype P)) hHc
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δC" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ

set_option maxHeartbeats 800000 in
/-- The exact integral character is the original radical modulus divided by
the actual correction-subgroup modulus. Both inverse-conjugation moduli
are transported through the original ambient group elements. -/
theorem geometricCompactHaarCharacter_eq_ambient (l : K) :
    geometricCompactHaarCharacter i ν I J dI n hPI hPJ l =
      Jacquet.complexCharacter δU l / Jacquet.complexCharacter δC l := by
  have hr : splitKernelHaarRatio rP sP HP hSI hHPc ((eK).symm l) = δU l / δC l :=
    @splitStagesAmbientHaarRatio_apply A _ _ Q L U dI P hker
      ((parabolic i ν J).map (MulAut.conj (n : A) : A →* A)) _ _ hUI
      (isClosed_map_conj (parabolic i ν J) hPJ (n : A))
      (inferInstanceAs (LocallyCompactSpace N)) (inferInstanceAs (MeasurableSpace N))
      (inferInstanceAs (BorelSpace N)) (inferInstanceAs (MeasurableSpace D))
      (inferInstanceAs (BorelSpace D)) hSI hHPc ((eK).symm l)
  apply Units.ext
  change (((((splitKernelHaarRatio rP sP HP hSI hHPc ((eK).symm l) : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ)) = _
  rw [hr]
  simp only [Units.val_div_eq_div_val, Jacquet.complexCharacter_apply,
    NNReal.coe_div, Complex.ofReal_div]

end AmbientHaar

section SmoothModuli

variable [NonarchimedeanGroup (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

local notation "hC" => isClosed_geometricTargetIntersection U (parabolic i ν J) hUI hPJ (n : A)
local notation "hKC" => geometricCompactTarget_normalizes_correction i ν I J dI n
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δC" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ

/-- The ambient radical modulus has open kernel on the whole target
intersection, by restriction of the original normalizer Haar character. -/
theorem isOpen_ker_geometricCompactRadicalModulus :
    IsOpen ((geometricCompactRadicalModulus i ν I J dI n hUI).ker : Set K) :=
  (HaarModulus.isOpen_ker_closedRestrictCharacter U hUI L dI.levi_le_normalizer).preimage
    continuous_subtype_val

/-- The actual correction-subgroup modulus has open kernel on the same
whole target intersection. -/
theorem isOpen_ker_geometricCompactCorrectionModulus :
    IsOpen ((geometricCompactCorrectionModulus i ν I J dI n hUI hPJ).ker : Set K) :=
  (HaarModulus.isOpen_ker_closedRestrictCharacter C hC Kt hKC).preimage
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

variable
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernel i ν I J dI n)]
  [BorelSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernelIntersection i ν I J dI n)]
  [BorelSpace (geometricCompactKernelIntersection i ν I J dI n)]

include hUI in
/-- The actual compact integral character has open kernel, so its scalar
twist preserves smooth representations. -/
theorem isOpen_ker_geometricCompactHaarCharacter :
    IsOpen ((geometricCompactHaarCharacter i ν I J dI n hPI hPJ).ker : Set K) := by
  apply Subgroup.isOpen_mono (H₁ := (δU).ker ⊓ (δC).ker)
  · intro l hl
    change geometricCompactHaarCharacter i ν I J dI n hPI hPJ l = 1
    rw [geometricCompactHaarCharacter_eq_ambient i ν I J dI n hUI hPJ hPI l]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Jacquet.complexCharacter_apply,
      show δU l = 1 from hl.1, show δC l = 1 from hl.2]
    simp only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, div_self one_ne_zero]
  · exact (isOpen_ker_geometricCompactRadicalModulus i ν I J dI n hUI).inter
      (isOpen_ker_geometricCompactCorrectionModulus i ν I J dI n hUI hPJ)

end SmoothModuli

end Langlands.Aubert.General.RationalPointFamily
