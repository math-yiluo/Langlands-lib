import Langlands.Representation.Induction.SplitKernelCompact
import Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Jacquet.Coinvariants

/-!
# Relative coinvariant integration for a split kernel

Compose actual compact kernel restriction with the published quotient integral.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis

universe uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L] [TopologicalSpace L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] [TopologicalSpace L] in
/-- Closedness of the actual intersection in the kernel topology. -/
theorem isClosed_splitKernelIntersection (r : G →* L) (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    IsClosed ((H.comap r.ker.subtype : Subgroup r.ker) : Set r.ker) :=
  hH.preimage continuous_subtype_val

omit [IsTopologicalGroup G] [TopologicalSpace L] in
/-- The actual inclusion of the kernel intersection into the inducing group
is continuous for both subgroup topologies. -/
theorem continuous_splitKernelInducing (r : G →* L) (H : Subgroup G) :
    Continuous (r.ker.subtype.subgroupComap H) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] [TopologicalSpace L] in
/-- Smoothness restricts to the actual intersection, without a new premise. -/
theorem isSmooth_splitKernelInducing (r : G →* L) (H : Subgroup G)
    (σ : Representation ℂ H V) (hσ : IsSmooth σ) :
    IsSmooth (σ.comp (r.ker.subtype.subgroupComap H)) :=
  isSmooth_comp _ (continuous_splitKernelInducing r H) hσ

variable [LocallyCompactSpace G]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "I" => H.comap r.ker.subtype
local notation "σI" => σ.comp (r.ker.subtype.subgroupComap H)
local notation "E" => splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ

/-- The actual kernel restriction equivalence induces a linear equivalence
on the actual coinvariant quotients. Its inverse is induced by extension. -/
def splitKernelCompactCoinvariantRestrictEquiv :
    Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype) ≃ₗ[ℂ]
      Representation.Coinvariants (compactInduced I σI) where
  toLinearMap := Representation.Coinvariants.map _ _ (E).toIntertwiningMap
  invFun := Representation.Coinvariants.map _ _ (E).symm.toIntertwiningMap
  left_inv z := by
    obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    change Representation.Coinvariants.mk _ ((E).symm (E f)) =
      Representation.Coinvariants.mk _ f
    rw [(E).symm_apply_apply]
  right_inv z := by
    obtain ⟨k, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    change Representation.Coinvariants.mk _ (E ((E).symm k)) =
      Representation.Coinvariants.mk _ k
    rw [(E).apply_symm_apply]

variable [mQ : MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
variable [bQ : BorelSpace (LeftQuotient (H.comap r.ker.subtype))]
variable (ν : @Measure (LeftQuotient (H.comap r.ker.subtype)) mQ)
variable [IsFiniteMeasureOnCompacts ν]

/-- Relative integration before descent is the actual quotient integral
of the function restricted to the actual kernel. -/
def splitKernelCompactIntegral : CompactFunctions H σ →ₗ[ℂ]
    Representation.Coinvariants σI :=
  (compactCoinvariantIntegral I σI ν).comp (E).toLinearMap

/-- The integral's simple-function integrand takes exactly the class of f(n). -/
@[simp] theorem splitKernelCompactIntegrand_mk (f : CompactFunctions H σ) (n : r.ker) :
    quotientCoinvariantSimple I σI (E f) (quotientMap I n) =
      Representation.Coinvariants.mk σI (eval H σ f.1 (n : G)) := rfl

/-- The representative formula uses the supplied quotient measure and the
published finite-fiber algebraic integral. -/
theorem splitKernelCompactIntegral_apply (f : CompactFunctions H σ) :
    splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple I σI (E f)) := rfl

variable (hν : ∀ n : r.ker, MeasurePreserving (rightTranslate (H.comap r.ker.subtype) n) ν ν)

include hν in
/-- Every actual kernel right translate has the same relative integral. -/
theorem splitKernelCompactIntegral_translate (n : r.ker) (f : CompactFunctions H σ) :
    splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν
        (compactInduced H σ (n : G) f) =
      splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f := by
  change compactCoinvariantIntegral I σI ν (E (compactInduced H σ (n : G) f)) =
    compactCoinvariantIntegral I σI ν (E f)
  have he : E (compactInduced H σ (n : G) f) = compactInduced I σI n (E f) :=
    Representation.IntertwiningMap.isIntertwining _ _ (E).toIntertwiningMap n f
  rw [he]
  exact compactCoinvariantIntegral_translate I σI ν hν n (E f)

/-- Descend to the actual kernel coinvariants by composing the induced
restriction map with the published absolute integral descent. -/
def splitKernelCompactCoinvariantDesc :
    Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype) →ₗ[ℂ]
      Representation.Coinvariants σI :=
  (compactCoinvariantDesc I σI ν hν).comp
    (splitKernelCompactCoinvariantRestrictEquiv r s hrs hr hs H hH hsH σ hσ).toLinearMap

@[simp] theorem splitKernelCompactCoinvariantDesc_mk (f : CompactFunctions H σ) :
    splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν hν
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f) =
      splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f := rfl

/-- The descended map has the required actual quotient-integral formula. -/
theorem splitKernelCompactCoinvariantDesc_mk_integral (f : CompactFunctions H σ) :
    splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν hν
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f) =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple I σI (E f)) := rfl

section Naturality

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)

/-- Relative integration commutes with every coefficient intertwiner. -/
theorem splitKernelCompactIntegral_natural (f : CompactFunctions H σ) :
    splitKernelCompactIntegral r s hrs hr hs H hH hsH τ hτ ν (compactInducedMap H T f) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f) := by
  change compactCoinvariantIntegral I (τ.comp (r.ker.subtype.subgroupComap H)) ν
      (splitKernelCompactEquiv r s hrs hr hs H hH hsH τ hτ (compactInducedMap H T f)) = _
  rw [splitKernelCompactEquiv_natural r s hrs hr hs H hH hsH hσ hτ T]
  exact compactCoinvariantIntegral_natural I σI ν (splitKernelInducingMap r H T) (E f)

/-- The actual coinvariant descent is natural in independent coefficient universes. -/
theorem splitKernelCompactCoinvariantDesc_natural
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH τ hτ ν hν
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν hν z) := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  exact splitKernelCompactIntegral_natural r s hrs hr hs H hH hsH σ hσ ν hτ T f

end Naturality

section Bijectivity

variable [T2Space G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
  ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
variable (μN : Measure r.ker) (μI : Measure (H.comap r.ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible (H.comap r.ker.subtype) μN μI ν)

include hBasis in
/-- Bijectivity follows from actual kernel restriction and the proved
bijectivity of the supplied compatible quotient integral. -/
theorem splitKernelCompactCoinvariantDesc_bijective :
    Function.Bijective (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
      hCompatible.right_invariant) := by
  exact (compactCoinvariantIntegralBijective hBasis I
      (isClosed_splitKernelIntersection r H hH) μN μI ν hCompatible V σI
      (isSmooth_splitKernelInducing r H σ hσ)).comp
    (splitKernelCompactCoinvariantRestrictEquiv r s hrs hr hs H hH hsH σ hσ).bijective

/-- The actual relative quotient integral as a natural linear equivalence. -/
def splitKernelCompactCoinvariantEquiv :
    Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype) ≃ₗ[ℂ]
      Representation.Coinvariants σI :=
  LinearEquiv.ofBijective
    (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
      hCompatible.right_invariant)
    (splitKernelCompactCoinvariantDesc_bijective r s hrs hr hs H hH hsH σ hσ ν
      hBasis μN μI hCompatible)

@[simp] theorem splitKernelCompactCoinvariantEquiv_mk (f : CompactFunctions H σ) :
    splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ ν
        hBasis μN μI hCompatible
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f) =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple I σI (E f)) := rfl

/-- Naturality holds for arbitrary coefficient intertwiners after bundling
bijectivity as the relative linear equivalence. -/
theorem splitKernelCompactCoinvariantEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH τ hτ ν
        hBasis μN μI hCompatible
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ ν
          hBasis μN μI hCompatible z) :=
  splitKernelCompactCoinvariantDesc_natural r s hrs hr hs H hH hsH σ hσ ν
    hCompatible.right_invariant hτ T z

end Bijectivity

end Langlands.Induction
