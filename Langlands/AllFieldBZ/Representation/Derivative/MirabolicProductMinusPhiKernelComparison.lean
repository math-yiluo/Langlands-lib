import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitRadicals
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitSectionCoefficients
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitStages
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinus
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding phiMinusKernelAction phiMinusKernelAction_smooth phiMinusKernelEquiv phiMinusKernelEquiv_mk phiMinusKernelEquiv_natural phiMinusKernelFunctor phiMinusKernelIso phiMinusKernelMap phiMinusNormalizedKernelEquiv phiMinusNormalizedKernelEquiv_mk phiMinusNormalizedKernelIso
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.HarmonicAnalysis
open Langlands.Induction
open Langlands.Induction.SplitKernelLocalization
open Langlands.MixedProductTensor
universe uF uV uW

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Restrict to the actual plus subgroup and localize by its positive kernel
character, retaining the actual unnormalized successor section action. -/
abbrev phiMinusKernelAction (ρ : Representation ℂ (mirabolic (n + 1) F.Carrier) V) :
    letI := T.topology
    Representation ℂ (mirabolic n F.Carrier)
      (Jacquet.Localization.Coinvariants (ρ.comp (plusSubgroup n F.Carrier).subtype)
        (plusProjection (n := n) (F := F.Carrier)).ker (plusKernelTheta ψ n)) :=
  letI := T.topology
  localizedAction (plusProjection (n := n) (F := F.Carrier))
    (plusSuccessor (n := n) (F := F.Carrier)) (plusKernelTheta ψ n)
    (plusKernelTheta_sectionInvariant ψ n) (ρ.comp (plusSubgroup n F.Carrier).subtype)

/-- The actual map on the kernel-localized classes, for arbitrary independent
source and target coefficient universes. -/
abbrev phiMinusKernelMap
    {ρ : Representation ℂ (mirabolic (n + 1) F.Carrier) V}
    {σ : Representation ℂ (mirabolic (n + 1) F.Carrier) W}
    (f : ρ.IntertwiningMap σ) :
    letI := T.topology
    (phiMinusKernelAction T ψ n ρ).IntertwiningMap (phiMinusKernelAction T ψ n σ) :=
  letI := T.topology
  sectionMap (plusProjection (n := n) (F := F.Carrier))
    (plusSuccessor (n := n) (F := F.Carrier)) (plusKernelTheta ψ n)
    (plusKernelTheta_sectionInvariant ψ n) (pullbackMap (plusSubgroup n F.Carrier).subtype f)

/-- Smoothness follows from the actual continuous restriction and section,
and the actual surjective character quotient. -/
theorem phiMinusKernelAction_smooth
    (ρ : Representation ℂ (mirabolic (n + 1) F.Carrier) V)
    (hρ : letI := T.topology; IsSmooth ρ) :
    letI := T.topology
    IsSmooth (phiMinusKernelAction T ψ n ρ) := by
  let := T.topology
  exact isSmooth_sectionAction _ _ _ _ _ continuous_plusSuccessor
    (isSmooth_comp (plusSubgroup n F.Carrier).subtype continuous_subtype_val hρ)

/-- Removing the redundant plus membership identifies the full positive kernel
quotient with the actual unnormalized Phi-minus quotient, including its action. -/
def phiMinusKernelEquiv
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)) :
    letI := T.topology
    Representation.Equiv (phiMinusKernelAction T ψ n A.representation)
      ((Mirabolic.phiMinusUnnormalized T ψ n).obj A).representation :=
  letI := T.topology
  Representation.Equiv.mk
    (Jacquet.Localization.transportEquiv
      (A.representation.comp (plusSubgroup n F.Carrier).subtype) A.representation
      (plusProjection (n := n) (F := F.Carrier)).ker (radical (n + 1) F.Carrier)
      (plusKernelTheta ψ n) (T.mirabolicTheta ψ n) (plusKernelRadicalEquiv n)
      (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl))
    (fun _ => LinearMap.ext fun z => Submodule.Quotient.induction_on _ z fun _ => rfl)

@[simp] theorem phiMinusKernelEquiv_mk
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
    (v : letI := T.topology; A) :
    letI := T.topology
    phiMinusKernelEquiv T ψ n A (Jacquet.Localization.mk _ _ _ v) =
      Mirabolic.phiMinusQuotient T ψ n A v := rfl

/-- Naturality is on every localized element, for every ambient intertwiner,
with independently quantified carrier universes. -/
theorem phiMinusKernelEquiv_natural
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (mirabolic (n + 1) F.Carrier))
    (f : letI := T.topology; A.representation.IntertwiningMap B.representation)
    (z : letI := T.topology
      Jacquet.Localization.Coinvariants
        (A.representation.comp (plusSubgroup n F.Carrier).subtype)
        (plusProjection (n := n) (F := F.Carrier)).ker (plusKernelTheta ψ n)) :
    letI := T.topology
    phiMinusKernelEquiv T ψ n B (phiMinusKernelMap T ψ n f z) =
      Jacquet.Localization.mapLinear (radical (n + 1) F.Carrier)
        (T.mirabolicTheta ψ n) f (phiMinusKernelEquiv T ψ n A z) := by
  let := T.topology
  exact Submodule.Quotient.induction_on _ z fun _ => rfl

/-- Twisting the entire kernel section action by the actual inverse-half
determinant character gives the actual normalized Phi-minus action. -/
def phiMinusNormalizedKernelEquiv
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (twist (Mirabolic.phiMinusCharacter T n) (phiMinusKernelAction T ψ n A.representation))
      ((Mirabolic.phiMinus T ψ n).obj A).representation :=
  letI := T.topology
  twistEquiv (Mirabolic.phiMinusCharacter T n) (phiMinusKernelEquiv T ψ n A)

@[simp] theorem phiMinusNormalizedKernelEquiv_mk
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
    (v : letI := T.topology; A) :
    letI := T.topology
    phiMinusNormalizedKernelEquiv T ψ n A (Jacquet.Localization.mk _ _ _ v) =
      Mirabolic.phiMinusQuotient T ψ n A v := rfl

/-- The elementary kernel model as a smooth functor on the entire source group. -/
def phiMinusKernelFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) :=
  letI := T.topology
  { obj A := SmoothRep.of (phiMinusKernelAction T ψ n A.representation)
      (phiMinusKernelAction_smooth T ψ n A.representation A.isSmooth)
    map f := SmoothRep.ofHom (phiMinusKernelMap T ψ n (SmoothRep.hom f))
    map_id A := by
      apply smoothRep_hom_ext
      intro z
      exact Submodule.Quotient.induction_on _ z fun _ => rfl
    map_comp f g := by
      apply smoothRep_hom_ext
      intro z
      exact Submodule.Quotient.induction_on _ z fun _ => rfl }

/-- The class-preserving comparison is natural as a smooth-functor isomorphism. -/
def phiMinusKernelIso :
    letI := T.topology
    phiMinusKernelFunctor.{uF, uV} T ψ n ≅ Mirabolic.phiMinusUnnormalized T ψ n :=
  letI := T.topology
  NatIso.ofComponents (fun A => SmoothRep.mkIso (phiMinusKernelEquiv T ψ n A)) (by
    intro A B f
    apply smoothRep_hom_ext
    intro z
    exact phiMinusKernelEquiv_natural T ψ n A B (SmoothRep.hom f) z)

/-- The actual normalized Phi-minus is the kernel model with its full published
inverse-half determinant twist, naturally on all smooth source representations. -/
def phiMinusNormalizedKernelIso :
    letI := T.topology
    phiMinusKernelFunctor.{uF, uV} T ψ n ⋙
        SmoothRep.twistFunctor (Mirabolic.phiMinusCharacter T n)
          (Mirabolic.isOpen_ker_phiMinusCharacter T n) ≅ Mirabolic.phiMinus T ψ n :=
  letI := T.topology
  Functor.isoWhiskerRight (phiMinusKernelIso T ψ n)
    (SmoothRep.twistFunctor (Mirabolic.phiMinusCharacter T n)
      (Mirabolic.isOpen_ker_phiMinusCharacter T n))

end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
