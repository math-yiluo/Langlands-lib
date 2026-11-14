import Langlands.Representation.CuspidalSupport.NormalHeckeTwist
import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeCommutative
import Langlands.Representation.CuspidalSupport.RationalSummandEndCommutativeProof
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement

/-! # Maps to unramified twists separate the vectors of `ind_{⁰G}^G ρ₀`

Let `ρ₀` be a smooth representation of the common norm kernel `⁰G` of `G(F)`, `π` a smooth
representation of `G(F)` and `j : ρ₀ → π|_{⁰G}` an injective `⁰G`-map. A vector `f` of
`Π = ind_{⁰G}^{G} ρ₀` killed by every map `Π → π ⊗ ω`, `ω` an unramified character, is zero.
Indeed, the map `Π → π ⊗ ω` corresponding to `j` sends `f` to
`∑_{x ∈ ⁰G \ G} ω(x)⁻¹ π(x⁻¹) j(f(x))`, and the characters of `G(F)/⁰G` are linearly independent and separate its points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandTwistSeparationTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalSummandTwistSeparationTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- Maps to the unramified twists of `π` separate the vectors of `ind_{⁰G}^{G} ρ₀` when
`ρ₀` embeds in `π|_{⁰G}`: a vector killed by every map `ind_{⁰G}^{G} ρ₀ → π ⊗ ω` is zero. -/
theorem rationalNormKernelSummandInduction_eq_zero_of_forall_twist
    (ρ₀ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (j : ρ₀.representation.IntertwiningMap
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    (hj : Function.Injective j) (f : rationalNormKernelSummandInduction G ρ₀)
    (hf : ∀ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
      (U : rationalNormKernelSummandInduction G ρ₀ ⟶ rationalUnramifiedTwist G ω π),
        SmoothRep.hom U f = 0) :
    f = 0 := by
  let H := rationalCommonNormKernel G
  have hH : IsOpen (H : Set (GroupScheme.rationalPoints G)) := isOpen_rationalCommonNormKernel G
  have : DiscreteTopology (GroupScheme.rationalPoints G ⧸ H) := QuotientGroup.discreteTopology hH
  let t : Induction.LeftQuotient H → π :=
    Induction.cosetTerm H π.representation ρ₀.representation j f
  have ht : t = 0 := by
    refine NormalHecke.eq_zero_of_forall_character
      (rationalNormKernelQuotient_exists_character_ne_one G) (NormalHecke.leftQuotientEquiv H)
      (NormalHecke.leftQuotientEquiv H).injective t
      (Induction.hasFiniteSupport_cosetTerm H hH π.representation _ j f) fun ω₀ => ?_
    let χc : (GroupScheme.rationalPoints G ⧸ H) →ₜ* ℂˣ :=
      { toMonoidHom := ω₀⁻¹
        continuous_toFun := continuous_of_discreteTopology }
    let ω := quotientCharacterPullback (fun χ => (rationalNormCharacters G χ).toMul) χc
    have hω := isOpen_rationalUnramifiedCharacter_ker G ω
    have hωH : H ≤ ω.val.toMonoidHom.ker := ω.2
    let U : rationalNormKernelSummandInduction G ρ₀ ⟶ rationalUnramifiedTwist G ω π :=
      (NormalHecke.inducedHomEquiv H ρ₀ hH (π.twist ω.val.toMonoidHom hω)).symm
        ((NormalHecke.twistRestrictEquiv ρ₀ ω.val.toMonoidHom hω hωH π).symm j)
    have h1 := hf ω U
    change ∑ᶠ q, Induction.cosetTerm H (π.twist ω.val.toMonoidHom hω).representation
      ρ₀.representation ((NormalHecke.twistRestrictEquiv ρ₀ ω.val.toMonoidHom hω hωH π).symm j)
      f q = 0 at h1
    refine Eq.trans (finsum_congr fun q => ?_) h1
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hωx : ((ω.val.toMonoidHom x⁻¹ : ℂˣ) : ℂ) =
        ((ω₀ (x : GroupScheme.rationalPoints G ⧸ H) : ℂˣ) : ℂ) := by
      change (((ω₀⁻¹) ((x⁻¹ : GroupScheme.rationalPoints G) :
        GroupScheme.rationalPoints G ⧸ H) : ℂˣ) : ℂ) = _
      rw [MonoidHom.inv_apply, QuotientGroup.mk_inv, map_inv, inv_inv]
    change ((ω₀ (x : GroupScheme.rationalPoints G ⧸ H) : ℂˣ) : ℂ) •
        π.representation x⁻¹ (j (Induction.eval H ρ₀.representation f.1 x)) =
      ((ω.val.toMonoidHom x⁻¹ : ℂˣ) : ℂ) •
        π.representation x⁻¹ (j (Induction.eval H ρ₀.representation f.1 x))
    rw [hωx]
  refine Induction.compactFunctions_ext H _ fun x => ?_
  have h1 := congrFun ht (Induction.quotientMap H x)
  change π.representation x⁻¹ (j (Induction.eval H ρ₀.representation f.1 x)) = 0 at h1
  have h2 : j (Induction.eval H ρ₀.representation f.1 x) = 0 := by
    rw [← Representation.self_inv_apply π.representation x (j _), h1, map_zero]
  apply hj
  exact h2.trans (map_zero j).symm

end Langlands.CuspidalSupport
