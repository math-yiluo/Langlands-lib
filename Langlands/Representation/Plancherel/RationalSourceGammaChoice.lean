import Langlands.Representation.Plancherel.RationalDynamicSourceHaar
import Langlands.Representation.Plancherel.SourceGammaTransport
import Langlands.GroupScheme.Dynamic.PositivePowers
import Langlands.GroupScheme.Dynamic.CentralKernelIndependence
import Langlands.GroupScheme.Dynamic.OppositeBaseChange

/-! # Original subgroup Haar and gamma under changes of cocharacter description -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz QuotientIntegration
open BruhatTits.DynamicUnipotentContainment

section Algebraic

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- Taking the opposite commutes with every integral power of the parameter. -/
theorem oppositeCocharacter_precomp_power (n : ℤ) :
    oppositeCocharacter
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ χ) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫
        oppositeCocharacter χ := by
  apply hom_ext_points
  intro T t
  unfold oppositeCocharacter
  rw [Grp.comp_hom_hom, ← Category.assoc, Dynamic.comp_powerHom,
    Grp.comp_hom_hom, ← Category.assoc, Dynamic.comp_powerHom,
    Grp.comp_hom_hom, ← Category.assoc, Dynamic.comp_powerHom,
    Grp.comp_hom_hom, ← Category.assoc, Dynamic.comp_powerHom,
    ← zpow_mul, ← zpow_mul, mul_comm]

end Algebraic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance sourceGammaChoicePointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance sourceGammaChoicePointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance sourceGammaChoicePointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceGammaChoiceFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceGammaChoicePointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
local instance sourceGammaChoicePointLocallyCompact :
    LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G

variable (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "A" => RationalPoint F G.X
local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "Pχ" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "Pψ" => SubgroupFunctor.carrier (Dynamic.parabolic ψ) X₀
local notation "Vχ" => unipotentPoints (oppositeCocharacter χ)
local notation "Vψ" => unipotentPoints (oppositeCocharacter ψ)

/-- The identity on original rational points restricts to the parabolics
of two descriptions of the same dynamic subgroup. -/
def parabolicSourceChoiceEquiv (hpar : Dynamic.parabolic χ = Dynamic.parabolic ψ) :
    Pχ ≃ₜ* Pψ :=
  subgroupContinuousMulEquiv (ContinuousMulEquiv.refl A) Pχ Pψ
    (fun x => by change x ∈ Pψ ↔ x ∈ Pχ; rw [hpar])

/-- The identity on original rational points restricts to the opposite
radicals of two descriptions of the same dynamic subgroup. -/
def oppositeRadicalSourceChoiceEquiv
    (hopp : Dynamic.unipotent (oppositeCocharacter χ) =
      Dynamic.unipotent (oppositeCocharacter ψ)) : Vχ ≃ₜ* Vψ :=
  subgroupContinuousMulEquiv (ContinuousMulEquiv.refl A) Vχ Vψ
    (fun x => by
      change x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter ψ)) X₀ ↔
        x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter χ)) X₀
      rw [hopp])

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Identical subgroup descriptions carry the original parabolic Haar
measure to the original measure with no change of scale. -/
theorem measurePreserving_parabolicSourceChoiceEquiv
    (hpar : Dynamic.parabolic χ = Dynamic.parabolic ψ) :
    MeasurePreserving (parabolicSourceChoiceEquiv χ ψ hpar)
      (parabolicHaar χ K hK) (parabolicHaar ψ K hK) :=
  measurePreserving_sourceSubgroupHaar (ContinuousMulEquiv.refl A) K K hK hK
    Pχ Pψ (isClosed_dynamic_parabolic F G χ) (isClosed_dynamic_parabolic F G ψ)
    (fun x => by change x ∈ Pψ ↔ x ∈ Pχ; rw [hpar]) (fun _ => Iff.rfl)

/-- Identical opposite-radical descriptions preserve their original Haar
measures at the same common compact open. -/
theorem measurePreserving_oppositeRadicalSourceChoiceEquiv
    (hopp : Dynamic.unipotent (oppositeCocharacter χ) =
      Dynamic.unipotent (oppositeCocharacter ψ)) :
    MeasurePreserving (oppositeRadicalSourceChoiceEquiv χ ψ hopp)
      (radicalHaar (oppositeCocharacter χ) K hK)
      (radicalHaar (oppositeCocharacter ψ) K hK) :=
  measurePreserving_sourceSubgroupHaar (ContinuousMulEquiv.refl A) K K hK hK
    Vχ Vψ (isClosed_unipotentPoints (oppositeCocharacter χ))
    (isClosed_unipotentPoints (oppositeCocharacter ψ))
    (fun x => by
      change x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter ψ)) X₀ ↔
        x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter χ)) X₀
      rw [hopp]) (fun _ => Iff.rfl)

/-- The actual source gamma depends only on its two dynamic subgroups
and their original common-compact Haar normalization. -/
theorem gamma_eq_of_dynamic_subgroups_eq
    (hpar : Dynamic.parabolic χ = Dynamic.parabolic ψ)
    (hopp : Dynamic.unipotent (oppositeCocharacter χ) =
      Dynamic.unipotent (oppositeCocharacter ψ)) :
    gamma χ K hK = gamma ψ K hK := by
  symm
  exact compactNormalizedSourceGamma_eq_of_transport (ContinuousMulEquiv.refl A)
    K K hK hK (isClosed_dynamic_parabolic F G χ)
    (isClosed_unipotentPoints (oppositeCocharacter χ))
    (isClosed_dynamic_parabolic F G ψ)
    (isClosed_unipotentPoints (oppositeCocharacter ψ))
    (fun x => by change x ∈ Pψ ↔ x ∈ Pχ; rw [hpar])
    (fun x => by
      change x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter ψ)) X₀ ↔
        x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter χ)) X₀
      rw [hopp]) (fun _ => Iff.rfl)

/-- Positive integral powers of a cocharacter preserve the original
common-compact source gamma. -/
theorem gamma_precomp_power {n : ℤ} (hn : 0 < n) :
    gamma (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ χ)
        K hK = gamma χ K hK := by
  apply gamma_eq_of_dynamic_subgroups_eq _ χ K hK
    (Dynamic.parabolic_precomp_power χ hn)
  rw [oppositeCocharacter_precomp_power]
  exact Dynamic.unipotent_precomp_power (oppositeCocharacter χ) hn

/-- Two lifts with the same projection through a central full kernel
give the same gamma in the original group. -/
theorem gamma_eq_of_comp_eq_of_central_kernel
    {H : GroupScheme (Spec (CommRingCat.of F))} (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (hχψ : χ ≫ q = ψ ≫ q) :
    gamma χ K hK = gamma ψ K hK := by
  apply gamma_eq_of_dynamic_subgroups_eq χ ψ K hK
    (Dynamic.parabolic_eq_of_comp_eq_of_central_kernel q hq χ ψ hχψ)
  apply Dynamic.unipotent_eq_of_comp_eq_of_central_kernel q hq
  simpa only [oppositeCocharacter, Category.assoc] using
    congrArg (fun f =>
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ f) hχψ

/-- Positive powers may agree only after projection through a central
kernel: the two original source gammas still agree at the common compact. -/
theorem gamma_eq_of_positive_powers_comp_eq_of_central_kernel
    {H : GroupScheme (Spec (CommRingCat.of F))} (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) {m n : ℤ} (hm : 0 < m) (hn : 0 < n)
    (hχψ : (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) m) ≫ χ) ≫ q =
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ ψ) ≫ q) :
    gamma χ K hK = gamma ψ K hK := by
  calc
    gamma χ K hK =
        gamma (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) m) ≫ χ)
          K hK := (gamma_precomp_power χ K hK hm).symm
    _ = gamma (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ ψ)
          K hK := gamma_eq_of_comp_eq_of_central_kernel _ _ K hK q hq hχψ
    _ = gamma ψ K hK := gamma_precomp_power ψ K hK hn

end Langlands.Plancherel.RationalDynamicSource
