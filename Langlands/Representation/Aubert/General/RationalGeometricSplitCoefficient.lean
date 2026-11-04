import Langlands.Representation.Aubert.General.RationalGeometricSplitStages
import Langlands.Representation.Aubert.General.GeometricCoefficientAction
import Langlands.Representation.Induction.SplitKernelCovariance

/-! # Actual split-stage geometric coefficient action -/

noncomputable section

universe u uA uB uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section SectionComparison

variable {A : Type uA} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {B : Type uB} [Group B]
  (r : A →* B) (s : B →* A) (hrs : ∀ b, r (s b) = b)
  (P H : Subgroup A) (hker : r.ker ≤ P) (hHP : H ≤ P)
  (hsH : ∀ l : Subgroup.comap s P, s (l : B) ∈ H)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "rP" => Induction.splitStagesRetraction r s hrs P hker
local notation "sP" => MonoidHom.subgroupComap s P
local notation "HP" => Subgroup.subgroupOf H P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "hSI" => (fun l : Subgroup.comap s P => hsH l)
local notation "N" => Subgroup.comap (Subgroup.subtype H) r.ker

/-- The published class-preserving quotient equivalence also retains the section action. -/
private def splitStagesSectionCoefficientEquiv (σ : Representation ℂ H V) :
    (Induction.splitKernelCoefficientAction rP sP HP hSI (σ.comp φ)).Equiv
      ((σ.toCoinvariants N).comp (Induction.splitStagesInducingSection s P H hsH)) where
  toLinearEquiv := Induction.splitStagesCoefficientEquiv r s hrs P H hker hHP σ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    rfl

end SectionComparison

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]

local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (parabolic i ν I)
local notation "N" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker dI.projection)
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (levi i ν I)
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection (levi i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  (parabolic i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  dJ (n : RationalPoint k G.X)
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "hker" => geometricSplit_ker_le i ν I J dI n
local notation "hHP" =>
  stabilizer_le_geometricSplitIntermediate i ν I J dI n hStandard hG hi hν hN
local notation "rP" => Induction.splitStagesRetraction dI.projection s
  (fun m => dI.projection_levi m) P hker
local notation "sP" => MonoidHom.subgroupComap s P
local notation "HP" => Subgroup.subgroupOf H P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "hSH" => geometricSplit_section_mem i ν I J dI n
local notation "hSI" => (fun l : Subgroup.comap s P => hSH l)
local notation "eK" => geometricSplitQuotientEquiv i ν I J dI n
local notation "j" => MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rP)) HP

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The nested split-stage quotient with its action by the literal target intersection. -/
abbrev geometricSplitCoefficientAction (σ : Representation ℂ (levi i ν J) V) :
    Representation ℂ K (Representation.Coinvariants (((σ.comp f).comp φ).comp j)) :=
  (Induction.splitKernelCoefficientAction rP sP HP hSI ((σ.comp f).comp φ)).comp
    (MulEquiv.toMonoidHom (MulEquiv.symm eK))

@[simp] theorem geometricSplitCoefficientAction_mk
    (σ : Representation ℂ (levi i ν J) V) (l : K) (v : V) :
    geometricSplitCoefficientAction i ν hStandard hG hi hν hN I J dI dJ n σ l
        (Representation.Coinvariants.mk (((σ.comp f).comp φ).comp j) v) =
      Representation.Coinvariants.mk (((σ.comp f).comp φ).comp j)
        (σ (f (geometricCoefficientSection (parabolic i ν I) (levi i ν I)
          (unipotent i ν I) (parabolic i ν J) dI (n : RationalPoint k G.X) l)) v) := rfl

variable
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "p" => geometricCoefficientLeviMap
  (levi i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget

/-- Remove the nested subtypes, retaining the action of the whole target parabolic. -/
def geometricSplitCoefficientEquiv (σ : Representation ℂ (levi i ν J) V) :
    (geometricSplitCoefficientAction i ν hStandard hG hi hν hN I J dI dJ n σ).Equiv
      ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p) :=
  (show (geometricSplitCoefficientAction i ν hStandard hG hi hν hN I J dI dJ n σ).Equiv
      ((Representation.toCoinvariants (σ.comp f) N).comp
        (geometricCoefficientSection (parabolic i ν I) (levi i ν I)
          (unipotent i ν I) (parabolic i ν J) dI (n : RationalPoint k G.X))) from
    { toLinearEquiv :=
        (splitStagesSectionCoefficientEquiv dI.projection s
          (fun m => dI.projection_levi m) P H hker hHP hSH (σ.comp f)).toLinearEquiv
      isIntertwining' l :=
        (splitStagesSectionCoefficientEquiv dI.projection s
          (fun m => dI.projection_levi m) P H hker hHP hSH (σ.comp f)).isIntertwining'
            (MulEquiv.symm eK l) }).trans
    (geometricCoefficientActionEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ)

@[simp] theorem geometricSplitCoefficientEquiv_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ
        (Representation.Coinvariants.mk (((σ.comp f).comp φ).comp j) v) =
      Jacquet.mk σ S v :=
  geometricCoefficientActionEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ v

@[simp] theorem geometricSplitCoefficientEquiv_symm_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ).symm (Jacquet.mk σ S v) =
      Representation.Coinvariants.mk (((σ.comp f).comp φ).comp j) v := by
  exact (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ).toLinearEquiv.symm_apply_eq.mpr
      (geometricSplitCoefficientEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ v).symm

end RationalPointFamily
end Langlands.Aubert.General
