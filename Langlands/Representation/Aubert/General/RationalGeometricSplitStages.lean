import Langlands.Representation.Aubert.General.RationalGeometricStabilizerProjection
import Langlands.Representation.Induction.SplitStagesRetraction

/-! # Actual rational geometric subgroups for split induction in stages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

private theorem ker_le_subgroup_comap
    {A B : Type*} [Group A] [Group B] (r : A →* B) (K : Subgroup B) :
    r.ker ≤ K.comap r := by
  intro a ha
  change r a ∈ K
  rw [show r a = 1 from ha]
  exact K.one_mem

private theorem comap_comap_section
    {A B : Type*} [Group A] [Group B] (r : A →* B) (s : B →* A)
    (hrs : ∀ b, r (s b) = b) (K : Subgroup B) :
    (K.comap r).comap s = K := by
  ext b
  change r (s b) ∈ K ↔ b ∈ K
  rw [hrs]

private theorem section_mem_inf_subgroup
    {A : Type*} [Group A] (Q L F : Subgroup A) (hL : L ≤ Q)
    (r : Q →* L) (hr : ∀ l, r (Subgroup.inclusion hL l) = l)
    (l : (((L ⊓ F).subgroupOf L).comap r).comap (Subgroup.inclusion hL)) :
    Subgroup.inclusion hL (l : L) ∈ (Q ⊓ F).subgroupOf Q := by
  have hk := l.property
  change r (Subgroup.inclusion hL (l : L)) ∈ (L ⊓ F).subgroupOf L at hk
  rw [hr] at hk
  exact ⟨hL l.val.property, hk.2⟩

private theorem le_comap_of_restriction
    {A B : Type*} [Group A] [Group B] (r : A →* B)
    (H : Subgroup A) (K : Subgroup B) (g : H →* K)
    (hg : ∀ h : H, (g h : B) = r h) :
    H ≤ K.comap r := by
  intro h hh
  change r h ∈ K
  exact (hg ⟨h, hh⟩) ▸ (g ⟨h, hh⟩).property

private theorem restriction_eq_of_val
    {A B : Type*} [Group A] [Group B] (r : A →* B)
    (P H : Subgroup A) (K : Subgroup B) (hHP : H ≤ P)
    (f : P →* K) (g : H →* K)
    (hf : ∀ p : P, (f p : B) = r p)
    (hg : ∀ h : H, (g h : B) = r h) (h : H) :
    f (Subgroup.inclusion hHP h) = g h :=
  Subtype.ext ((hf _).trans (hg _).symm)

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

local notation "Q" => parabolic i ν I
local notation "L" => levi i ν I
local notation "H" =>
  Subgroup.subgroupOf (geometricTargetIntersection Q (parabolic i ν J)
    (n : RationalPoint k G.X)) Q
local notation "K" =>
  Subgroup.subgroupOf (geometricTargetIntersection L (parabolic i ν J)
    (n : RationalPoint k G.X)) L
local notation "s" => Subgroup.inclusion d.levi_le

/-- The actual intermediate subgroup is the inverse image of the target
intersection under the original target Levi projection. -/
def geometricSplitIntermediate : Subgroup Q :=
  (K).comap d.projection

local notation "P" => geometricSplitIntermediate i ν I J d n

/-- The intermediate subgroup contains the whole original projection kernel. -/
theorem geometricSplit_ker_le :
    d.projection.ker ≤ P :=
  ker_le_subgroup_comap d.projection K

/-- Restriction to the actual Levi section recovers the literal target
intersection, with its original subgroup restriction. -/
theorem geometricSplit_comap_section :
    (P).comap s = K :=
  comap_comap_section d.projection s (fun m => d.projection_levi m) K

/-- Every point of the split quotient has its actual Levi section in the
original orbit stabilizer. -/
theorem geometricSplit_section_mem (l : (P).comap s) :
    s (l : L) ∈ H :=
  section_mem_inf_subgroup Q L
    ((parabolic i ν J).map
      (MulAut.conj (n : RationalPoint k G.X) : RationalPoint k G.X →* RationalPoint k G.X))
    d.levi_le d.projection (fun m => d.projection_levi m) l

/-- The split quotient and the literal target intersection have the same
original Levi point. -/
def geometricSplitQuotientEquiv : (P).comap s ≃* K :=
  MulEquiv.subgroupCongr (geometricSplit_comap_section i ν I J d n)

@[simp] theorem geometricSplitQuotientEquiv_apply (l : (P).comap s) :
    (geometricSplitQuotientEquiv i ν I J d n l : L) = (l : L) := rfl

@[simp] theorem geometricSplitQuotientEquiv_symm_apply (l : K) :
    ((geometricSplitQuotientEquiv i ν I J d n).symm l : L) = (l : L) := rfl

/-- The published split-stages retraction, with its codomain identified with
the actual target intersection. -/
def geometricSplitRetraction : P →* K :=
  (geometricSplitQuotientEquiv i ν I J d n).toMonoidHom.comp
    (Induction.splitStagesRetraction d.projection s
      (fun m => d.projection_levi m) P (geometricSplit_ker_le i ν I J d n))

@[simp] theorem geometricSplitRetraction_apply (p : P) :
    (geometricSplitRetraction i ν I J d n p : L) = d.projection p.val := rfl

section Stabilizer

variable (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)

include hStandard hG hi hν hN

/-- The actual orbit stabilizer lies in the intermediate subgroup. -/
theorem stabilizer_le_geometricSplitIntermediate :
    H ≤ P :=
  le_comap_of_restriction d.projection H K
    (stabilizerProjection i ν hStandard hG hi hν hN I J d n) (fun _ => rfl)

/-- Restricting the split-stages retraction to the orbit stabilizer gives
exactly the original stabilizer projection. -/
theorem geometricSplitRetraction_stabilizer (p : H) :
    geometricSplitRetraction i ν I J d n
        (Subgroup.inclusion
          (stabilizer_le_geometricSplitIntermediate i ν I J d n hStandard hG hi hν hN) p) =
      stabilizerProjection i ν hStandard hG hi hν hN I J d n p :=
  restriction_eq_of_val d.projection P H K
    (stabilizer_le_geometricSplitIntermediate i ν I J d n hStandard hG hi hν hN)
    (geometricSplitRetraction i ν I J d n)
    (stabilizerProjection i ν hStandard hG hi hν hN I J d n)
    (geometricSplitRetraction_apply i ν I J d n)
    (stabilizerProjection_apply i ν hStandard hG hi hν hN I J d n) p

end Stabilizer

section Topology

variable [TopologicalSpace (RationalPoint k G.X)]

/-- The actual Levi section is continuous for the induced subgroup topologies. -/
theorem continuous_geometricSplitSection :
    Continuous s :=
  continuous_subtype_val.subtype_mk _

/-- The literal split quotient identification preserves the induced topology. -/
def geometricSplitQuotientContinuousEquiv : (P).comap s ≃ₜ* K where
  toMulEquiv := geometricSplitQuotientEquiv i ν I J d n
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The restricted split-stages retraction is continuous whenever the
original ambient Levi projection is continuous. -/
theorem continuous_geometricSplitRetraction (hproj : Continuous d.projection) :
    Continuous (geometricSplitRetraction i ν I J d n) :=
  (hproj.comp continuous_subtype_val).subtype_mk _

variable (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)

/-- The actual stabilizer projection inherits continuity from the original
target projection, without an extra continuity premise for this restriction. -/
theorem continuous_stabilizerProjection (hproj : Continuous d.projection) :
    Continuous (stabilizerProjection i ν hStandard hG hi hν hN I J d n) :=
  (hproj.comp continuous_subtype_val).subtype_mk _

/-- The inducing-side radical projection inherits continuity from the original
inducing Levi projection. -/
theorem continuous_sourceRadicalProjection
    (dJ : IsSemidirectDecomposition
      (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (hproj : Continuous dJ.projection) :
    Continuous (sourceRadicalProjection i ν hStandard hG hi hν hN I J dJ n) :=
  (hproj.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalGroup (RationalPoint k G.X)]

/-- The actual orbit stabilizer is closed in the target parabolic. -/
theorem isClosed_geometricStabilizer
    (hPI : IsClosed (Q : Set (RationalPoint k G.X)))
    (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X))) :
    IsClosed (H : Set Q) :=
  (isClosed_geometricTargetIntersection Q (parabolic i ν J) hPI hPJ
    (n : RationalPoint k G.X)).preimage continuous_subtype_val

/-- The literal target intersection is closed in the original target Levi. -/
theorem isClosed_geometricSplitTarget
    (hMI : IsClosed (L : Set (RationalPoint k G.X)))
    (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X))) :
    IsClosed (K : Set L) :=
  (isClosed_geometricTargetIntersection L (parabolic i ν J) hMI hPJ
    (n : RationalPoint k G.X)).preimage continuous_subtype_val

/-- The intermediate subgroup is closed as the continuous inverse image of
the literal target intersection. -/
theorem isClosed_geometricSplitIntermediate
    (hMI : IsClosed (L : Set (RationalPoint k G.X)))
    (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
    (hproj : Continuous d.projection) :
    IsClosed (P : Set Q) :=
  (isClosed_geometricSplitTarget i ν I J n hMI hPJ).preimage hproj

end Topology

end Langlands.Aubert.General.RationalPointFamily
