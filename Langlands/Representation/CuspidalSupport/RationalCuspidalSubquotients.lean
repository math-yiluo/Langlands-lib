import Langlands.Representation.CuspidalSupport.RationalCuspidalCategory
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Actual cuspidality passes to arbitrary smooth subquotients -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] {I : Type uI}
  (P M U : I → Subgroup G)
  (h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k))
  (hU : ∀ k, IsClosed (U k : Set G))

/-- Cuspidality for the actual Jacquet test family is closed under all actual
smooth subquotients, without a representation finiteness condition. -/
def CuspidalSubquotientClosure : Prop :=
  ∀ A D : SmoothRep.{0, uG, uV} ℂ G,
    IsCuspidalFor P M U h hU A → SmoothRep.IsSubquotient D A →
      IsCuspidalFor P M U h hU D

/-- Compact exhaustion of the tested radicals gives actual cuspidality
closure under arbitrary smooth subquotients. -/
theorem cuspidalSubquotientClosure_of_compactExhaustion
    (hUc : ∀ k, Jacquet.Localization.IsLimitOfCompactSubgroups (U k)) :
    CuspidalSubquotientClosure.{uG, uV} P M U h hU := by
  intro A D hA hDA k
  obtain ⟨C, f, q, hf, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  let R := jacquetFunctor (h k) (hU k)
  have hf' : Function.Injective (SmoothRep.hom (R.map f)) :=
    Jacquet.Localization.map_injective_of_smooth (U k) (hUc k) 1
      (IsLocallyConstant.of_constant _ fun _ _ => by simp) (M k)
      (h k).levi_le_normalizer
      (Jacquet.Localization.isInvariant_one _ _ (h k).levi_le_normalizer)
      (SmoothRep.hom f) hf A.isSmooth
  have hq' : Function.Surjective (SmoothRep.hom (R.map q)) :=
    Jacquet.Localization.map_surjective (U k) 1 (M k)
      (h k).levi_le_normalizer
      (Jacquet.Localization.isInvariant_one _ _ (h k).levi_le_normalizer)
      (SmoothRep.hom q) hq
  have hC : Subsingleton (R.obj C) :=
    ⟨fun x y => hf' (@Subsingleton.elim _ (hA k) _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hq' x
  obtain ⟨y', rfl⟩ := hq' y
  exact congrArg (SmoothRep.hom (R.map q)) (@Subsingleton.elim _ hC x' y')

end Langlands.Aubert.General

namespace Langlands.CuspidalSupport

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalCuspidalSubquotientsTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hStandard : StandardCocharacterStatement.{uF}) (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (h : ∀ J, IsSemidirectDecomposition
    (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))

include hStandard hG hi hν

omit [LocallyOfFiniteType G.X.hom] in
/-- For actual proper standard tests, the all-cuspidal-subquotient property
is equivalent to ordinary cuspidality. Compact exhaustion is discharged by
the published dynamic-unipotent containment theorem. -/
theorem rationalAllCuspidalSubquotientProperty_iff_isCuspidal
    (A : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    rationalAllCuspidalSubquotientProperty G i ν h hU A ↔
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A := by
  constructor
  · intro hA
    exact hA A (SmoothRep.IsSubrepresentation.isSubquotient
      ⟨𝟙 _, Function.injective_id⟩)
  · intro hA D hDA
    have := hG.isAffineHom
    have hcompact (J : Finset (SimpleRoot i ν)) :
        Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J) :=
      standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J
    exact cuspidalSubquotientClosure_of_compactExhaustion
      (fun J : {J : Finset (SimpleRoot i ν) // J ≠ Finset.univ} => parabolic i ν J.val)
      (fun J => levi i ν J.val) (fun J => unipotent i ν J.val)
      (fun J => h J.val) (fun J => hU J.val)
      (fun J => hcompact J.val) A D hA hDA

end Langlands.CuspidalSupport
