import Langlands.Global.AdelicIntrinsicLeviIwasawaHeight
import Langlands.Global.AdelicWeilPointTransport
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport

/-! # Intrinsic standard families and compatible compacts of actual standard Levis -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

local notation "M" => fam.M Q
local notation "j" => (fam.l Q ≫ fam.p Q)
local notation "tL" => fam.torus Q
set_option quotPrecheck false in
local notation "hM" => (fam.isCompatible Q).levi.isConnectedReductive

local instance : IsAffineHom (M).X.hom := (hM).isAffineHom

omit [NumberField F] in
theorem intrinsicStandardRootData :
    IsMaximalSplitTorus tL ∧ IsGenericCocharacter tL fam.ν ∧ simpleRelativeRoots tL fam.ν = Q.val ∧
      ∀ J : Set (characterLattice fam.T), J ⊆ Q.val →
        standardParabolic tL fam.ν J = (standardParabolic fam.i fam.ν J).comap j ∧
        standardLevi tL fam.ν J = (standardLevi fam.i fam.ν J).comap j ∧
        standardUnipotent tL fam.ν J = (standardUnipotent fam.i fam.ν J).comap j := by
  have hj : IsClosedSubgroup j :=
    (fam.isCompatible Q).levi.isClosedSubgroup.comp (fam.isCompatible Q).parabolic.isClosedSubgroup
  let : Mono (j).hom.hom.left := hj.mono
  let hrep : (standardLevi fam.i fam.ν Q.val).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible Q).levi_eq⟩
  let iL := standardLeviTorusFactor fam.i fam.ν Q.val hrep
  have ht : iL = tL := hrep.hom_ext ((standardLeviTorusFactor_comp _ _ _ _).trans (fam.torus_comp Q).symm)
  have hsplit := fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor fam.i fam.ν Q.val hrep hj
  obtain ⟨hr, hνL, hs⟩ :=
    standardLeviStandardFamilies dynamicLie standardCocharacter F G fam.connectedReductive fam.T
      fam.i fam.maximalSplit fam.ν fam.generic Q.val Q.property M (hM) j hrep hj
  rw [← ht]
  exact ⟨hsplit, hνL, hr, hs⟩

/-- The standard family for the ambient maximal split torus viewed inside the outer Levi. -/
def intrinsicStandardFamily : StandardParabolicFamily F M :=
  ofMaximalSplitTorus (hM) tL (fam.intrinsicStandardRootData Q).1 fam.ν
    (fam.intrinsicStandardRootData Q).2.1

local notation "lower" => fam.intrinsicStandardFamily Q
local notation "Idx" => StandardIndex F G fam.i fam.ν
set_option quotPrecheck false in
local notation "IdxL" => StandardIndex F M (lower).i (lower).ν

/-- A parabolic contained in the outer parabolic gives a standard index in its Levi. -/
def intrinsicStandardIndex (I : Idx) (hIQ : I ≤ Q) : IdxL :=
  ⟨I.val, by
    change I.val ⊆ simpleRelativeRoots tL fam.ν
    rwa [(fam.intrinsicStandardRootData Q).2.2.1]⟩

local notation "Iₗ(" I ", " h ")" => fam.intrinsicStandardIndex Q I h

omit [NumberField F] in
private theorem intrinsicLeviRep (I : Idx) :
    (standardLevi fam.i fam.ν I.val).IsRepresentedBy (fam.l I ≫ fam.p I) := by
  let : Mono (fam.l I ≫ fam.p I).hom.hom.left :=
    ((fam.isCompatible I).levi.isClosedSubgroup.comp (fam.isCompatible I).parabolic.isClosedSubgroup).mono
  exact ⟨Over.mono_of_mono_left _, (fam.isCompatible I).levi_eq⟩

/-- The intrinsic Levi of a nested standard parabolic is isomorphic over the ambient group
to the corresponding ambient standard Levi. -/
def intrinsicNestedLeviIso (I : Idx) (hIQ : I ≤ Q) : (lower).M (Iₗ(I, hIQ)) ≅ fam.M I := by
  let low := lower
  let L := Iₗ(I, hIQ)
  let inc := low.l L ≫ low.p L
  let : Mono inc.hom.hom.left :=
    ((low.isCompatible L).levi.isClosedSubgroup.comp (low.isCompatible L).parabolic.isClosedSubgroup).mono
  let hRep : (standardLevi tL fam.ν I.val).IsRepresentedBy inc :=
    ⟨Over.mono_of_mono_left _, (low.isCompatible L).levi_eq⟩
  have hle : standardLevi fam.i fam.ν I.val ≤ SubgroupFunctor.range j := by
    rw [(fam.intrinsicLeviRep Q).2,
      ← (Standard.isRepresentedBy_leviHom fam.i fam.ν Q.val).2]
    exact StandardLeviNested.standardLevi_le_range_leviHom fam.connectedReductive fam.i
      fam.maximalSplit fam.ν fam.generic Q.property hIQ
  exact StandardLeviNested.nestedIso (fam.intrinsicLeviRep Q).1
    (((fam.intrinsicStandardRootData Q).2.2.2 I.val hIQ).2.1).symm hRep hle
    (fam.intrinsicLeviRep I)

omit [NumberField F] in
theorem intrinsicNestedLeviIso_hom_comp (I : Idx) (hIQ : I ≤ Q) :
    (fam.intrinsicNestedLeviIso Q I hIQ).hom ≫ fam.l I ≫ fam.p I =
      (((lower).l (Iₗ(I, hIQ)) ≫ (lower).p (Iₗ(I, hIQ))) ≫ j) := by
  unfold intrinsicNestedLeviIso
  exact StandardLeviNested.nestedIso_hom_comp _ _ _ _ _

variable {K : Subgroup (AdelicGroupPoints F G)}

set_option quotPrecheck false in
local notation "KM" => K.comap (map F M G j).toMonoidHom

/-- The inherited compact is admissible for the intrinsic family, with maximal inverse
images on all its standard Levis. A proper Levi has strictly fewer simple roots. -/
def IntrinsicStandardCompactStatement : Prop :=
  IsIwasawaCompact (fam.p fam.bot) K →
  (∀ I, IsMaximalCompactSubgroup F (fam.M I)
    (K.comap (map F (fam.M I) G (fam.l I ≫ fam.p I)).toMonoidHom)) →
  IsPositiveTorusCompatible F G fam.T fam.i fam.ν fam.T (𝟙 fam.T) K →
  IsIwasawaCompact ((lower).p (lower).bot) KM ∧
  IsPositiveTorusCompatible F M (lower).T (lower).i (lower).ν (lower).T (𝟙 (lower).T) KM ∧
  (∀ I : IdxL, IsMaximalCompactSubgroup F ((lower).M I)
    ((KM).comap (map F ((lower).M I) M ((lower).l I ≫ (lower).p I)).toMonoidHom)) ∧
  (Q < fam.top → Set.ncard (simpleRelativeRoots (lower).i (lower).ν) <
    Set.ncard (simpleRelativeRoots fam.i fam.ν))

set_option maxHeartbeats 2400000 in
theorem intrinsicStandardCompact : fam.IntrinsicStandardCompactStatement Q (K := K) := by
  intro hK hmax htorus
  refine ⟨fam.intrinsicLevi_isIwasawaCompact Q hK (hmax Q),
    fam.intrinsicLevi_isPositiveTorusCompatible Q htorus, ?_, ?_⟩
  · intro A
    let low := lower
    have hr : simpleRelativeRoots low.i low.ν = Q.val := (fam.intrinsicStandardRootData Q).2.2.1
    have hAQ : A.val ⊆ Q.val := hr ▸ A.property
    let I : Idx := ⟨A.val, hAQ.trans Q.property⟩
    have hIQ : I ≤ Q := hAQ
    have he : Iₗ(I, hIQ) = A := Subtype.ext rfl
    rw [← he]
    let IL := Iₗ(I, hIQ)
    let e := adelicPointsIso F (fam.intrinsicNestedLeviIso Q I hIQ)
    let KI := K.comap (map F (fam.M I) G (fam.l I ≫ fam.p I)).toMonoidHom
    have hmap : KI.comap e.toMonoidHom =
        (KM).comap (map F (low.M IL) M (low.l IL ≫ low.p IL)).toMonoidHom := by
      ext x
      change map F (fam.M I) G (fam.l I ≫ fam.p I) (e x) ∈ K ↔
        map F M G j (map F (low.M IL) M (low.l IL ≫ low.p IL) x) ∈ K
      rw [show e x = map F (low.M IL) (fam.M I) (fam.intrinsicNestedLeviIso Q I hIQ).hom x from rfl,
        ← map_comp_apply_of_hom, ← map_comp_apply_of_hom, fam.intrinsicNestedLeviIso_hom_comp Q I hIQ]
    rw [← hmap]
    exact (Langlands.CompactIwasawa.isMaximalCompact_comap_equiv e).mpr (hmax I)
  · intro hQ
    change Set.ncard (simpleRelativeRoots tL fam.ν) < Set.ncard (simpleRelativeRoots fam.i fam.ν)
    rw [(fam.intrinsicStandardRootData Q).2.2.1]
    have hlt : Q.val ⊂ simpleRelativeRoots fam.i fam.ν := hQ
    exact Set.ncard_lt_ncard hlt
      (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν)

end Langlands.Global.StandardParabolicFamily
