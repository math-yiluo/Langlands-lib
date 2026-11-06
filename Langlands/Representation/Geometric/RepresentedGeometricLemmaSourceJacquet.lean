import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarCharacters
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Aubert.General.JacquetStages

/-! # The source-intersection Jacquet quotient and the original inducing half -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance sourceJacquetAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

/-- A smooth ambient character restricts through the actual represented Levi map. -/
def leviRestrictionCharacter (p : P ⟶ G) (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (χ : Induction.SmoothCharacter ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    Induction.SmoothCharacter ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  exact {
    toMonoidHom := χ.toMonoidHom.comp (rationalPoints.map (l ≫ p))
    isOpen_ker := χ.isOpen_ker.preimage
      (continuous_subtype_val.comp (leviPointsEquiv p l hp hl).continuous) }

set_option maxHeartbeats 800000 in
/-- A smooth character trivial on the actual radical passes naturally through
normalized Jacquet restriction, with its original restriction to the Levi. -/
def leviJacquetTwistIso (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (χ : Induction.SmoothCharacter ℂ (rationalPoints G))
    (hχN : pointImage (r ≫ p) ≤ χ.toMonoidHom.ker) :
    letI := leviPointTopology l hl
    SmoothRep.twistFunctor χ.toMonoidHom χ.isOpen_ker ⋙
        leviJacquetFunctor.{u, v} p l r hp hr hl hmul ≅
      leviJacquetFunctor p l r hp hr hl hmul ⋙
        SmoothRep.twistFunctor
          (leviRestrictionCharacter p l hp hl χ).toMonoidHom
          (leviRestrictionCharacter p l hp hl χ).isOpen_ker := by
  letI := leviPointTopology l hl
  let R := pointImage (r ≫ p)
  let e := fun A : SmoothRep.{0, u, v} ℂ (rationalPoints G) =>
    Jacquet.Localization.transportEquiv
      (Langlands.twist χ.toMonoidHom A.representation) A.representation
      R R 1 1 (MulEquiv.refl R) (LinearEquiv.refl ℂ A)
      (fun n a => by
        change (χ.toMonoidHom n : ℂ) • A.representation n a = A.representation n a
        rw [show χ.toMonoidHom n = 1 from hχN n.property]
        simp only [Units.val_one, one_smul])
      (fun _ => rfl)
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso {
    toLinearEquiv := e A
    isIntertwining' := ?_ }) ?_
  · intro m
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective
      (Langlands.twist χ.toMonoidHom A.representation) R 1 x
    change e A
        (((leviInverseHalfCharacter p l r hp hr hl).toMonoidHom m : ℂ) •
          Jacquet.Localization.mk _ R 1
            ((χ.toMonoidHom (rationalPoints.map (l ≫ p) m) : ℂ) •
              A.representation (rationalPoints.map (l ≫ p) m) a)) =
      (χ.toMonoidHom (rationalPoints.map (l ≫ p) m) : ℂ) •
        ((leviInverseHalfCharacter p l r hp hr hl).toMonoidHom m : ℂ) •
          Jacquet.Localization.mk A.representation R 1
            (A.representation (rationalPoints.map (l ≫ p) m) a)
    rw [map_smul, map_smul]
    exact smul_comm
      ((leviInverseHalfCharacter p l r hp hr hl).toMonoidHom m : ℂ)
      (χ.toMonoidHom (rationalPoints.map (l ≫ p) m) : ℂ)
      (Jacquet.Localization.mk A.representation R 1
        (A.representation (rationalPoints.map (l ≫ p) m) a))
  · intro A B f
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective
      (Langlands.twist χ.toMonoidHom A.representation) R 1 x
    rfl

@[simp]
theorem leviJacquetTwistIso_hom_mk (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (χ : Induction.SmoothCharacter ℂ (rationalPoints G))
    (hχN : pointImage (r ≫ p) ≤ χ.toMonoidHom.ker)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (a : A) :
    letI := leviPointTopology l hl
    SmoothRep.hom ((leviJacquetTwistIso p l r hp hr hl hmul χ hχN).hom.app A)
        (Jacquet.Localization.mk (Langlands.twist χ.toMonoidHom A.representation)
          (pointImage (r ≫ p)) 1 a) =
      Jacquet.Localization.mk A.representation (pointImage (r ≫ p)) 1 a := rfl

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

/-- The original inducing half-character is trivial on the actual source
intersection radical, without a root or dynamic presentation premise. -/
theorem sourceRadical_le_ker_inducingHalfCharacter :
    letI := leviPointTopology l hl
    pointImage (D.r' ≫ D.p') ≤
      (leviInducingHalfCharacter p l r hp hr hl).toMonoidHom.ker := by
  let _ := hl.isConnectedReductive.isAffineHom
  let _ := leviPointTopology l hl
  let _ := leviPoints_nonarchimedeanGroup p l hp hl
  let R := pointImage (r ≫ p)
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let hn := pointImage_le_normalizer p l r hr
  let δ := (HaarModulus.closedRestrictCharacter R hc (pointImage (l ≫ p)) hn).comp
    (leviPointsEquiv p l hp hl).toMonoidHom
  have ho : IsOpen (δ.ker : Set (rationalPoints M)) :=
    (HaarModulus.isOpen_ker_closedRestrictCharacter R hc (pointImage (l ≫ p)) hn).preimage
      (leviPointsEquiv p l hp hl).continuous
  have hcompact := isLimitOfCompactSubgroups_pointImage_radical
    D.p' D.r' D.hp'.isClosedSubgroup D.hr'.1
  intro n hn
  have hδ := positiveCharacter_eq_one_on_compactLimit δ ho
    (pointImage (D.r' ≫ D.p')) hcompact ⟨n, hn⟩
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) n = 1
  simp only [Jacquet.complexCharacter, Jacquet.positiveHalfCharacter,
    MonoidHom.comp_apply, hδ, map_one]

/-- Moving the original source inducing half through the actual source
intersection Jacquet quotient, naturally in every smooth source representation. -/
def sourceJacquetInducingHalfTwistIso :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    let χ := leviInducingHalfCharacter p l r hp hr hl
    SmoothRep.twistFunctor χ.toMonoidHom χ.isOpen_ker ⋙
        leviJacquetFunctor.{u, v} D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ≅
      leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ⋙
        SmoothRep.twistFunctor
          (leviRestrictionCharacter D.p' D.l' D.hp' D.hl' χ).toMonoidHom
          (leviRestrictionCharacter D.p' D.l' D.hp' D.hl' χ).isOpen_ker := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  exact leviJacquetTwistIso D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul'
    (leviInducingHalfCharacter p l r hp hr hl)
    D.sourceRadical_le_ker_inducingHalfCharacter

@[simp]
theorem sourceJacquetInducingHalfTwistIso_hom_mk
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (a : A) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    SmoothRep.hom (D.sourceJacquetInducingHalfTwistIso.hom.app A)
        (Jacquet.Localization.mk
          (Langlands.twist
            (leviInducingHalfCharacter p l r hp hr hl).toMonoidHom A.representation)
          (pointImage (D.r' ≫ D.p')) 1 a) =
      Jacquet.Localization.mk A.representation (pointImage (D.r' ≫ D.p')) 1 a := rfl

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
