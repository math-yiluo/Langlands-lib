import Langlands.GroupScheme.Rational.SimpleCorootCoordinates
import Langlands.GroupScheme.Rational.CorootRationalGaloisTransport
import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning
import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots

/-! # Actual Galois transport of simple coroots and their points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

private def torusGroupIso {S : Scheme.{u}} {T T' : CommGroupScheme S}
    (e : T ≅ T') : T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

namespace GaloisCompatiblePinningData

open GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance orbitDecompositionBaseAffine : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (D : GaloisCompatiblePinningData k K G)

private def descendedRootDatum :=
  torusTransportRootDatum D.torusIso D.pinning.rootDatum

private theorem descendedRootDatum_isRootDatum :
    IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
      D.descendedRootDatum := by
  have hs : D.pinning.inclusion ≫ (Iso.refl _).hom =
      CommGroupScheme.groupHom D.torusIso.hom ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion := by
    simpa only [Iso.refl_hom, Category.comp_id] using D.inclusion_eq
  exact D.pinning.isRootDatum.torusTransport D.torusIso (Iso.refl _) hs

private theorem baseChange_inclusion_eq :
    (GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion =
      CommGroupScheme.groupHom D.torusIso.inv ≫ D.pinning.inclusion := by
  rw [D.inclusion_eq]
  change _ = CommGroupScheme.groupHom (D.torusIso.inv ≫ D.torusIso.hom) ≫ _
  rw [D.torusIso.inv_hom_id]
  exact (Category.id_comp _).symm

private theorem baseChange_inclusion_isClosed :
    IsClosedSubgroup ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion) := by
  rw [D.baseChange_inclusion_eq]
  exact D.pinning.isMaximalTorus.2.1.iso_comp (torusGroupIso D.torusIso).symm

private theorem baseChange_torus_isSplit :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp :=
  IsSplitTorus.of_iso (torusGroupIso D.torusIso).symm D.pinning.isSplitTorus

local instance baseChange_inclusion_mono :
    Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion).hom.hom.left := by
  have : IsClosedImmersion
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion).hom.hom.left :=
    D.baseChange_inclusion_isClosed
  infer_instance

private theorem baseChange_inclusion_weylImageFinite :
    Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)) := by
  have := D.baseChange_inclusion_isClosed
  have := D.pinning.isConnectedReductive.smooth
  exact splitTorusWeylImageFinite K _ _ D.baseChange_torus_isSplit _
    D.baseChange_inclusion_isClosed

private theorem descendedRootDatum_action_root (σ : K ≃ₐ[k] K)
    (a : D.pinning.base.support) :
    D.descendedRootDatum.root (D.action σ a : D.pinning.rootIndex) =
      (galoisTransportRootDatum k K D.torus D.descendedRootDatum σ).root
        (a : D.pinning.rootIndex) := by
  simpa only [descendedRootDatum, torusTransportRootDatum_root,
    galoisTransportRootDatum_root] using D.action_root σ a

private theorem descendedRootDatum_galois_isRootDatum (σ : K ≃ₐ[k] K) :
    IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
      (galoisTransportRootDatum k K D.torus D.descendedRootDatum σ) :=
  IsRootDatumOf.galoisTransport k K D.inclusion
    D.descendedRootDatum_isRootDatum σ

private theorem descendedRootDatum_action_coroot (σ : K ≃ₐ[k] K)
    (a : D.pinning.base.support) :
    D.descendedRootDatum.coroot (D.action σ a : D.pinning.rootIndex) =
      (galoisTransportRootDatum k K D.torus D.descendedRootDatum σ).coroot
        (a : D.pinning.rootIndex) := by
  have := D.baseChange_inclusion_isClosed
  have := D.baseChange_inclusion_weylImageFinite
  exact D.descendedRootDatum_isRootDatum.coroot_eq_of_finite_weylImage _
    (D.descendedRootDatum_galois_isRootDatum σ) (D.descendedRootDatum_action_root σ a)

/-- The root permutation of compatible pinning data also transports its actual coroots. -/
theorem action_coroot (σ : K ≃ₐ[k] K) (a : D.pinning.base.support) :
    cocharacterLattice.congr D.torusIso
        (D.pinning.rootDatum.coroot (D.action σ a)) =
      cocharacterLattice.galoisRepresentation k K D.torus σ
        (cocharacterLattice.congr D.torusIso (D.pinning.rootDatum.coroot a)) := by
  have heq := D.descendedRootDatum_action_coroot σ a
  simpa only [descendedRootDatum, torusTransportRootDatum_coroot,
    galoisTransportRootDatum_coroot] using heq

/-- Actual points of the pinned torus transported to the base changed descended torus. -/
def torusPointEquiv : rationalPoints D.pinning.torus.toGrp ≃*
    rationalPoints (baseChanged k K D.torus.toGrp) :=
  isoPointsEquiv (torusGroupIso D.torusIso) _

/-- The actual simple-coroot point in the base changed descended torus. -/
def torusCorootPoint (a : D.pinning.base.support) (t : Kˣ) :
    rationalPoints (baseChanged k K D.torus.toGrp) :=
  D.torusPointEquiv (D.pinning.simpleCorootPoint a t)

/-- Actual simple-coroot coordinates on the base changed descended torus. -/
def torusCoordinates (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤) :
    rationalPoints (baseChanged k K D.torus.toGrp) ≃*
      (D.pinning.base.support → Kˣ) :=
  D.torusPointEquiv.symm.trans (D.pinning.simpleCorootCoordinates hspan)

/-- Galois conjugation carries a coroot point to the permuted coroot with conjugated unit. -/
theorem torusCorootPoint_rationalConjugate (σ : K ≃ₐ[k] K)
    (a : D.pinning.base.support) (t : Kˣ) :
    rationalConjugate k K D.torus.toGrp σ (D.torusCorootPoint a t) =
      D.torusCorootPoint (D.action σ a) (Units.map σ.toMonoidHom t) := by
  change rationalConjugate k K D.torus.toGrp σ
      (rationalCocharacterValue k K D.torus.toGrp
        (CommGroupScheme.groupHom
          (cocharacterLattice.congr D.torusIso (D.pinning.rootDatum.coroot a))) t) =
    rationalCocharacterValue k K D.torus.toGrp
      (CommGroupScheme.groupHom
        (cocharacterLattice.congr D.torusIso
          (D.pinning.rootDatum.coroot (D.action σ a)))) (Units.map σ.toMonoidHom t)
  rw [rationalCocharacterValue_rationalConjugate]
  change rationalCocharacterValue k K D.torus.toGrp
      (CommGroupScheme.groupHom
        (cocharacterLattice.galoisRepresentation k K D.torus σ
          (cocharacterLattice.congr D.torusIso (D.pinning.rootDatum.coroot a))))
      (Units.map σ.toMonoidHom t) = _
  rw [← D.action_coroot σ a]

end GaloisCompatiblePinningData

end Langlands.GroupScheme
