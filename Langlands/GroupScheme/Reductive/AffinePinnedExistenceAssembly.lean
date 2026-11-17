import Langlands.GroupScheme.Reductive.AffinePinnedBasedCorrection
import Langlands.GroupScheme.Reductive.AffinePinnedCorrectionAssembly

/-! # Global assembly from affine based pinning corrections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

namespace FppfPinnedCorrection

/-- The correction's actual covering map as a singleton fppf covering family. -/
def cover {e : Comparison f g} (C : FppfPinnedCorrection e) :
    Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T :=
  Scheme.Cover.mkOfCovers PUnit (fun _ => C.space) (fun _ => C.map)
    (fun x => by
      let : Surjective C.map := C.surjective
      obtain ⟨y, hy⟩ := C.map.surjective x
      exact ⟨PUnit.unit, y, hy⟩)
    (fun _ => ⟨C.flat, C.locallyOfFinitePresentation⟩)

/-- Compose arbitrary fppf covering families with the individual fppf
correction covers, then collapse to one actual correction. -/
def bindCover (e : Comparison f g)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T)
    (C : ∀ i, FppfPinnedCorrection (pullComparison e (𝒰.f i))) :
    FppfPinnedCorrection e :=
  ofCover e (𝒰.bind (fun i => (C i).cover)) (fun ⟨i, _⟩ =>
    (pinnedCorrection_pullComparison_comp_iff e (𝒰.f i) (C i).map).mp
      ⟨(C i).section_, (C i).pinned⟩)

/-- Absorb an initial actual target inner correction by multiplying its
pulled-back section with the later pinning-correction section. -/
def absorbTargetCorrection (e : Comparison f g)
    (c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X)
    (C : FppfPinnedCorrection (e ≪≫ (N.groupOver g).innerIso c)) :
    FppfPinnedCorrection e := by
  let b := N.pullBasePoint g C.map c
  refine {
    space := C.space
    map := C.map
    flat := C.flat
    surjective := C.surjective
    locallyOfFinitePresentation := C.locallyOfFinitePresentation
    section_ := C.section_ * b
    pinned := ?_
  }
  have hi : (N.groupOver (C.map ≫ g)).innerIso (C.section_ * b) =
      (N.groupOver (C.map ≫ g)).innerIso b ≪≫
        (N.groupOver (C.map ≫ g)).innerIso C.section_ :=
    Iso.ext (innerIso_mul_hom _ _ _)
  rw [hi]
  have h := C.pinned
  rw [pullComparison_trans, pullComparison_inner] at h
  simpa only [b, Iso.trans_assoc] using h

end FppfPinnedCorrection

/-- The remaining affine input: every algebra-based full based comparison
admits an actual fppf target correction aligning its original pinning vectors. -/
def HasAffineBasedPinnedCorrections : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (d : BasedCoordinateIso
      (M.inclusionOver (algebraBaseMap M.ring A))
      (N.inclusionOver (algebraBaseMap N.ring A))
      M.rootDatum N.rootDatum M.basis N.basis),
      Nonempty (FppfPinnedCorrection d.groupIso)

private theorem exists_pinnedCorrection_at_affineMap
    (h : HasAffineBasedPinnedCorrections.{u})
    (A : CommRingCat.{u}) (f : Spec A ⟶ M.base) (g : Spec A ⟶ N.base)
    (d : BasedCoordinateIso (M.inclusionOver f) (N.inclusionOver g)
      M.rootDatum N.rootDatum M.basis N.basis) :
    Nonempty (FppfPinnedCorrection d.groupIso) := by
  let : Algebra M.ring A := (Spec.preimage f).hom.toAlgebra
  let : Algebra N.ring A := (Spec.preimage g).hom.toAlgebra
  have hf : algebraBaseMap M.ring A = f := Spec.map_preimage f
  have hg : algebraBaseMap N.ring A = g := Spec.map_preimage g
  revert d
  rw [← hf, ← hg]
  intro d
  exact h M N A d

namespace FppfPinnedCorrection

/-- Arbitrary-comparison existence follows from the affine based input,
using actual affine etale based-correction charts and fppf cover assembly. -/
def ofAffineBasedInput (h : HasAffineBasedPinnedCorrections.{u})
    (e : Comparison f g) : FppfPinnedCorrection e := by
  let 𝒰₀ := affineBasedCorrectionCover e
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T :=
    𝒰₀.cover.changeProp (fun x => by
      let : Etale (𝒰₀.f x) := 𝒰₀.map_prop x
      exact ⟨inferInstance, inferInstance⟩)
  refine bindCover e 𝒰 (fun x => ?_)
  let D := affineBasedCorrectionChart e x
  have hD : Nonempty (FppfPinnedCorrection D.data.groupIso) :=
    exists_pinnedCorrection_at_affineMap h D.ring (D.map ≫ f) (D.map ≫ g) D.data
  have hC : Nonempty (FppfPinnedCorrection
      (pullComparison e D.map ≪≫ (N.groupOver (D.map ≫ g)).innerIso D.section_)) := by
    rw [← D.groupIso_eq]
    exact hD
  exact absorbTargetCorrection (pullComparison e D.map) D.section_ (Classical.choice hC)

end FppfPinnedCorrection

end Langlands.GroupScheme.AffinePinnedModel

namespace Langlands.GroupScheme

open AffinePinnedModel

/-- The sole affine based-correction input suffices for the exact arbitrary
scheme local-normalization statement. -/
theorem fppfLocalPinnedNormalization_of_affineBasedPinnedCorrections
    (h : HasAffineBasedPinnedCorrections.{u}) :
    FppfLocalPinnedNormalizationExistenceStatement.{u} :=
  fppfLocalPinnedNormalization_of_pinnedCorrections
    (fun _ _ _ _ _ e => ⟨FppfPinnedCorrection.ofAffineBasedInput h e⟩)

end Langlands.GroupScheme
