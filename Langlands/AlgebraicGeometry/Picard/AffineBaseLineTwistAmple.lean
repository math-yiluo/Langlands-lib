import Langlands.AlgebraicGeometry.Picard.AffineBaseAmpleLocality
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof

/-! # Ampleness is unchanged by an actual line twist from an affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {X S : Scheme.{u}}

/-- A trivialization of the actual base line removes its twist over the
inverse image of that open, using actual module pullbacks and tensors. -/
def affineBaseTwistLocalIso (f : X ⟶ S) (L M : LineBundle X) (B : LineBundle S)
    (e : M.obj ≅ tensorObj L.obj ((Scheme.Modules.pullback f).obj B.obj))
    (U : S.Opens)
    (eB : (Scheme.Modules.pullback U.ι).obj B.obj ≅ structureModule U.toScheme) :
    (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M.obj ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L.obj := by
  let i := (f ⁻¹ᵁ U).ι
  let q := f ∣_ U
  let EB : (Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback f).obj B.obj) ≅ structureModule (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullbackComp i f).app B.obj ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app B.obj ≪≫
        ((Scheme.Modules.pullbackComp q U.ι).app B.obj).symm ≪≫
          (Scheme.Modules.pullback q).mapIso eB ≪≫ pullbackUnitIso q
  let := pullbackTensorComparisonIsIso i
  exact (Scheme.Modules.pullback i).mapIso e ≪≫
    (asIso (pullbackTensorComparison i)).app
      (L.obj, (Scheme.Modules.pullback f).obj B.obj) ≪≫
      (tensorFunctor (f ⁻¹ᵁ U).toScheme).mapIso ((Iso.refl _).prod EB) ≪≫
        tensorRightUnitor ((Scheme.Modules.pullback i).obj L.obj)

/-- Over an affine base, an actual tensor twist by a pulled-back base line
preserves and reflects ampleness on a compact quasi-separated total space. -/
theorem isAmple_iff_of_affine_base_twist
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S]
    (f : X ⟶ S) (L M : LineBundle X) (B : LineBundle S)
    (e : M.obj ≅ tensorObj L.obj ((Scheme.Modules.pullback f).obj B.obj)) :
    M.IsAmple ↔ L.IsAmple := by
  have hlocal (s : S) : ∃ (r : Γ(S, ⊤)), s ∈ S.basicOpen r ∧ Nonempty
      ((Scheme.Modules.pullback (S.basicOpen r).ι).obj B.obj ≅
        structureModule (S.basicOpen r).toScheme) := by
    obtain ⟨r, hr, hsr⟩ := (isAffineOpen_top S).exists_basicOpen_le
      (V := B.trivializingOpen s) ⟨s, B.mem_trivializingOpen s⟩ (by trivial)
    exact ⟨r, hsr, ⟨pullbackTrivializationOfLE hr B.obj (B.localTrivialization s)⟩⟩
  have haff (r : Γ(S, ⊤)) : IsAffineHom (f ⁻¹ᵁ S.basicOpen r).ι := by
    rw [Scheme.preimage_basicOpen_top f r]
    infer_instance
  constructor
  · intro hM
    apply L.isAmple_of_affine_base_neighbourhoods f
    intro s
    obtain ⟨r, hsr, ⟨eB⟩⟩ := hlocal s
    let := haff r
    exact ⟨S.basicOpen r, hsr,
      (hM.pullback_of_isAffineHom (f ⁻¹ᵁ S.basicOpen r).ι).of_iso
        (affineBaseTwistLocalIso f L M B e (S.basicOpen r) eB)⟩
  · intro hL
    apply M.isAmple_of_affine_base_neighbourhoods f
    intro s
    obtain ⟨r, hsr, ⟨eB⟩⟩ := hlocal s
    let := haff r
    exact ⟨S.basicOpen r, hsr,
      (hL.pullback_of_isAffineHom (f ⁻¹ᵁ S.basicOpen r).ι).of_iso
        (affineBaseTwistLocalIso f L M B e (S.basicOpen r) eB).symm⟩

/-- In particular the actual tensor product with any actual pulled-back base
line preserves ampleness over an affine base. -/
theorem LineBundle.IsAmple.tensor_pullback_of_affine_base
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S]
    {L : LineBundle X} (hL : L.IsAmple) (f : X ⟶ S) (B : LineBundle S) :
    (LineBundle.tensor pullbackTensorComparisonIsIso L ((LineBundle.pullback f).obj B)).IsAmple :=
  (isAmple_iff_of_affine_base_twist f L _ B (Iso.refl _)).mpr hL

end Langlands.AlgebraicGeometry.Picard
