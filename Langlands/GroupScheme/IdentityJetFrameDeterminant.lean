import Langlands.GroupScheme.IdentityJetFrames
import Langlands.AlgebraicGeometry.Modules.BasisHomGluing

/-! # Determinant transitions of actual adapted jet frames -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

open Langlands.Scheme.Modules Algebra.SectionJet.Coordinates CoordinateWeights

variable {S : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {σ : Type u} [Fintype σ] [DecidableEq σ]

attribute [local instance] sectionAlgebra

private theorem frameMatrix_restrict {M : S.Modules} {I : Type u} [Fintype I]
    {T T' W W' : S.Opens}
    (e : SheafOfModules.free (R := S.ringCatSheaf.over T) I ≅ M.over T)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over T') I ≅ M.over T')
    (hT : W ≤ T) (hT' : W ≤ T') (h : W' ≤ W) :
    ((localSectionBasis e (Over.mk (homOfLE hT))).toMatrix
      (localSectionBasis e' (Over.mk (homOfLE hT')))).map
        (S.presheaf.map (homOfLE h).op).hom =
      (localSectionBasis e (Over.mk (homOfLE (h.trans hT)))).toMatrix
        (localSectionBasis e' (Over.mk (homOfLE (h.trans hT')))) := by
  ext i j
  change S.presheaf.map (homOfLE h).op
      ((localSectionBasis e (Over.mk (homOfLE hT))).repr
        (localSectionBasis e' (Over.mk (homOfLE hT')) j) i) = _
  calc
    _ = (localSectionBasis e (Over.mk (homOfLE (h.trans hT)))).repr
        (M.presheaf.map (homOfLE h).op
          (localSectionBasis e' (Over.mk (homOfLE hT')) j)) i :=
      (localSectionBasis_repr_restrict e
        (Over.homMk (homOfLE h) :
          Over.mk (homOfLE (h.trans hT)) ⟶ Over.mk (homOfLE hT)) _ i).symm
    _ = _ := congrArg
      (fun x => (localSectionBasis e (Over.mk (homOfLE (h.trans hT)))).repr x i)
      (localSectionBasis_restrict e'
        (Over.homMk (homOfLE h) :
          Over.mk (homOfLE (h.trans hT')) ⟶ Over.mk (homOfLE hT')) j)

private theorem frameMatrix_det_restrict {M : S.Modules} {I : Type u} [Fintype I]
    [DecidableEq I] {T T' W W' : S.Opens}
    (e : SheafOfModules.free (R := S.ringCatSheaf.over T) I ≅ M.over T)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over T') I ≅ M.over T')
    (hT : W ≤ T) (hT' : W ≤ T') (h : W' ≤ W) :
    S.presheaf.map (homOfLE h).op
        ((localSectionBasis e (Over.mk (homOfLE hT))).toMatrix
          (localSectionBasis e' (Over.mk (homOfLE hT')))).det =
      ((localSectionBasis e (Over.mk (homOfLE (h.trans hT)))).toMatrix
        (localSectionBasis e' (Over.mk (homOfLE (h.trans hT'))))).det := by
  rw [RingHom.map_det]
  exact congrArg (fun A : Matrix I I Γ(S, W') => A.det)
    (frameMatrix_restrict e e' hT hT' h)

private theorem sectionBasis_restriction_det
    {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (bU : Module.Basis σ Γ(S, U) (RingHom.ker (augmentation G U)).Cotangent)
    (bV : Module.Basis σ Γ(S, V) (RingHom.ker (augmentation G V)).Cotangent)
    (zU : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (hzU : ∀ i, augmentation G U (zU i) = 0)
    (hzbU : ∀ i, AugmentedAlgebra.classMap (augmentation G U) (zU i) = bU i)
    (zV : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ V))
    (hzV : ∀ i, augmentation G V (zV i) = 0)
    (hzbV : ∀ i, AugmentedAlgebra.classMap (augmentation G V) (zV i) = bV i)
    (n : ℕ) :
    (((chosenTotalBasis zV bV hzV hzbV n).map (sectionsEquiv G n V).symm).toMatrix
      (fun j => (module G n).presheaf.map (homOfLE h).op
        (((chosenTotalBasis zU bU hzU hzbU n).map (sectionsEquiv G n U).symm) j))).det =
      (cotangentRestrictionMatrix G h bU bV).det ^ jetExponent σ n := by
  have heq :
      ((chosenTotalBasis zV bV hzV hzbV n).map (sectionsEquiv G n V).symm).toMatrix
          (fun j => (module G n).presheaf.map (homOfLE h).op
            (((chosenTotalBasis zU bU hzU hzbU n).map (sectionsEquiv G n U).symm) j)) =
        (chosenTotalBasis zV bV hzV hzbV n).toMatrix
          (fun j => restriction G n h (chosenTotalBasis zU bU hzU hzbU n j)) := by
    ext i j
    change (chosenTotalBasis zV bV hzV hzbV n).repr
      (sectionsEquiv G n V ((module G n).presheaf.map (homOfLE h).op
        ((sectionsEquiv G n U).symm (chosenTotalBasis zU bU hzU hzbU n j)))) i = _
    have hr := sectionsEquiv_restrict G n h
      ((sectionsEquiv G n U).symm (chosenTotalBasis zU bU hzU hzbU n j))
    rw [LinearEquiv.apply_symm_apply] at hr
    exact congrArg (fun x => (chosenTotalBasis zV bV hzV hzbV n).repr x i) hr.symm
  rw [heq]
  exact totalBasis_restrictionMatrix_det G h bU bV zU hzU hzbU zV hzV hzbV
    (Algebra.SectionJet.linearSection (augmentation G U))
    (Algebra.SectionJet.truncate_linearSection (augmentation G U))
    (Algebra.SectionJet.linearSection (augmentation G V))
    (Algebra.SectionJet.truncate_linearSection (augmentation G V)) n

variable (U V : S.affineOpens)
    (eU : SheafOfModules.free (R := S.ringCatSheaf.over U.1) σ ≅
      G.cotangentAtIdentity.over U.1)
    (eV : SheafOfModules.free (R := S.ringCatSheaf.over V.1) σ ≅
      G.cotangentAtIdentity.over V.1)
    (zU : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (hzU : ∀ i, augmentation G U (zU i) = 0)
    (hzbU : ∀ i, AugmentedAlgebra.classMap (augmentation G U) (zU i) =
      cotangentFrameBasis G U eU U le_rfl i)
    (zV : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ V))
    (hzV : ∀ i, augmentation G V (zV i) = 0)
    (hzbV : ∀ i, AugmentedAlgebra.classMap (augmentation G V) (zV i) =
      cotangentFrameBasis G V eV V le_rfl i)

/-- The actual cotangent frame change on any open inside both charts. -/
def cotangentOverlapMatrix (W : S.Opens) (hU : W ≤ U.1) (hV : W ≤ V.1) :
    Matrix σ σ Γ(S, W) :=
  (localSectionBasis eU (Over.mk (homOfLE hU))).toMatrix
    (localSectionBasis eV (Over.mk (homOfLE hV)))

/-- The actual adapted-jet frame change on any open inside both charts. -/
def adaptedOverlapMatrix (n : ℕ) (W : S.Opens) (hU : W ≤ U.1) (hV : W ≤ V.1) :
    Matrix (JetIndex σ n) (JetIndex σ n) Γ(S, W) :=
  (localSectionBasis (adaptedFrame G U eU zU hzU hzbU n)
    (Over.mk (homOfLE hU))).toMatrix
      (localSectionBasis (adaptedFrame G V eV zV hzV hzbV n)
        (Over.mk (homOfLE hV)))

theorem adaptedOverlapMatrix_det_affine (n : ℕ) (W : S.affineOpens)
    (hU : W.1 ≤ U.1) (hV : W.1 ≤ V.1) :
    (adaptedOverlapMatrix G U V eU eV zU hzU hzbU zV hzV hzbV n W hU hV).det =
      (cotangentOverlapMatrix G U V eU eV W hU hV).det ^ jetExponent σ n := by
  classical
  let bW := cotangentFrameBasis G U eU W hU
  obtain ⟨zW, hzW, hzbW⟩ := exists_basis_lifts (ε := augmentation G W) bW
  let cW := (chosenTotalBasis zW bW hzW hzbW n).map (sectionsEquiv G n W).symm
  let cU : Module.Basis (JetIndex σ n) Γ(S, W) Γ(module G n, W) :=
    localSectionBasis (adaptedFrame G U eU zU hzU hzbU n) (Over.mk (homOfLE hU))
  let cV : Module.Basis (JetIndex σ n) Γ(S, W) Γ(module G n, W) :=
    localSectionBasis (adaptedFrame G V eV zV hzV hzbV n) (Over.mk (homOfLE hV))
  have h0 : (cW.toMatrix cU).det = 1 := by
    have hvec : (cU : JetIndex σ n → Γ(module G n, W)) =
        fun j => (module G n).presheaf.map (homOfLE hU).op
          (adaptedSectionBasis G U eU zU hzU hzbU n j) :=
      funext (adaptedFrame_basis G U eU zU hzU hzbU n (Over.mk (homOfLE hU)))
    rw [hvec]
    change (((chosenTotalBasis zW bW hzW hzbW n).map (sectionsEquiv G n W).symm).toMatrix
      (fun j => (module G n).presheaf.map (homOfLE hU).op
        (((chosenTotalBasis zU (cotangentFrameBasis G U eU U le_rfl) hzU hzbU n).map
          (sectionsEquiv G n U).symm) j))).det = 1
    rw [sectionBasis_restriction_det,
      cotangentRestrictionMatrix_frame G U eU W hU, Matrix.det_one, one_pow]
  have hm :
      cotangentRestrictionMatrix G hV (cotangentFrameBasis G V eV V le_rfl) bW =
        cotangentOverlapMatrix G U V eU eV W hU hV := by
    ext i j
    change bW.repr (IdentityCotangent.restriction G ‹Smooth G.X.hom› hV
      (cotangentFrameBasis G V eV V le_rfl j)) i = _
    rw [cotangentFrameBasis_restrict G V eV W hV]
    change (localSectionBasis eU (Over.mk (homOfLE hU))).repr
      ((IdentityCotangent.sectionsEquiv G ‹Smooth G.X.hom› W).symm
        (IdentityCotangent.sectionsEquiv G ‹Smooth G.X.hom› W
          (localSectionBasis eV (Over.mk (homOfLE hV)) j))) i = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have h1 : (cW.toMatrix cV).det =
      (cotangentOverlapMatrix G U V eU eV W hU hV).det ^ jetExponent σ n := by
    have hvec : (cV : JetIndex σ n → Γ(module G n, W)) =
        fun j => (module G n).presheaf.map (homOfLE hV).op
          (adaptedSectionBasis G V eV zV hzV hzbV n j) :=
      funext (adaptedFrame_basis G V eV zV hzV hzbV n (Over.mk (homOfLE hV)))
    rw [hvec]
    change (((chosenTotalBasis zW bW hzW hzbW n).map (sectionsEquiv G n W).symm).toMatrix
      (fun j => (module G n).presheaf.map (homOfLE hV).op
        (((chosenTotalBasis zV (cotangentFrameBasis G V eV V le_rfl) hzV hzbV n).map
          (sectionsEquiv G n V).symm) j))).det = _
    rw [sectionBasis_restriction_det, hm]
  have hmul : (cW.toMatrix cU).det * (cU.toMatrix cV).det = (cW.toMatrix cV).det := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]
  rw [h0, one_mul, h1] at hmul
  exact hmul

/-- The actual adapted-jet transition determinant equals the cotangent
transition determinant power on every overlap open, including nonaffine opens. -/
theorem adaptedOverlapMatrix_det (n : ℕ) (W : S.Opens)
    (hU : W ≤ U.1) (hV : W ≤ V.1) :
    (adaptedOverlapMatrix G U V eU eV zU hzU hzbU zV hzV hzbV n W hU hV).det =
      (cotangentOverlapMatrix G U V eU eV W hU hV).det ^ jetExponent σ n := by
  apply BasisHomGluing.eq_of_basis (N := Langlands.SchemeModule.structureModule S)
    (P := IsAffineOpen)
    (fun _ _ hx => exists_isAffineOpen_mem_and_subset hx)
  intro T hT hTW
  change S.presheaf.map (homOfLE hTW).op
      (adaptedOverlapMatrix G U V eU eV zU hzU hzbU zV hzV hzbV n W hU hV).det =
    S.presheaf.map (homOfLE hTW).op
      ((cotangentOverlapMatrix G U V eU eV W hU hV).det ^ jetExponent σ n)
  rw [map_pow]
  change S.presheaf.map (homOfLE hTW).op
      ((localSectionBasis (adaptedFrame G U eU zU hzU hzbU n)
        (Over.mk (homOfLE hU))).toMatrix
          (localSectionBasis (adaptedFrame G V eV zV hzV hzbV n)
            (Over.mk (homOfLE hV)))).det = _
  rw [frameMatrix_det_restrict]
  change _ = (S.presheaf.map (homOfLE hTW).op
    ((localSectionBasis eU (Over.mk (homOfLE hU))).toMatrix
      (localSectionBasis eV (Over.mk (homOfLE hV)))).det) ^ jetExponent σ n
  rw [frameMatrix_det_restrict]
  exact adaptedOverlapMatrix_det_affine G U V eU eV zU hzU hzbU zV hzV hzbV n
    ⟨T, hT⟩ (hTW.trans hU) (hTW.trans hV)

end Langlands.GroupScheme.IdentityJet
