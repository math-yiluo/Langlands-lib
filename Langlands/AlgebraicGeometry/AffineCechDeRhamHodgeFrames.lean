import Langlands.AlgebraicGeometry.AffineCechDeRhamDifferentialSections
import Langlands.AlgebraicGeometry.FreeSectionPullback
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Čech cochains in a finite frame of relative differentials -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open Langlands.Scheme Langlands.Scheme.Modules

/-- The affine section ring with the scalar structure fixed by the structural morphism. -/
abbrev sectionRing {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) := (sectionAlgebras f).obj (op W)

/-- The actual global section given by a chosen frame vector. -/
abbrev frameSection {X : Scheme.{u}} {M : X.Modules} {κ : Type u}
    (E : SheafOfModules.free (R := X.ringCatSheaf) κ ≅ M) (i : κ) : Γ(M, ⊤) :=
  (SheafOfModules.sectionsMap E.hom (SheafOfModules.freeSection i)).val (op ⊤)

section Bases

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) {κ : Type u} [Fintype κ]
  (E : SheafOfModules.free (R := X.ringCatSheaf) κ ≅ relativeDifferentials f)

/-- The basis on an actual affine section ring induced by a global free frame. -/
def hodgeOneBasis (W : X.Opens) (hW : IsAffineOpen W) :
    Module.Basis κ (sectionRing f W) Ω[(sectionRing f W)⁄R] := by
  let : Module Γ(X, W) Ω[(sectionRing f W)⁄R] :=
    inferInstanceAs (Module (sectionRing f W) Ω[(sectionRing f W)⁄R])
  let e : Γ(relativeDifferentials f, W) ≃ₗ[Γ(X, W)] Ω[(sectionRing f W)⁄R] :=
    (oneFormsSectionsEquiv f W hW).symm
  exact (globalSectionBasis E W).map e

lemma oneFormsSectionsEquiv_hodgeOneBasis (W : X.Opens) (hW : IsAffineOpen W) (i : κ) :
    oneFormsSectionsEquiv f W hW (hodgeOneBasis f E W hW i) =
      (SheafOfModules.sectionsMap E.hom (SheafOfModules.freeSection i)).val (op W) := by
  change oneFormsSectionsEquiv f W hW
    ((oneFormsSectionsEquiv f W hW).symm (globalSectionBasis E W i)) = _
  rw [LinearEquiv.apply_symm_apply, globalSectionBasis_apply]
  rfl

lemma hodgeOneBasis_restrict {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (h : W' ≤ W) (i : κ) :
    RelativeForms.mapOne ((sectionAlgebras f).map (homOfLE h).op).hom
      (hodgeOneBasis f E W hW i) = hodgeOneBasis f E W' hW' i := by
  apply (oneFormsSectionsEquiv f W' hW').injective
  rw [oneFormsSectionsEquiv_restrict f hW hW' h, oneFormsSectionsEquiv_hodgeOneBasis,
    oneFormsSectionsEquiv_hodgeOneBasis]
  exact (SheafOfModules.sectionsMap E.hom (SheafOfModules.freeSection i)).property (homOfLE h).op

variable [LinearOrder κ]

/-- The increasing wedges of pairs of frame vectors form a basis of two-forms. -/
abbrev hodgeTwoBasis (W : X.Opens) (hW : IsAffineOpen W) :=
  (hodgeOneBasis f E W hW).exteriorPower 2

lemma hodgeTwoBasis_restrict {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (h : W' ≤ W) (i : Set.powersetCard κ 2) :
    RelativeForms.mapTwo ((sectionAlgebras f).map (homOfLE h).op).hom
      (hodgeTwoBasis f E W hW i) = hodgeTwoBasis f E W' hW' i := by
  simp only [hodgeTwoBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    RelativeForms.mapTwo_ιMulti]
  apply congrArg (exteriorPower.ιMulti (sectionRing f W') 2)
  funext j
  exact hodgeOneBasis_restrict f E hW hW' h _

end Bases

/-- Under a semilinear map carrying each basis vector to the corresponding basis
vector, the new coordinates are the images of the old coordinates. -/
lemma basis_coordinates_map {A B M N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N] [Fintype ι]
    {r : A →+* B} (g : M →ₛₗ[r] N) (b : Module.Basis ι A M) (b' : Module.Basis ι B N)
    (h : ∀ i, g (b i) = b' i) (x : M) (i : ι) :
    b'.equivFun (g x) i = r (b.equivFun x i) := by
  have hg : g x = b'.equivFun.symm (fun j => r (b.equivFun x j)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_equivFun x]
    simp only [map_sum, g.map_smulₛₗ, h]
  rw [hg, b'.equivFun.apply_symm_apply]

section Cochains

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X) [IsSeparated f]
  {κ : Type u} [Fintype κ]
  (E : SheafOfModules.free (R := X.ringCatSheaf) κ ≅ relativeDifferentials f)

/-- One-form cochains in the frame are families of function cochains. -/
def oneCochainCoordinates (p : ℕ) : Cochains U (oneForms f) p ≃ₗ[R]
    (κ → Cochains U (functions f) p) :=
  (LinearEquiv.piCongrRight fun σ =>
    ((hodgeOneBasis f E _ (isAffineOpen_inter f U σ)).equivFun.restrictScalars R)).trans
    { toFun := fun x i σ => x σ i
      invFun := fun x σ i => x i σ
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
lemma oneCochainCoordinates_apply (p : ℕ) (b : Cochains U (oneForms f) p) (i : κ) (σ) :
    oneCochainCoordinates f U E p b i σ =
      (hodgeOneBasis f E _ (isAffineOpen_inter f U σ)).equivFun (b σ) i := rfl

/-- The coordinate comparison intertwines the Čech differentials. -/
lemma oneCochainCoordinates_cechD (p : ℕ) (b : Cochains U (oneForms f) p) (i : κ) :
    oneCochainCoordinates f U E (p + 1) (cechD U (oneForms f) p b) i =
      cechD U (functions f) p (oneCochainCoordinates f U E p b i) := by
  funext τ
  rw [oneCochainCoordinates_apply, cechD_apply, cechD_apply, map_sum]
  simp only [Finset.sum_apply, map_zsmul, Pi.smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact basis_coordinates_map (RelativeForms.mapOne _)
    (hodgeOneBasis f E _ _) (hodgeOneBasis f E _ _)
    (hodgeOneBasis_restrict f E _ _ _) _ _

variable [LinearOrder κ]

/-- The coefficient of a wedge basis vector defines a function cochain. -/
def twoCochainCoordinates (p : ℕ) (b : Cochains U (twoForms f) p) :
    Set.powersetCard κ 2 → Cochains U (functions f) p := fun i σ =>
  (hodgeTwoBasis f E _ (isAffineOpen_inter f U σ)).equivFun (b σ) i

lemma twoCochainCoordinates_cechD (p : ℕ) (b : Cochains U (twoForms f) p)
    (i : Set.powersetCard κ 2) :
    twoCochainCoordinates f U E (p + 1) (cechD U (twoForms f) p b) i =
      cechD U (functions f) p (twoCochainCoordinates f U E p b i) := by
  funext τ
  change (hodgeTwoBasis f E _ (isAffineOpen_inter f U τ)).equivFun
    (cechD U (twoForms f) p b τ) i = _
  rw [cechD_apply, cechD_apply, map_sum]
  simp only [Finset.sum_apply, map_zsmul, Pi.smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact basis_coordinates_map (RelativeForms.mapTwo _)
    (hodgeTwoBasis f E _ _) (hodgeTwoBasis f E _ _)
    (hodgeTwoBasis_restrict f E _ _ _) _ _

end Cochains

end Langlands.AlgebraicGeometry.AffineCechDeRham
