import Langlands.AbelianScheme.ArtinianHodgeExactStatement
import Langlands.AbelianScheme.CanonicalH1Primitive
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof

/-! # Comparison of the function end of the degree-one Hodge sequence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof (secHom)

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open CechResolution.AllSeq

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)

/-- The scalar structure on the section ring used in the de Rham cochains agrees with `secHom`. -/
lemma sectionAlgebras_algebraMap (V : X.Opens) :
    algebraMap (CommRingCat.of R) ((sectionAlgebras f).obj (op V)) = (secHom f V).hom := rfl

/-- A function cochain written as a cochain of the structure sheaf module. -/
def structureCochainEquiv (p : ℕ) :
    Cochains U (functions f) p ≃ₗ[R] cochain f (coverOpens U) (unitModule X) p := by
  letI (V : X.Opens) : Algebra (CommRingCat.of R) Γ(X, V) :=
    Scheme.TwoAffineOpenCover.algebraOfHom f V
  exact (cochainSecEquiv f (coverOpens U) (sectionAlgebras_algebraMap f) p).symm

lemma structureCochainEquiv_cechD (p : ℕ) (c : Cochains U (functions f) p) :
    structureCochainEquiv f U (p + 1) (cechD U (functions f) p c) =
      dCochain f (coverOpens U) (unitModule X) p (structureCochainEquiv f U p c) := by
  exact (dCochain_unit f (coverOpens U) p _).symm

/-- Actual Čech cocycles in the function part of the de Rham complex, identified with
cocycles of the structure module. -/
def structureCocycleEquiv (n : ℕ) :
    (cechD U (functions f) (n + 1)).ker ≃ₗ[R]
      (dCochain f (coverOpens U) (unitModule X) (n + 1)).ker := by
  refine (LinearEquiv.ofEq _ _ ?_).trans ((structureCochainEquiv f U (n + 1)).ofSubmodule' _)
  ext x
  change cechD U (functions f) (n + 1) x = 0 ↔
    dCochain f (coverOpens U) (unitModule X) (n + 1) (structureCochainEquiv f U (n + 1) x) = 0
  rw [← structureCochainEquiv_cechD, LinearEquiv.map_eq_zero_iff]

open DerivedSections

variable [Finite U.I₀] [IsSeparated f]

/-- For any supplied finite affine cover, the function end of the Hodge sequence
is the first cohomology of the structure sheaf. -/
def structureH1Equiv : structureH1 f U ≃ₗ[R] (relativeCohomology f 1).obj (unitModule X) := by
  letI := Fintype.ofFinite U.I₀
  let hcover : ⨆ i, coverOpens U i = ⊤ := U.openCover.iSup_opensRange
  let haff : ∀ i, IsAffineOpen (coverOpens U i) := fun i => isAffineOpen_opensRange (U.f i)
  let c : structureCocycles f U →ₗ[R] (relativeCohomology f 1).obj (unitModule X) :=
    (canonicalClass f (coverOpens U) hcover haff 0).comp (structureCocycleEquiv f U 0).toLinearMap
  have hc (z : structureCocycles f U) : c z = 0 ↔ z ∈ structureBoundaries f U := by
    change canonicalClass f (coverOpens U) hcover haff 0 (structureCocycleEquiv f U 0 z) = 0 ↔ _
    rw [canonicalClass_eq_zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(structureCochainEquiv f U 0).symm y, Subtype.ext ?_⟩
      change cechD U (functions f) 0 ((structureCochainEquiv f U 0).symm y) = z.val
      apply (structureCochainEquiv f U 1).injective
      rw [structureCochainEquiv_cechD, LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨structureCochainEquiv f U 0 y, (structureCochainEquiv_cechD f U 0 y).symm⟩
  exact (Submodule.quotEquivOfEq _ _ (Submodule.ext fun z => (hc z).symm)).trans
    (c.quotKerEquivOfSurjective
      ((canonicalClass_surjective f (coverOpens U) hcover haff 0).comp
        (structureCocycleEquiv f U 0).surjective))

omit [IsSeparated f] in
/-- Properness and coherence give finiteness of function Čech cohomology over a
Noetherian base. -/
theorem structureH1_finite [IsNoetherianRing R] [IsProper f] :
    Module.Finite R (structureH1 f U) := by
  have h := (properCoherentCohomologyFinite R X f inferInstance
    (unitModule X) inferInstance (fun _ => Module.Finite.self _)).1 1
  exact Module.Finite.equiv (structureH1Equiv f U).symm

end Langlands.AlgebraicGeometry.AffineCechDeRham
