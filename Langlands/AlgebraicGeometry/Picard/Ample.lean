import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Modules.SectionResidueStatements
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Section generation loci and ampleness of line bundles

The generation locus of a global section is the published trivialization open:
the largest open subscheme on which the morphism from the structure sheaf sending
one to the section is an isomorphism. Ampleness asks for a quasi-compact scheme
whose points all lie in affine generation loci of sections of positive tensor powers.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule

variable {X : Scheme.{u}} (M : X.Modules) (s : GlobalSections M)

/-- A point lies in the trivialization open iff the section trivializes near it. -/
theorem mem_trivializationOpen_iff {x : X} :
    x ∈ trivializationOpen M s ↔ ∃ U : X.Opens, x ∈ U ∧ TrivializesOn M s U := by
  unfold trivializationOpen
  rw [Opens.mem_sSup]
  exact ⟨fun ⟨U, hU, hx⟩ ↦ ⟨U, hx, hU⟩, fun ⟨U, hx, hU⟩ ↦ ⟨U, hU, hx⟩⟩

/-- A point lies in the trivialization open iff it has a neighborhood of stalk frames. -/
theorem mem_trivializationOpen_iff_stalk {x : X} :
    x ∈ trivializationOpen M s ↔ ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsStalkFrame M s y := by
  rw [mem_trivializationOpen_iff]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ localStalkCriterion X M s U

/-- The section trivializes the module on its whole trivialization open. -/
theorem trivializesOn_trivializationOpen : TrivializesOn M s (trivializationOpen M s) :=
  (maximalTrivialization X M s _).mpr le_rfl

/-- The local trivialization induced by the section on its trivialization open. -/
noncomputable def trivializationOpenIso :
    SheafOfModules.unit (trivializationOpen M s).toScheme.ringCatSheaf ≅
      M.restrict (trivializationOpen M s).ι :=
  (Scheme.Modules.restrictUnitIso (trivializationOpen M s).ι).symm ≪≫
    @asIso _ _ _ _ ((Scheme.Modules.restrictFunctor (trivializationOpen M s).ι).map
      (sectionHom M s)) (trivializesOn_trivializationOpen M s)

/-- The local trivialization is the restriction of the section's morphism. -/
theorem trivializationOpenIso_hom :
    (trivializationOpenIso M s).hom =
      (Scheme.Modules.restrictUnitIso (trivializationOpen M s).ι).inv ≫
        (Scheme.Modules.restrictFunctor (trivializationOpen M s).ι).map (sectionHom M s) :=
  rfl

/-- If the line-bundle residue comparison holds, then for a locally free rank-one module
the trivialization open is the whole stalk-frame locus. -/
theorem coe_trivializationOpen_eq_setOf_isStalkFrame
    (h : LineBundleSectionResidueComparison.{u})
    (hM : Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne M) :
    (trivializationOpen M s : Set X) = {x | IsStalkFrame M s x} := by
  ext x
  refine ⟨fun hx ↦ isStalkFrame_of_mem_trivializationOpen M s hx, fun hx ↦ ?_⟩
  have hn : x ∈ nonvanishingLocus M s := (h.1 X ⟨M, hM⟩ s x).mpr hx
  rw [h.2 X ⟨M, hM⟩ s] at hn
  exact hn

/-- If the line-bundle residue open comparison holds, then for a locally free rank-one
module the trivialization open is the residue-field nonvanishing locus. -/
theorem coe_trivializationOpen_eq_nonvanishingLocus
    (h : LineBundleResidueOpenComparison.{u})
    (hM : Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne M) :
    (trivializationOpen M s : Set X) = nonvanishingLocus M s :=
  (h X ⟨M, hM⟩ s).symm

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

namespace LineBundle

variable {X : Scheme.{u}} (L : LineBundle X)

/-- Global sections of the actual `n`-th tensor power of a line bundle. -/
noncomputable abbrev powSections (n : ℕ) :=
  GlobalSections (tensorPow L.obj n)

/-- The generation locus `X_s` of a section of the `n`-th tensor power. -/
noncomputable abbrev sectionOpen {n : ℕ} (s : L.powSections n) : X.Opens :=
  trivializationOpen (tensorPow L.obj n) s

/-- The generation locus `X_s` as an actual open subscheme. -/
noncomputable abbrev sectionSubscheme {n : ℕ} (s : L.powSections n) : Scheme.{u} :=
  trivializationSubscheme (tensorPow L.obj n) s

/-- The open immersion of the generation locus `X_s` into `X`. -/
noncomputable abbrev sectionInclusion {n : ℕ} (s : L.powSections n) : L.sectionSubscheme s ⟶ X :=
  trivializationInclusion (tensorPow L.obj n) s

/-- A line bundle is ample if the scheme is quasi-compact and every point lies in the
generation locus of a section of a positive tensor power whose whole locus is affine. -/
def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
    x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s)

/-- Affineness of the generation locus means its actual open subscheme is affine. -/
theorem isAffineOpen_sectionOpen_iff {n : ℕ} (s : L.powSections n) :
    IsAffineOpen (L.sectionOpen s) ↔ IsAffine (L.sectionSubscheme s) :=
  Iff.rfl

variable {L}

/-- The underlying scheme of an ample line bundle is quasi-compact. -/
theorem IsAmple.compactSpace (hL : L.IsAmple) : CompactSpace X :=
  hL.1

/-- Every point lies in the affine generation locus of a section of a positive power. -/
theorem IsAmple.exists_section (hL : L.IsAmple) (x : X) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s) :=
  hL.2 x

/-- Under rank one of the tensor powers and the residue open comparison, ampleness is
the residue-field nonvanishing formulation. -/
theorem isAmple_iff_nonvanishingLocus (h : LineBundleResidueOpenComparison.{u})
    (hpow : ∀ n : ℕ, IsLocallyFreeRankOne (tensorPow L.obj n)) :
    L.IsAmple ↔ CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      x ∈ nonvanishingLocus (tensorPow L.obj n) s ∧
        ∃ U : X.Opens, (U : Set X) = nonvanishingLocus (tensorPow L.obj n) s ∧
          IsAffineOpen U := by
  refine and_congr_right fun _ ↦ forall_congr' fun x ↦ exists_congr fun n ↦
    and_congr_right fun _ ↦ exists_congr fun s ↦ ?_
  have hs := coe_trivializationOpen_eq_nonvanishingLocus (tensorPow L.obj n) s h (hpow n)
  constructor
  · rintro ⟨hx, ha⟩
    refine ⟨?_, L.sectionOpen s, hs, ha⟩
    rw [← hs]
    exact hx
  · rintro ⟨hx, U, hU, ha⟩
    have hU' : U = L.sectionOpen s := SetLike.coe_injective (hU.trans hs.symm)
    subst hU'
    refine ⟨?_, ha⟩
    show x ∈ (L.sectionOpen s : Set X)
    rw [hs]
    exact hx

end LineBundle

end Langlands.AlgebraicGeometry.Picard
