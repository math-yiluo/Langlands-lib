/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.RingTheory.CurveBranches

/-!
# The punctured spectrum of a strictly henselian local curve

For a reduced one-dimensional strictly henselian excellent local ring `R`, the punctured spectrum
`Spec R ∖ {𝔪}` is the finite disjoint union `∐ₐ Spec Frac(B(R)ₐ)` of the spectra of the fraction
fields of the branches `B(R)ₐ` (`IsLocalRing.branch`), which are excellent strictly henselian
discrete valuation rings with the residue field of `R` (blueprint
`lem-exc-punctured-curve-branches`).
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- The punctured spectrum `Spec R ∖ {𝔪}` of a local ring, as an open subscheme of `Spec R`. -/
def puncturedSpectrum [IsLocalRing R] : (Spec (CommRingCat.of R)).Opens :=
  ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩

/-- The fraction field of the branch `B(R)ₐ`, as a commutative ring. -/
abbrev branchFractionField (p : minimalPrimes R) : CommRingCat.{u} :=
  .of (FractionRing (branch R p))

variable {R}

/-- For `f` cutting out the punctured spectrum (`IsLocalRing.notMem_iff_ne_maximalIdeal`) with
`R_f = Q(R)`, the punctured spectrum is `∐ₐ Spec Frac(B(R)ₐ)`. -/
noncomputable def puncturedSpectrumIsoOfIsLocalization [IsLocalRing R] {f : R}
    (hf : ∀ q : Ideal R, q.IsPrime → (f ∉ q ↔ q ≠ maximalIdeal R))
    [IsLocalization.Away f (branchFractionRing R)] [Finite (minimalPrimes R)] :
    (puncturedSpectrum R).toScheme ≅ ∐ fun p ↦ Spec (branchFractionField R p) :=
  have h : puncturedSpectrum R = PrimeSpectrum.basicOpen (R := CommRingCat.of R) f := by
    ext x
    change x ≠ closedPoint R ↔ f ∉ x.asIdeal
    rw [hf x.asIdeal x.2, ne_eq, ne_eq, not_iff_not]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ PrimeSpectrum.ext h⟩
  let ψ : Localization.Away f ≃ₐ[R] ∀ p, FractionRing (branch R p) :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      (branchFractionRing R)).trans
      (AlgEquiv.piCongrRight fun p ↦ ((IsLocalization.algEquiv (nonZeroDivisors (branch R p))
        (FractionRing (R ⧸ p.1)) (FractionRing (branch R p))).restrictScalars R))
  (Spec (CommRingCat.of R)).isoOfEq h ≪≫ basicOpenIsoSpecAway (R := CommRingCat.of R) f ≪≫
    (Scheme.Spec.mapIso ψ.toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (asIso (sigmaSpec (branchFractionField R))).symm

lemma ι_puncturedSpectrumIsoOfIsLocalization_inv [IsLocalRing R] {f : R}
    (hf : ∀ q : Ideal R, q.IsPrime → (f ∉ q ↔ q ≠ maximalIdeal R))
    [IsLocalization.Away f (branchFractionRing R)] [Finite (minimalPrimes R)]
    (p : minimalPrimes R) :
    Sigma.ι _ p ≫ (puncturedSpectrumIsoOfIsLocalization hf).inv ≫ (puncturedSpectrum R).ι =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing (branch R p)))) := by
  simp only [puncturedSpectrumIsoOfIsLocalization, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Category.assoc, Scheme.isoOfEq_inv_ι, ι_sigmaSpec_assoc]
  rw [(Iso.inv_comp_eq _).2 (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) f).symm]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
    ← Spec.map_comp]
  congr 2
  ext r
  simp [AlgEquiv.commutes]

/-- Blueprint `lem-exc-punctured-curve-branches`: The punctured strictly local curve has DVR
branches.

Let `R` be a reduced excellent one-dimensional local ring which is henselian with algebraically
closed residue field (i.e. strictly henselian; the residue characteristic plays no role). Then
each branch `B(R)ₐ = \overline{R/pₐ}` (`IsLocalRing.branch`, the factors of the branch algebra
`B(R)`) is a finite `R / pₐ`-module and an excellent henselian discrete valuation ring whose
residue field is the (algebraically closed) residue field of `R`, and the punctured spectrum
`Spec R ∖ {𝔪}` is isomorphic to the finite disjoint union `∐ₐ Spec Frac(B(R)ₐ)`, compatibly with
the maps to `Spec R` induced by `R → Frac(B(R)ₐ)`. (The ring-level statement is
`IsLocalRing.branches_and_punctured_spectrum`.) -/
theorem puncturedSpectrum_branches (hR : IsExcellentRing R) [HenselianLocalRing R]
    [IsReduced R] [IsAlgClosed (ResidueField R)] (hdim : ringKrullDim R = 1) :
    (∀ p : minimalPrimes R, Module.Finite (R ⧸ p.1) (branch R p) ∧
      IsExcellentRing (branch R p) ∧
      IsDiscreteValuationRing (branch R p) ∧ HenselianLocalRing (branch R p) ∧
      (letI := isLocalRing_branch p;
        IsAlgClosed (ResidueField (branch R p)) ∧
          ∀ b : branch R p, ∃ r : R, b - algebraMap R (branch R p) r ∈ maximalIdeal _)) ∧
    Finite (minimalPrimes R) ∧
    ∃ e : (puncturedSpectrum R).toScheme ≅ ∐ fun p ↦ Spec (branchFractionField R p),
      ∀ p, Sigma.ι _ p ≫ e.inv ≫ (puncturedSpectrum R).ι =
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing (branch R p)))) := by
  obtain ⟨hbr, f, -, hf, hloc⟩ := branches_and_punctured_spectrum hR hdim
  have := hR.isNoetherianRing
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  refine ⟨fun p ↦ ⟨(hbr p).1, (hbr p).2.1, (hbr p).2.2.1, (hbr p).2.2.2.1,
    (hbr p).2.2.2.2.2⟩, this, puncturedSpectrumIsoOfIsLocalization hf,
    ι_puncturedSpectrumIsoOfIsLocalization_inv hf⟩

end AlgebraicGeometry
