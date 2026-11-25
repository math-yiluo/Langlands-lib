/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse

/-! Core definitions for the convolution filtration and its graded source. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules
namespace FilteredConvolutionCore

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The recorded general-site module category, with coefficient-sized modules.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- Integer cochain complexes in the recorded category of module sheaves.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev Complex (R : Sheaf J CommRingCat.{w}) := CochainComplex (Modules R) ℤ

/-- The actual sum of images of F^p P tensor F^(r-p) Q inside the total tensor complex.
The integers p enumerate exactly the pairs (p,q) with p+q=r.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, tensor convolution
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
def level {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (r : ℤ) : Subobject (P ⊗ Q) :=
  imageSubobject (Sigma.desc (fun p : ℤ ↦
    (F.F p).arrow ⊗ₘ (G.F (r - p)).arrow))

/-- The direct sum of tensor products of the existing graded quotient complexes.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, third graded identity
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev gradedSource {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (r : ℤ) : Complex R :=
  ∐ (fun p : ℤ ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p))

/-- The canonical comparison is characterized on every filtered tensor summand.
The lift lands in the r-th convolution step and its composite with the quotient is alpha
after tensoring the two quotient projections. Thus this specifies the canonical map,
independently of any splitting; the lift itself is unique by the subobject monomorphism.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, third graded identity
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
def IsCanonical {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (H : DecreasingFiltration (P ⊗ Q)) (r : ℤ)
    (α : gradedSource F G r ⟶ H.gradedPiece r) : Prop :=
  ∀ p : ℤ, ∃ t : ((F.F p : Complex R) ⊗ (G.F (r - p) : Complex R)) ⟶ (H.F r : Complex R),
    t ≫ (H.F r).arrow = (F.F p).arrow ⊗ₘ (G.F (r - p)).arrow ∧
    (F.complexQuotientπ p (p + 1) (by omega) ⊗ₘ
      G.complexQuotientπ (r - p) (r - p + 1) (by omega)) ≫
        Sigma.ι (fun p : ℤ ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p)) p ≫ α =
      t ≫ H.complexQuotientπ r (r + 1) (by omega)


end FilteredConvolutionCore
end SheafOfModules
