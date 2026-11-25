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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionCanonicalComparisonIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionCanonicalComparisonUnique
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionFiltration
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore

/-! # Graded quotients of the convolution tensor filtration

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sec-additivity-of-trace-classes/
sk-i-additivity/sk-i-additivity.proof.md,
"Filtered operations", third graded identity and the sentence on Koszul signs
(blueprint: lem-trf-filtered-convolution-graded-quotient).

The helper predicates specify the convolution by its actual image sum and the comparison
by its composites with tensor quotient projections. They impose no chosen splitting on Q
and no differential-compatible splitting on P. All tensors are the existing total tensor
of cochain complexes, whose second differential has sign (-1)^i in cochain degree i.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules
namespace FilteredConvolution

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

/-- The convolution filtration level. -/
abbrev level {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (r : ℤ) : Subobject (P ⊗ Q) :=
  FilteredConvolutionCore.level F G r

/-- The direct sum of tensor products of the existing graded quotient complexes.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, third graded identity
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev gradedSource {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (r : ℤ) : Complex R :=
  ∐ (fun p : ℤ ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p))

/-- The canonical comparison predicate. -/
abbrev IsCanonical {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (H : DecreasingFiltration (P ⊗ Q)) (r : ℤ)
    (α : gradedSource F G r ⟶ H.gradedPiece r) : Prop :=
  FilteredConvolutionCore.IsCanonical F G H r α

/-- The graded quotient of the convolution filtration, for a termwise split filtration
with flat graded terms in the first factor and any finite filtration in the second.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, tensor identity
(blueprint: lem-trf-filtered-convolution-graded-quotient).

Proof:
1. Sums in module sheaves are exact: express them as filtered colimits of finite sums.
Tensor preserves sums and cokernels in both variables, the second by the sheaf tensor switch.
2. The tensor of the two quotient projections kills F^(p+1) tensor F^q and F^p tensor
F^(q+1). Both map into convolution level r+1. The two cokernel universal properties
therefore give the unique canonical comparison out of each graded tensor summand.
3. In each cochain degree i choose a splitting P^i = direct sum E_t^i, a <= t <= b,
compatible with its finite filtration. Successive split quotient projections supply it.
The E_t^i identify with the graded terms and are flat. No splitting respects d_P,
and none is chosen on Q.
4. In bidegree (i,j) the convolution level is the direct sum of
E_t^i tensor F^(r-t)Q^j: a generator with t >= p lands there by decreasingness,
and conversely use the generator p=t. Flatness makes these genuine subobjects.
5. Exactness of tensor with E_t^i identifies consecutive quotients with
E_t^i tensor gr^(r-t)Q^j. Sum in t and then along the possibly infinite cochain
diagonal i+j=n. Exactness of sums identifies the result with the source of alpha^n.
The resulting isomorphism sends the tensor of quotient classes to the class of the
tensor of representatives, so it is exactly the canonical comparison from step 2.
6. On homogeneous representatives both differentials give [dx tensor y] plus
(-1)^i [x tensor dy]. Thus alpha commutes with the total differential; its degreewise
inverse does too. There is no sign from the filtration weights.
7. Filtered maps send [x tensor y] to [f(x) tensor g(y)], giving naturality as stated
separately below. The same calculation covers zero complexes, one-step filtrations,
out-of-range weights and unbounded cochain degrees. -/
theorem graded_quotient
    (P Q : Complex R) (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (a b c d : ℤ) (hPa : F.F a = ⊤) (hPb : F.F (b + 1) = ⊥)
    (hQc : G.F c = ⊤) (hQd : G.F (d + 1) = ⊥)
    (hSplit : ∀ p n : ℤ, IsSplitEpi ((F.complexQuotientπ p (p + 1) (by omega)).f n))
    (hFlat : ∀ p n : ℤ, IsFlatOnSite (R := R) ((F.gradedPiece p).X n)) :
    ∃ H : DecreasingFiltration (P ⊗ Q),
      (∀ r : ℤ, H.F r = level F G r) ∧
      ∀ r : ℤ, ∃! α : gradedSource F G r ⟶ H.gradedPiece r,
        IsCanonical F G H r α ∧ IsIso α := by
  obtain ⟨H, hH⟩ :=
    FilteredConvolutionCore.convolution_filtration_exists P Q F G
  refine ⟨H, hH, ?_⟩
  intro r
  obtain ⟨α, hα, huniq⟩ :=
    FilteredConvolutionCore.canonical_comparison_unique F G H hH r
  have : IsIso α :=
    FilteredConvolutionCore.canonical_comparison_isIso F G a b c d hPa hPb hQc hQd
      hSplit hFlat H hH r α hα
  refine ⟨α, ⟨hα, inferInstance⟩, ?_⟩
  intro β hβ
  exact huniq β hβ.1

end FilteredConvolution
end SheafOfModules
