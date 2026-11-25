/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.SecondFiltrationRowCycleComparison

/-! # The signed row comparison for one concrete quotient page

Source: Stacks Project, Homology, Tag 0130, `lemma-ss-double-complex`, clauses 2 and 4,
and Tag 012K, the representative formula for a filtered-complex differential.
(blueprint: lem-sp-second-filtration-signed-first-page).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
private theorem row_cycle_total_d
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (r : ℕ) (s : ℤ) :
    let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
    let f := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))
    let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
      (ComplexShape.up ℤ)
    (R s).iCycles r ≫ secondFiltrationRowι F I r s ≫
        K.d (s + (r : ℤ)) ((s + 1) + (r : ℤ)) =
      (r : ℤ).negOnePow • (HomologicalComplex.cyclesMap f r ≫
        (R (s + 1)).iCycles r ≫ secondFiltrationRowι F I r (s + 1)) := by
  let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  dsimp only
  rw [secondFiltrationRowι, J.total_d, Preadditive.comp_add,
    Preadditive.comp_add]
  simp only [Category.assoc]
  rw [J.ι_D₁, J.ι_D₂]
  rw [J.d₁_eq (ComplexShape.up ℤ) (show
      (ComplexShape.up ℤ).Rel (r : ℤ) ((r : ℤ) + 1) from rfl) s
      ((s + 1) + (r : ℤ)) (by change (r : ℤ) + 1 + s = (s + 1) + (r : ℤ); omega),
    J.d₂_eq (ComplexShape.up ℤ) (r : ℤ) (show
      (ComplexShape.up ℤ).Rel s (s + 1) from rfl) ((s + 1) + (r : ℤ))
      (by change (r : ℤ) + (s + 1) = (s + 1) + (r : ℤ); omega)]
  simp only [Linear.comp_units_smul]
  change (1 : ℤˣ) • ((R s).iCycles r ≫
      ((R s).extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
      ((R s).extend ComplexShape.embeddingUpNat).d (r : ℤ) ((r : ℤ) + 1) ≫
      J.ιTotal (ComplexShape.up ℤ) ((r : ℤ) + 1) s ((s + 1) + (r : ℤ)) (by
        change (r : ℤ) + 1 + s = (s + 1) + (r : ℤ); omega)) +
    (r : ℤ).negOnePow • ((R s).iCycles r ≫
      ((R s).extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
      (HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1)))
        ComplexShape.embeddingUpNat).f (r : ℤ) ≫
      J.ιTotal (ComplexShape.up ℤ) (r : ℤ) (s + 1) ((s + 1) + (r : ℤ)) (by
        change (r : ℤ) + (s + 1) = (s + 1) + (r : ℤ); omega)) = _
  rw [one_smul, HomologicalComplex.extend_d_eq _ _ (by rfl)
      (show ComplexShape.embeddingUpNat.f (r + 1) = (r : ℤ) + 1 by simp),
    HomologicalComplex.extendMap_f _ _ (by rfl)]
  dsimp only [R]
  simp only [Iso.inv_hom_id_assoc, HomologicalComplex.iCycles_d_assoc, zero_comp,
    zero_add, HomologicalComplex.cyclesMap_i_assoc, secondFiltrationRowι, Category.assoc]
  rfl

/-- The first concrete cycle/boundary quotient page is row cohomology, and the
representative differential carries the totalization sign. This concerns a single
page with specified differential, without constructing a spectral sequence or
asserting anything about higher pages.
Source: Stacks Project, Homology, Tag 0130, `lemma-ss-double-complex`, clauses 2 and 4,
and Tag 012K, the displayed representative differential formula.
(blueprint: lem-sp-second-filtration-signed-first-page).

Proof. Write J for the flipped mapped bicomplex and n = s+r. The diagonal
coprojection from J^(r,s) lifts to the filtration step L^s in degree n. Modulo
L^(s+1), the other diagonal summands disappear. Projecting this lift gives the
canonical isomorphism from J^(r,s) to gr^s L in degree n: its inverse is the
projection onto that summand, which kills every summand in L^(s+1). These maps
are inverse by the coproduct universal property. The total differential on
J^(r,s) has a resolution component and a complex-index component; the latter
lands in L^(s+1), so the graded differential is the resolution differential.
Thus its kernel and image identify with the row cycles and boundaries. The
first filtered cycles and boundaries are exactly that kernel and image.
Taking their cokernel identifies the actual object filteredComplexPageObject
at (s,r) with row cohomology. Extension by zero from the natural numbers
preserves cohomology in degree r, including degree zero.

To compute the differential, restrict the same diagonal lift to row cycles.
Its resolution component is zero. Its remaining total differential is
(-1)^r times the complex-index map J^(r,s) to J^(r,s+1). This is again a row
cycle since the bicomplex differentials commute. Apply D.on_representatives
with these two lifts and their graded cycle classes. The result is the desired
equation after precomposition with the epic row-cycles-to-homology projection;
cancel that epimorphism. Row boundaries map to row boundaries because the
complex-index differential is a row chain map, so the induced map is exactly
HomologicalComplex.homologyMap of F(I.d s (s+1)). Scalars commute with the
quotient projections by preadditivity. The construction uses only the
specified representative differential and the diagonal coprojections, not any
choice of arbitrary isomorphisms between page objects. -/
theorem secondFiltration_signed_firstPage
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (D : FilteredComplexPageDifferential
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)) L 1) :
    ∃ e : ∀ (r : ℕ) (s : ℤ), D.page.X (s, (r : ℤ)) ≅
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).homology r,
      ∀ (r : ℕ) (s : ℤ),
        D.page.d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e r (s + 1)).hom =
          (r : ℤ).negOnePow • ((e r s).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r) := by
  obtain ⟨e, t, x, ht, hx, he⟩ := secondFiltration_row_cycle_comparison F I hbelow L hL
  refine ⟨e, ?_⟩
  intro r s
  let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
    (ComplexShape.up ℤ)
  let f := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))
  let z := (r : ℤ).negOnePow
  let c := HomologicalComplex.cyclesMap f r
  let π := filteredComplexPageπ K L 1 (s, (r : ℤ))
  have hrep := D.on_representatives ((R s).cycles r) (s, (r : ℤ))
    (s + 1, (r : ℤ)) (by
      change (s, (r : ℤ)) + (1, 1 - 1) = (s + 1, (r : ℤ))
      ext <;> simp)
    (t r s) (z • (c ≫ t r (s + 1)))
    (x r s) (z • (c ≫ x r (s + 1)))
    (by
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [reassoc_of% (ht r s), ht r (s + 1)]
      exact row_cycle_total_d F I r s)
    (hx r s)
    (by simp only [Linear.units_smul_comp, Category.assoc, hx r (s + 1)])
  have hπ : Epi (x r s ≫ π) := by
    apply (epi_comp_iff_of_isIso (x r s ≫ π) (e r s).hom).mp
    rw [Category.assoc, he r s]
    infer_instance
  apply (cancel_epi (x r s ≫ π)).1
  change (x r s ≫ π) ≫ D.d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫
      (e r (s + 1)).hom =
    (x r s ≫ π) ≫ (z • ((e r s).hom ≫ HomologicalComplex.homologyMap f r))
  calc
    (x r s ≫ π) ≫ D.d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫
        (e r (s + 1)).hom =
      (z • (c ≫ x r (s + 1))) ≫
        filteredComplexPageπ K L 1 (s + 1, (r : ℤ)) ≫ (e r (s + 1)).hom := by
          simpa only [Category.assoc] using
            congrArg (fun g ↦ g ≫ (e r (s + 1)).hom) hrep
    _ = z • (c ≫ (R (s + 1)).homologyπ r) := by
      dsimp only [K]
      simp only [Linear.units_smul_comp, Category.assoc, he r (s + 1)]
      rfl
    _ = z • ((R s).homologyπ r ≫ HomologicalComplex.homologyMap f r) := by
      rw [HomologicalComplex.homologyπ_naturality]
    _ = (x r s ≫ π) ≫ (z • ((e r s).hom ≫ HomologicalComplex.homologyMap f r)) := by
      simp only [Linear.comp_units_smul, ← Category.assoc]
      rw [Category.assoc (x r s) π, he r s]

end CategoryTheory.Functor
