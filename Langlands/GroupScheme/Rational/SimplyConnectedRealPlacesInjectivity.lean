import Langlands.GroupScheme.Rational.NumberFieldHasseGaloisReduction
import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.Global.FiniteCompletionLocalField

/-! # From the all-place Hasse principle to real-place injectivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

private theorem cohomologous_of_isTrivial {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    {c d : Cocycle G U} (hc : c.IsTrivial) (hd : d.IsTrivial) : c.Cohomologous d := by
  obtain ⟨f, hf⟩ := hc
  obtain ⟨g, hg⟩ := hd
  refine ⟨f * g⁻¹, fun x y => ?_⟩
  simp only [Cocycle.twist, MonObj.comp_mul, GrpObj.comp_inv, hf, hg]
  group

private theorem isAlgClosed_of_complexRingEquiv {K : Type u} [Field K]
    (e : K ≃+* ℂ) : IsAlgClosed K := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom p
    (ne_of_gt (Polynomial.degree_pos_of_irreducible hp))
  refine ⟨e.symm x, e.injective ?_⟩
  change e.toRingHom (p.eval (e.symm x)) = e.toRingHom 0
  rw [← Polynomial.eval₂_at_apply, map_zero]
  simpa using hx

section FieldCovers

variable {F K L : Type u} [Field F] [Field K] [Field L] [Algebra F L] [Algebra F K]
  [FiniteDimensional F L]

/-- At an algebraically closed extension of the base field, the pulled-back cover has a
section. Its cocycles are coboundaries, with no conditions on the coefficient group. -/
private theorem isTrivial_pullback_of_isAlgClosed [IsAlgClosed K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (c : Cocycle G ((Over.pullback (algebraBaseMap F K)).obj (ringTest F L))) :
    c.IsTrivial := by
  let b := algebraBaseMap F K
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let p : (Over.map b).obj P ⟶ ringTest F K := Over.homMk (𝟙 _) (by simp [P, b, ringTest])
  let e : L →ₐ[F] K := IsAlgClosed.lift
  exact Cocycle.isTrivial_of_section c ((Over.mapPullbackAdj b).homEquiv _ _ (p ≫ ringTestMap F e))

/-- A cocycle on the pulled-back cover of a finite field extension becomes trivial if all
cocycles on finite separable field covers of the new base vanish. A residue field of the
finite tensor algebra supplies a field cover through which to apply that premise. -/
private theorem isTrivial_pullback_of_fieldCovers [CharZero K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (h : ∀ (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]
      [Algebra.IsSeparable K E], ∀ d : Cocycle G (ringTest K E), d.IsTrivial)
    (c : Cocycle G ((Over.pullback (algebraBaseMap F K)).obj (ringTest F L))) :
    c.IsTrivial := by
  let A := K ⊗[F] L
  let : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F K L
      (algebraMap F K).injective (algebraMap F L).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let E := A ⧸ m
  let : Field E := Ideal.Quotient.field m
  let : FiniteDimensional K E := inferInstanceAs (Module.Finite K (A ⧸ m))
  let e : L →ₐ[F] E := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  let b := algebraBaseMap F K
  let p : (Over.map b).obj (ringTest K E) ⟶ ringTest F E :=
    Over.homMk (𝟙 _) (by
      change 𝟙 (Spec (CommRingCat.of E)) ≫ algebraBaseMap F E =
        algebraBaseMap K E ≫ algebraBaseMap F K
      unfold algebraBaseMap
      rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        IsScalarTower.algebraMap_eq F K E])
  let r : ringTest K E ⟶ (Over.pullback b).obj (ringTest F L) :=
    (Over.mapPullbackAdj b).homEquiv _ _ (p ≫ ringTestMap F e)
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc K E
  let : Surjective (ringTest K E).hom := hs
  let : Flat (ringTest K E).hom := hf
  let : QuasiCompact (ringTest K E).hom := hq
  exact (h E (c.refine r)).of_refine_fpqcCover r

end FieldCovers

/-- Localization at the real places detects cohomology of two cocycles on the same finite
separable field cover for semisimple simply connected groups over number fields. This is the
injectivity clause of `SimplyConnectedRealPlacesCohomologyStatement`. -/
def SimplyConnectedRealPlacesInjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ ζ : Cocycle G (ringTest F L)),
      (∀ w : InfinitePlace F, w.IsReal →
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w))
        let r := (Over.mapPullbackAdj b).counit.app (ringTest F L)
        (ξ.baseChange b _ r).Cohomologous (ζ.baseChange b _ r)) →
      ξ.Cohomologous ζ

/-- For a simply connected group, real-place cohomology comparisons imply the
corresponding comparisons over every completion. -/
def SimplyConnectedRealToAllPlacesComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L]
      (ξ ζ : Cocycle G (ringTest F L)),
      (∀ w : InfinitePlace F, w.IsReal →
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w))
        let r := (Over.mapPullbackAdj b).counit.app (ringTest F L)
        (ξ.baseChange b _ r).Cohomologous (ζ.baseChange b _ r)) →
      ξ.LocallyCohomologous ζ

theorem simplyConnectedRealToAllPlacesComparison :
    SimplyConnectedRealToAllPlacesComparisonStatement.{u} := by
  intro F _ _ G hG L _ _ _ ξ ζ hreal i
  rcases i with w | v
  · by_cases hw : w.IsReal
    · exact hreal w hw
    · let K := w.Completion
      let b := algebraBaseMap F K
      let r := (Over.mapPullbackAdj b).counit.app (ringTest F L)
      let : IsAlgClosed K := isAlgClosed_of_complexRingEquiv
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      exact cohomologous_of_isTrivial
        (isTrivial_pullback_of_isAlgClosed (ξ.baseChange b _ r))
        (isTrivial_pullback_of_isAlgClosed (ζ.baseChange b _ r))
  · let K := Langlands.Global.FiniteCompletion F v
    let b := algebraBaseMap F K
    let r := (Over.mapPullbackAdj b).counit.app (ringTest F L)
    let : ValuativeRel K := Langlands.Global.FiniteCompletion.valuativeRel v
    let : IsNonarchimedeanLocalField K := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    have hGK : IsSimplyConnected ((baseChange b).obj G) :=
      isSimplyConnectedFieldExtension F K G hG
    let : IsAffineHom ((baseChange b).obj G).X.hom := hGK.isSemisimple.isConnectedReductive.isAffineHom
    have h := localSimplyConnectedCocycleVanishing K ((baseChange b).obj G) hGK
    exact cohomologous_of_isTrivial
      (isTrivial_pullback_of_fieldCovers h (ξ.baseChange b _ r))
      (isTrivial_pullback_of_fieldCovers h (ζ.baseChange b _ r))

/-- The all-place Hasse principle implies real-place injectivity. -/
theorem simplyConnectedRealPlacesInjectivity_of_hasse
    (hasse : NumberFieldHassePrincipleStatement.{u}) :
    SimplyConnectedRealPlacesInjectivityStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ ζ hreal
  exact hasse F G (Or.inl hG) L ξ ζ
    (simplyConnectedRealToAllPlacesComparison F G hG L ξ ζ hreal)

end Langlands.GroupScheme
