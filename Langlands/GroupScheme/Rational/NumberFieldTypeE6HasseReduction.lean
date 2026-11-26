import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Rational.NumberFieldHasseInflation
import Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # The type `E_6` Hasse kernel from totally complex fields and quadratic covers

This module states two cases of the Hasse principle for simply connected absolutely
almost-simple groups of type `E_6` over number fields: vanishing of every cocycle over a
totally complex number field, and the Hasse kernel on a totally complex quadratic cover. It
proves that the two statements together give `NumberFieldTypeE6HasseStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IntermediateField Polynomial

namespace Langlands.GroupScheme

/-- Over a totally complex number field, every cocycle of a simply connected absolutely
almost-simple group of type `E_6`, inner or outer, on a finite Galois field cover is
trivial. -/
def NumberFieldTotallyComplexTypeE6VanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], NumberField.IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

/-- The localization kernel of a simply connected absolutely almost-simple group of type
`E_6` on a quadratic Galois cover `E/F` whose field `E` is totally complex. -/
def NumberFieldTypeE6QuadraticHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (E : Type u) [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
      [IsGalois F E], Module.finrank F E = 2 → NumberField.IsTotallyComplex E →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F E), ξ.LocallyTrivial → ξ.IsTrivial

namespace TypeE6HasseReduction

variable (F : Type u) [Field F]

/-- The separable closure of a field of characteristic zero contains a square root of `-1`. -/
theorem exists_sq_eq_neg_one [CharZero F] : ∃ i : SeparableClosure F, i ^ 2 = -1 :=
  IsAlgClosed.exists_pow_nat_eq (-1 : SeparableClosure F) two_pos

/-- A field with a real place contains no square root of `-1`. -/
theorem sq_ne_neg_one_of_isReal [NumberField F] {w : NumberField.InfinitePlace F}
    (hw : w.IsReal) (x : F) : x ^ 2 ≠ -1 := by
  intro hx
  have h := congrArg (NumberField.InfinitePlace.embedding_of_isReal hw) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (NumberField.InfinitePlace.embedding_of_isReal hw x)]

/-- A number field containing a square root of `-1` is totally complex. -/
theorem isTotallyComplex_of_sq_eq_neg_one [NumberField F] {x : F} (hx : x ^ 2 = -1) :
    NumberField.IsTotallyComplex F :=
  ⟨fun _ => NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
    (fun hw => sq_ne_neg_one_of_isReal F hw x hx)⟩

variable [NumberField F]

/-- A chosen square root of `-1` in the separable closure. -/
def sqrtNegOne : SeparableClosure F := (exists_sq_eq_neg_one F).choose

theorem sqrtNegOne_sq : sqrtNegOne F ^ 2 = -1 := (exists_sq_eq_neg_one F).choose_spec

/-- The field `F(√-1)` inside the separable closure of `F`. -/
abbrev gaussField : IntermediateField F (SeparableClosure F) := F⟮sqrtNegOne F⟯

theorem isIntegral_sqrtNegOne : IsIntegral F (sqrtNegOne F) :=
  Algebra.IsIntegral.isIntegral _

instance : FiniteDimensional F (gaussField F) :=
  adjoin.finiteDimensional (isIntegral_sqrtNegOne F)

instance : NumberField (gaussField F) := NumberField.of_module_finite F _

theorem isTotallyComplex_gaussField : NumberField.IsTotallyComplex (gaussField F) := by
  refine isTotallyComplex_of_sq_eq_neg_one (gaussField F)
    (x := ⟨sqrtNegOne F, mem_adjoin_simple_self F _⟩) ?_
  apply Subtype.ext
  simp [sqrtNegOne_sq]

/-- If `F` has a real place, then `F(√-1)` is quadratic over `F`. -/
theorem finrank_gaussField (hF : ¬ NumberField.IsTotallyComplex F) :
    Module.finrank F (gaussField F) = 2 := by
  obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace F, w.IsReal := by
    by_contra h
    exact hF ⟨fun w => NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
      (fun hw => h ⟨w, hw⟩)⟩
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by
    compute_degree!
  have hmonic : (X ^ 2 + 1 : F[X]).Monic := by
    monicity!
  have hirr : Irreducible (X ^ 2 + 1 : F[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => ?_
    apply sq_ne_neg_one_of_isReal F hw x
    have hx' : x ^ 2 + 1 = 0 := by simpa using hx
    linear_combination hx'
  have hmin := minpoly.eq_of_irreducible_of_monic (x := sqrtNegOne F) hirr
    (by simp [sqrtNegOne_sq]) hmonic
  rw [adjoin.finrank (isIntegral_sqrtNegOne F), ← hmin, hdeg]

theorem isGalois_gaussField (h : Module.finrank F (gaussField F) = 2) :
    IsGalois F (gaussField F) := by
  have : Algebra.IsQuadraticExtension F (gaussField F) := ⟨h⟩
  have : Algebra.IsSeparable F (gaussField F) :=
    Algebra.isSeparable_tower_bot_of_isSeparable F (gaussField F) (SeparableClosure F)
  infer_instance

/-- Two finite Galois extensions embed into a common finite Galois extension. -/
theorem exists_common_galois (L E : Type u) [Field L] [Field E] [Algebra F L] [Algebra F E]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F E] [IsGalois F E] :
    ∃ (M : IntermediateField F (SeparableClosure F)) (_ : L →ₐ[F] M) (_ : E →ₐ[F] M),
      FiniteDimensional F M ∧ IsGalois F M := by
  let φL : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φE : E →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let eL := AlgEquiv.ofInjectiveField φL
  let eE := AlgEquiv.ofInjectiveField φE
  have : FiniteDimensional F φL.fieldRange := LinearEquiv.finiteDimensional eL.toLinearEquiv
  have : FiniteDimensional F φE.fieldRange := LinearEquiv.finiteDimensional eE.toLinearEquiv
  have : Normal F φL.fieldRange := Normal.of_algEquiv eL
  have : Normal F φE.fieldRange := Normal.of_algEquiv eE
  let M := φL.fieldRange ⊔ φE.fieldRange
  have : Algebra.IsSeparable F M :=
    Algebra.isSeparable_tower_bot_of_isSeparable F M (SeparableClosure F)
  exact ⟨M, (IntermediateField.inclusion le_sup_left).comp eL.toAlgHom, (IntermediateField.inclusion le_sup_right).comp eE.toAlgHom,
    inferInstance, ⟨⟩⟩

/-- The algebra structure of the separable closure of an intermediate field. -/
local instance closureAlgebra (E : IntermediateField F (SeparableClosure F)) :
    Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

/-- The separable closure of `F` is a separable closure of each intermediate field. -/
def closureEquiv (E : IntermediateField F (SeparableClosure F)) :
    SeparableClosure E ≃ₐ[E] SeparableClosure F :=
  haveI : IsSepClosure E (SeparableClosure F) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable F E (SeparableClosure F)⟩
  IsSepClosure.equiv E (SeparableClosure E) (SeparableClosure F)

end TypeE6HasseReduction

open TypeE6HasseReduction

set_option backward.isDefEq.respectTransparency false in
/-- The type `E_6` Hasse kernel follows from vanishing over totally complex number fields
and the kernel on totally complex quadratic covers. Over a field with a real place, the
cocycle becomes trivial over `F(√-1)`, and inflation–restriction reduces it to the
quadratic cover `F(√-1)/F`. -/
theorem numberFieldTypeE6Hasse_of_totallyComplex_quadratic
    (hTI : NumberFieldTotallyComplexTypeE6VanishingStatement.{u})
    (hQ : NumberFieldTypeE6QuadraticHasseStatement.{u}) :
    NumberFieldTypeE6HasseStatement.{u} := by
  intro F _ _ G _ _ d e hsc habs hcar L _ _ _ _ ξ hξ
  by_cases hF : NumberField.IsTotallyComplex F
  · exact hTI F hF G d e hsc habs hcar L ξ
  let E := gaussField F
  have hfin : Module.finrank F E = 2 := finrank_gaussField F hF
  have : IsGalois F E := isGalois_gaussField F hfin
  have hEc : NumberField.IsTotallyComplex E := isTotallyComplex_gaussField F
  let : Algebra E (SeparableClosure E) := closureAlgebra F E
  let sse := d.separableScalarExtension E (closureEquiv F E)
  let GE := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
  have : IsAffineHom GE.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
    infer_instance
  have : LocallyOfFiniteType GE.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
    infer_instance
  have hscE : IsSimplyConnected GE := isSimplyConnectedFieldExtension F E G hsc
  have habsE : IsAbsolutelyAlmostSimple GE := habs.baseChange_of_algebraicExtension
  let eE : sse.index.Vertex ≃ Fin 6 := sse.vertices.symm.trans e
  have hcarE : ∀ a b, sse.index.cartan a b = CartanMatrix.E 6 (eE a) (eE b) := by
    intro a b
    have h := sse.cartan_eq (sse.vertices.symm a) (sse.vertices.symm b)
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    exact hcar _ _
  obtain ⟨M, φL, φE, hMfin, hMgal⟩ := exists_common_galois F L E
  let : Algebra L M := φL.toRingHom.toAlgebra
  let : Algebra E M := φE.toRingHom.toAlgebra
  let : Module E M := Algebra.toModule
  let : Module L M := Algebra.toModule
  have : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq (fun x => (φL.commutes x).symm)
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq (fun x => (φE.commutes x).symm)
  have : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have hE : (ξ.baseChangePullback (Spec.algebraMap F E)).IsTrivial :=
    GaloisCocycle.isTrivial_baseChange_of_scalarExtension (M := M) ξ
      (hTI E hEc GE sse.index eE hscE habsE hcarE M _)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel M ξ hξ hE
    (hQ F G d e hsc habs hcar E hfin hEc)

end Langlands.GroupScheme
