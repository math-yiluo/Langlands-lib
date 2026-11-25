/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.InternalModuleSectionwiseShortExact
import WeilConjectures.NumberTheory.Padics.Extension

/-! # A rank-one point resolution of the actual uniformizer quotient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

open Opposite MonoidalCategory

private def multiplicationHom (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (r : O) :
    Mod.regular (Profinite.continuousMapRingObj.{u} O) ⟶
      Mod.regular (Profinite.continuousMapRingObj.{u} O) := by
  let : MonObj (Profinite.continuousMapRingObj.{u} O).obj := inferInstanceAs
    (MonObj (Profinite.continuousMapRingPresheaf O ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1}))
  let m : Profinite.continuousMapRingObj.{u} O ⟶ Profinite.continuousMapRingObj O := ⟨{
    app S := AddCommGrpCat.ofHom {
      toFun x := ULift.up ⟨fun s ↦ r * x.down s, continuous_const.mul x.down.continuous⟩
      map_zero' := by
        apply ULift.ext
        ext s
        exact mul_zero r
      map_add' x y := by
        apply ULift.ext
        ext s
        exact mul_add r (x.down s) (y.down s) }
    naturality _ _ _ := by
      ext x
      apply ULift.ext
      ext s
      rfl }⟩
  refine Mod.homMk m ?_
  change MonObj.mul ≫ m = Profinite.continuousMapRingObj O ◁ m ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← Category.assoc, Sheaf.μ_comp_map_mul]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro x y
  apply ULift.ext
  ext z
  change r * (x.down z * y.down z) = x.down z * (r * y.down z)
  ring

private def reductionHom
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a] :
    Mod.regular R ⟶ (Mod.comap a).obj (Mod.regular S) :=
  Mod.homMk a (by
    change MonObj.mul ≫ a = R ◁ a ≫ a ▷ S ≫ MonObj.mul
    rw [IsMonHom.mul_hom]
    simp only [tensorHom_def', Category.assoc])

private theorem multiplicationHom_apply (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (r : O) (S : Profinite.{u})
    (x : ULift.{u + 1} C(S, O)) (z : S) :
    (((multiplicationHom O r).hom.hom.app (op S)) x).down z = r * x.down z := rfl

private theorem quotientMap_apply (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (S : Profinite.{u}) (x : ULift.{u + 1} C(S, PadicAlgCl.integers l E)) (z : S) :
    ((quotientMap l E π n).hom.app (op S) x).down z =
      Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1)) (x.down z) := rfl

attribute [local irreducible] multiplicationHom quotientMap

private theorem finiteModels_residue_discrete (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ) : DiscreteTopology (completedResidue ℓ E π n) := by
  have hp : π ≠ 0 := by
    intro h
    apply PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E.1
    rw [← hπ, h, Ideal.span_singleton_zero]
  let q := π ^ (n + 1)
  have hq : (q.val : E.1) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n + 1) hp
  let I : Ideal (PadicAlgCl.integers ℓ E.1) := (Ideal.span {π}) ^ (n + 1)
  have hopen : IsOpen (I : Set (PadicAlgCl.integers ℓ E.1)) := by
    apply I.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    have ho : IsOpen ((fun x : PadicAlgCl.integers ℓ E.1 ↦ (x : E.1)) ⁻¹'
        Metric.ball 0 ‖(q : E.1)‖) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    apply Filter.mem_of_superset (ho.mem_nhds (by
      change dist (0 : E.1) 0 < ‖(q : E.1)‖
      simpa only [dist_self] using norm_pos_iff.mpr hq))
    intro x hx
    have hx' : ‖(x : E.1)‖ < ‖(q : E.1)‖ := by
      change dist (x : E.1) 0 < ‖(q : E.1)‖ at hx
      simpa only [dist_zero_right] using hx
    have hdiv : (x : E.1) / q ∈ PadicAlgCl.integers ℓ E.1 := by
      change ‖(x : E.1) / q‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hq)).2 hx'.le
    change x ∈ (Ideal.span {π}) ^ (n + 1)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨⟨(x : E.1) / q, hdiv⟩, ?_⟩
    apply Subtype.ext
    change (x : E.1) = (q : E.1) * ((x : E.1) / q)
    exact (mul_div_cancel₀ _ hq).symm
  exact QuotientAddGroup.discreteTopology hopen

/-- The actual uniformizer quotient has a two-term rank-one free condensed resolution.
Source: current diagonal coefficient proof, paragraph (1), cofinal uniformizer quotients,
and scalar-six direct-image proof, finite free coefficient argument.
(blueprint: lem-diagonal-uniformizer-point-resolution).

Proof: the integer ring is a DVR domain and the maximal-ideal generator pi is nonzero.
Multiplication by pi^(n+1), followed by the actual quotient map, is a short exact sequence
of modules. Multiplication is a homeomorphism onto its image: divide in the ambient valued
field and restrict to the integer ring. A continuous function from a profinite set into
the kernel therefore divides continuously by pi^(n+1). The quotient is discrete;
choose one lift per residue class and glue the resulting constant functions on the clopen
fibres. Thus continuous sections preserve injectivity, exactness, and surjectivity of this
sequence. The arrows are linear for the continuous integer-valued functions, by pointwise
multiplication. Sectionwise short exactness gives short exactness of internal condensed
modules. The first two terms are the regular module, and the last is the quotient regular
module restricted along quotientMap. These identifications give the asserted isomorphisms.
The exponent n+1 is positive, including n=0; ramification only changes the nonzero scalar.
-/
theorem diagonalUniformizer_pointResolution
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ) :
    ∃ P : ShortComplex (IntegralFiniteScalar.PointModules
        (CommMon.mk (Profinite.padicIntegersRingObj.{u} l E.1))),
      P.ShortExact ∧
      Nonempty (P.X₁ ≅ Mod.regular (Profinite.padicIntegersRingObj.{u} l E.1)) ∧
      Nonempty (P.X₂ ≅ Mod.regular (Profinite.padicIntegersRingObj.{u} l E.1)) ∧
      Nonempty (P.X₃ ≅ (Mod.comap (quotientMap l E π n)).obj
        (Mod.regular (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)))) := by
  classical
  let O := PadicAlgCl.integers l E.1
  let r : O := π ^ (n + 1)
  let I : Ideal O := (Ideal.span {π}) ^ (n + 1)
  have hp : π ≠ 0 := by
    intro h
    apply PadicAlgCl.maximalIdeal_integers_ne_bot l E.1
    rw [← hπ, h, Ideal.span_singleton_zero]
  have hr : r ≠ 0 := pow_ne_zero _ hp
  have hrE : (r : E.1) ≠ 0 := by exact_mod_cast hr
  let Λ := Profinite.padicIntegersRingObj.{u} l E.1
  let m : Mod.regular Λ ⟶ Mod.regular Λ := multiplicationHom O r
  let q := reductionHom (quotientMap.{u} l E π n)
  have hz : m ≫ q = 0 := by
    apply Mod.hom_ext
    change (multiplicationHom O r).hom ≫ quotientMap l E π n = 0
    ext S x
    apply ULift.ext
    apply ContinuousMap.ext
    intro z
    change (((quotientMap l E π n).hom.app S)
      (((multiplicationHom O r).hom.hom.app S) x)).down z = 0
    rw [quotientMap_apply, multiplicationHom_apply]
    change Ideal.Quotient.mk I (r * x.down z) = 0
    rw [map_mul]
    have hzero : Ideal.Quotient.mk I r = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change π ^ (n + 1) ∈ Ideal.span {π} ^ (n + 1)
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) _
    rw [hzero, zero_mul]
  let P := ShortComplex.mk m q hz
  refine ⟨P, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  apply (Mod.shortExact_of_sectionwise (coherentTopology Profinite.{u}) Λ P ?_).2.2
  intro S
  let U := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ
  let V := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let N := ((P.map U).map V).map ((evaluation _ Ab.{u + 1}).obj (op S))
  have hf (x : ULift.{u + 1} C(S, O)) (z : S) :
      (N.f x).down z = r * x.down z := by
    exact multiplicationHom_apply O r S x z
  have hg (x : ULift.{u + 1} C(S, O)) (z : S) :
      (N.g x).down z = Ideal.Quotient.mk I (x.down z) := by
    exact quotientMap_apply l E π n S x z
  have hinj : Function.Injective N.f := by
    intro x y h
    apply ULift.ext
    apply ContinuousMap.ext
    intro z
    have hh := congrArg (fun t ↦ t.down z) h
    rw [hf, hf] at hh
    exact mul_left_cancel₀ hr hh
  have hdiv (x : C(S, O)) (hx : ∀ z, Ideal.Quotient.mk I (x z) = 0) :
      ∀ z, (x z : E.1) / (r : E.1) ∈ PadicAlgCl.integers l E.1 := by
    intro z
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp (hx z)
    change x z ∈ Ideal.span {π} ^ (n + 1) at hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hh : (x z : E.1) = (r : E.1) * (y : E.1) := by
      exact congrArg (fun t : O ↦ (t : E.1)) hy
    rw [hh, mul_div_cancel_left₀ _ hrE]
    exact y.property
  have hex : Function.Exact N.f N.g := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ z, Ideal.Quotient.mk I (x.down z) = 0 := by
        intro z
        have hh := congrArg (fun t ↦ t.down z) hx
        rw [hg] at hh
        exact hh
      let y : C(S, O) := ⟨fun z ↦ ⟨(x.down z : E.1) / (r : E.1), hdiv x.down hx' z⟩,
        ((continuous_subtype_val.comp x.down.continuous).div_const (r : E.1)).subtype_mk _⟩
      refine ⟨ULift.up y, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro z
      rw [hf]
      apply Subtype.ext
      change (r : E.1) * ((x.down z : E.1) / (r : E.1)) = (x.down z : E.1)
      exact mul_div_cancel₀ _ hrE
    · rintro ⟨y, rfl⟩
      exact congrArg (fun t ↦ t y) N.zero
  have hsurj : Function.Surjective N.g := by
    let : DiscreteTopology (completedResidue l E π n) :=
      finiteModels_residue_discrete l E π hπ n
    let liftResidue := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
    have hs : ∀ x, Ideal.Quotient.mk I (liftResidue x) = x :=
      Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I))
    intro x
    let y : C(S, O) := ⟨liftResidue ∘ x.down, continuous_of_discreteTopology.comp x.down.continuous⟩
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro z
    rw [hg]
    exact hs (x.down z)
  exact ShortComplex.ShortExact.mk' ((ShortComplex.ab_exact_iff_function_exact _).2 hex)
    ((AddCommGrpCat.mono_iff_injective _).2 hinj)
    ((AddCommGrpCat.epi_iff_surjective _).2 hsurj)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
