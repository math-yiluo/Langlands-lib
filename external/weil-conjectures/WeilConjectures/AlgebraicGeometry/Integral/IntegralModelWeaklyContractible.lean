/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomML
import WeilConjectures.AlgebraicGeometry.InternalPerfectScalarModelComplete
import WeilConjectures.AlgebraicGeometry.Internal.InternalReductionHomSections
import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import WeilConjectures.AlgebraicGeometry.InternalPerfectDualTensorFinite
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Integral models on weakly contractible schemes

Let `W` be an affine weakly contractible scheme, `K` a derived complete complex of
`𝒪_{E,W}`-modules and `P` a bounded complex of finite free `𝒪_E`-modules. If every reduction
`K_n` is isomorphic to `(P/π^n)_W`, then `K ≅ 𝒪_{E,W} ⊗_{𝒪_E} P`.

The isomorphisms at the finite levels need not be compatible.

## Implementation details

The proof of `nonempty_iso_internalPerfectScalarModel_of_isWeaklyContractible` runs as follows.
1. Choose `e` with `π_E^e` killing the torsion of `H^1` of `Q = P^∨ ⊗ P`, a bounded complex of
   finite free modules over the discrete valuation ring `𝒪_E`.
2. By weak contractibility the tower of groups `Hom(T_n, K_n)` is Mittag-Leffler, with
   stable images from level `n + e` on (`internalPerfectReductionHom_mittagLeffler`).
3. Each group contains an isomorphism, whose reductions are isomorphisms, so the stable image at
   the first level contains an isomorphism; it lifts to a compatible family.
4. As `K` is complete, the family lifts to a map `T ⟶ K`
   (`exists_hom_of_internalReductionHomTower_sections`), whose first reduction is invertible.
5. `T` is complete (`isDerivedComplete_internalPerfectScalarModel`), so derived Nakayama
   (`derived_nakayama_first_reduction`) shows that this map is an isomorphism.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Some power of an irreducible element kills the torsion of a finite module over a
discrete valuation ring. -/
private theorem exists_pow_smul_eq_zero_of_mem_torsion {R M : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ e : ℕ, ∀ x ∈ Submodule.torsion R M, ϖ ^ e • x = 0 := by
  let t := Submodule.torsion R M
  obtain ⟨r, hr, hr₀⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := R) (M := M))
  obtain ⟨e, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hr₀) hϖ
  refine ⟨e, fun x hx ↦ ?_⟩
  have hx' : ((v : R) * ϖ ^ e) • (⟨x, hx⟩ : t) = 0 :=
    (Submodule.mem_annihilator.mp hr) _ Submodule.mem_top
  have hx'' : ((v : R) * ϖ ^ e) • x = 0 := congrArg Subtype.val hx'
  rw [mul_smul] at hx''
  simpa using congrArg (fun y ↦ (↑v⁻¹ : R) • y) hx''

/-- Choose a compatible family whose first term has a property attained from every level. -/
private theorem exists_sections_with_property (F : ℕᵒᵖ ⥤ Type w)
    (hF : F.IsMittagLeffler) (p : F.obj (op 0) → Prop)
    (hp : ∀ n : ℕ, ∃ x : F.obj (op n), p (F.map (homOfLE (Nat.zero_le n)).op x)) :
    ∃ x : F.sections, p (x.val (op 0)) := by
  classical
  obtain ⟨n, f, hf⟩ := F.isMittagLeffler_iff_eventualRange.mp hF (op 0)
  obtain ⟨x, hx⟩ := hp n.unop
  have hfx : p (F.map f x) := by
    have he : f = (homOfLE (Nat.zero_le n.unop)).op := Subsingleton.elim _ _
    simpa only [he] using hx
  let y : (F.toEventualRanges).obj (op 0) := ⟨F.map f x, hf.symm ▸ ⟨x, rfl⟩⟩
  obtain ⟨z, hz⟩ := Types.surjective_π_app_zero_of_surjective_map
    (Types.limitConeIsLimit F.toEventualRanges)
    (fun n ↦ F.surjective_toEventualRanges hF (homOfLE (Nat.le_succ n)).op) y
  refine ⟨F.toEventualRangesSectionsEquiv z, ?_⟩
  exact (congrArg (fun t : (F.toEventualRanges).obj (op 0) ↦ p t.val) hz).mpr hfx

/-- The transitions of the Hom tower carry isomorphisms to isomorphisms. -/
private theorem isIso_internalReductionHomTower_map (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ)
    (φ : internalReductionHom l E W T K n) (hφ : IsIso φ) :
    IsIso ((internalReductionHomTower l E W T K).map (homOfLE (Nat.zero_le n)).op φ) := by
  induction n with
  | zero =>
    simpa only [show (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) from rfl,
      Functor.map_id_apply] using hφ
  | succ n ih =>
    have he : (homOfLE (Nat.zero_le (n + 1))).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (Nat.zero_le n)).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp_apply]
    apply ih
    dsimp only [internalReductionHomTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change IsIso (internalReductionHomStep l E W T K n φ)
    dsimp only [internalReductionHomStep]
    infer_instance

/-- **Integral models on weakly contractible schemes.** Let `W` be an affine weakly
contractible object of the pro-étale site, `K` a derived complete complex of
`𝒪_{E,W}`-modules and `P` a bounded complex of finite free `𝒪_E`-modules. If for every `n`
the reduction `K_n` is isomorphic to the reduction `(P/π_E^n)_W` of the scalar model
`𝒪_{E,W} ⊗_{𝒪_E} P`, then `K ≅ 𝒪_{E,W} ⊗_{𝒪_E} P`. The levelwise isomorphisms are not assumed
to be compatible. The index `n : ℕ` denotes the exponent `n + 1`. -/
theorem nonempty_iso_internalPerfectScalarModel_of_isWeaklyContractible
    (X : Scheme.{u}) (W : X.ProEt) (hAffine : IsAffine W.left)
    (hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (K : DerivedCategory (AdicCompletion.Modules l E W.left))
    (hK : IsDerivedComplete l E W.left K)
    (hiso : ∀ n : ℕ, Nonempty
      ((AdicCompletion.derivedReduction l E W.left n).obj
        (internalPerfectScalarModel l E W.left P) ≅
          (AdicCompletion.derivedReduction l E W.left n).obj K)) :
    Nonempty (K ≅ internalPerfectScalarModel l E W.left P) := by
  let A := Padic.coefficientExtensionIntegers l E
  let T := internalPerfectScalarModel l E W.left P
  -- Step 1: a uniform torsion exponent.
  have hcoeff := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsDiscreteValuationRing A := hcoeff.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hcoeff.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l E) := by
    have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hcoeff.2.2.2.2.1
    have hne : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ := hcoeff.2.2.2.2.2.2.2.2.2.1
    have h0 : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
      intro h
      apply hne
      rw [← hgen, h, Ideal.span_singleton_eq_bot.mpr rfl]
    have hprime : (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)).IsPrime :=
      hgen ▸ hmax.isPrime
    exact ((Ideal.span_singleton_prime h0).mp hprime).irreducible
  obtain ⟨c, d, hc, hd, hQ⟩ :=
    internalPerfectScalarDualTensor_finite l E P a b ha hb hfree
  let Q := internalPerfectScalarDualTensor l E P
  have : Module.Finite A (Q.X 1) := (hQ 1).2
  have : Module.Finite A (Q.cycles 1) :=
    Module.Finite.of_injective (Q.iCycles 1).hom
      ((ModuleCat.mono_iff_injective (Q.iCycles 1)).1 inferInstance)
  have : Module.Finite A (Q.homology 1) :=
    Module.Finite.of_surjective (Q.homologyπ 1).hom
      ((ModuleCat.epi_iff_surjective (Q.homologyπ 1)).1 inferInstance)
  obtain ⟨e, he⟩ := exists_pow_smul_eq_zero_of_mem_torsion hirr (M := Q.homology 1)
  -- Step 2: the Mittag-Leffler property of the Hom tower.
  have hML := (internalPerfectReductionHom_mittagLeffler l E X W hAffine hweak P a b ha hb
    hfree K hiso e (fun x hx ↦ he x hx)).2
  -- Step 3: a compatible family starting with an isomorphism.
  obtain ⟨s, hs⟩ := exists_sections_with_property (internalReductionHomTower l E W.left T K)
    hML (fun φ ↦ IsIso φ) (fun n ↦ ⟨(hiso n).some.hom,
      isIso_internalReductionHomTower_map l E W.left T K n _ inferInstance⟩)
  -- Step 4: lift it to a map into the complete `K`.
  obtain ⟨g, hg⟩ := exists_hom_of_internalReductionHomTower_sections l E W.left T K hK s
  -- Step 5: derived Nakayama.
  have : IsIso g := (derived_nakayama_first_reduction l E W.left).2.2.2 T K g
    (isDerivedComplete_internalPerfectScalarModel l E W.left P a b ha hb hfree) hK
    (by rw [hg 0]; exact hs)
  exact ⟨(asIso g).symm⟩

end AlgebraicGeometry.ProEtale
