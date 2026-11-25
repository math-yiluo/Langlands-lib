/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.SectionCohomologyUnitComparisons

/-! # Denominators for raw section cohomology

Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-section-cohomology-principal-denominators).
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A class on a principal open lifts after multiplication by a power of its defining
function. This asserts only denominator lifting, not the kernel of restriction.

Source: Stacks Project, Tag 09MR, Lemma 30.17.3, surjectivity of the canonical map;
Tag 01E4, Lemma 20.7.3, computation by the section complex.
(blueprint: lem-pc-section-cohomology-principal-denominators).

Proof: Put Y = f inverse W, G = F restricted to Y, and let s be the pullback
of a viewed as a section of the tensor unit. The affine and qcqs assumptions give
compactness and quasi-separatedness of Y; restriction preserves quasi-coherence.
Apply invertS_cohomology with the tensor unit. The comparison theorem
sectionCohomology_unit_comparisons identifies derived sections with raw cohomology,
compatibly with tensor-unit powers, restriction, and the a-action. Thus the image
of each fraction [n, xi] has denominator a^n and numerator c(n)(xi).
Descend the desired existential property by QuotientAddGroup.induction_on, and use
DirectSum.induction_on on a representative. Zero has exponent zero and numerator
zero. If two images have exponents n and m and numerators y and y', their sum has
exponent n+m and numerator a^m y + a^n y', by linearity of restriction. Finally use
surjectivity of the composite additive equivalence. No common-degree fraction
normalization or transition identity is needed. The proof works unchanged for a=0,
a a unit, q=0, empty W, and zero coefficients. -/
theorem sectionCohomologyPresheaf_pow_lifts {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    ∀ x : P.obj (op (T.basicOpen a)), ∃ (n : ℕ) (y : P.obj (op W)),
      a ^ n • x = (P.map (homOfLE (T.basicOpen_le a)).op).hom y := by
  classical
  dsimp only
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let L := MonoidalCategory.tensorUnit Y.Modules
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
  let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  let r : P.obj (op W) →ₗ[Γ(T, W)] P.obj (op (T.basicOpen a)) :=
    (P.map (homOfLE (T.basicOpen_le a)).op).hom
  have : CompactSpace Y :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hW.isCompact)
  have : IsAffine W.toScheme := hW
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (f ∣_ W)
  obtain ⟨U, hU, e, he⟩ := invertS_cohomology Y L G s q
  obtain ⟨t, c, d, hmul, hres⟩ :=
    sectionCohomology_unit_comparisons f F I q W a U hU
  let v : CohomologyFractionPresentation L G s q ⊤ →+
      P.obj (op (T.basicOpen a)) := t.toAddMonoidHom.comp e.toAddMonoidHom
  have hgen (n : ℕ) (ξ : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
      (MonoidalCategory.tensorObj G (L.tensorPow n) : Y.Modules)) :
      a ^ n • v (cohomologyFraction L G s q ⊤ n ξ) = r (c n ξ) := by
    exact (hmul n (e (cohomologyFraction L G s q ⊤ n ξ))).symm.trans
      ((congrArg (d n) (he n ξ)).trans (hres n ξ))
  have hlift (z : CohomologyFractionPresentation L G s q ⊤) :
      ∃ (n : ℕ) (y : P.obj (op W)), a ^ n • v z = r y := by
    refine QuotientAddGroup.induction_on z ?_
    intro z
    induction z using DirectSum.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | of n ξ => exact ⟨n, c n ξ, hgen n ξ⟩
    | add z w hz hw =>
      obtain ⟨n, y, hy⟩ := hz
      obtain ⟨m, y', hy'⟩ := hw
      refine ⟨n + m, a ^ m • y + a ^ n • y', ?_⟩
      change a ^ (n + m) • v (QuotientAddGroup.mk z + QuotientAddGroup.mk w) = _
      rw [map_add, smul_add, r.map_add, r.map_smul, r.map_smul]
      congr 1
      · rw [Nat.add_comm n m, pow_add, mul_smul, hy]
      · rw [pow_add, mul_smul, hy']
  intro x
  obtain ⟨z, hz⟩ := (e.trans t).surjective x
  obtain ⟨n, y, hy⟩ := hlift z
  change t (e z) = x at hz
  change a ^ n • t (e z) = r y at hy
  rw [hz] at hy
  exact ⟨n, y, hy⟩

end AlgebraicGeometry.Scheme.Modules
