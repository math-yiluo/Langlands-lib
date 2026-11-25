/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpenAlgebra
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpenDictionary
import WeilConjectures.AlgebraicGeometry.NonvanishingLocusRestrict
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Affine opens intersected with section nonvanishing loci

Source: Stacks Project, Properties, Lemma 01PV (properties-lemma-affine-cap-s-open)
(blueprint: lem-sc-affine-cap-section-open).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem affine_nonvanishing {R : Type u} [CommRing R]
    (M : (Spec (.of R)).Modules) [M.IsInvertible]
    (s : M.val.presheaf.obj (Opposite.op ⊤)) :
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ (V : Set _) = nonvanishingLocus M s := by
  classical
  let N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
  obtain ⟨_, ⟨hfin, hproj⟩, hlocal, hloc⟩ := affine_cap_section_open_dictionary M s
  let : Module.Finite R N := hfin
  let : Module.Projective R N := hproj
  have hrank (p : PrimeSpectrum R) : Module.rankAtStalk N p = 1 := by
    obtain ⟨e⟩ := (hlocal p.asIdeal).1
    simpa only [Module.rankAtStalk, Module.finrank_self] using e.finrank_eq
  let sN : N := s
  obtain ⟨hf, himage⟩ := affine_cap_section_open_algebra R N hrank sN
  let B := SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N sN - 1}
  let f : Spec (.of B) ⟶ Spec (.of (ULift.{u} R)) := Spec.map (CommRingCat.ofHom
    ((algebraMap R B).comp (ULift.ringEquiv : ULift.{u} R ≃+* R).toRingHom))
  let g : Spec (.of (ULift.{u} R)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom
    (ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom)
  have : IsOpenImmersion f := hf
  have : CategoryTheory.IsIso g := by
    change CategoryTheory.IsIso (Spec.map
      (((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toCommRingCatIso).hom))
    infer_instance
  refine ⟨(CategoryTheory.CategoryStruct.comp f g).opensRange,
    isAffineOpen_opensRange (CategoryTheory.CategoryStruct.comp f g), ?_⟩
  apply Eq.trans ?_ hloc.symm
  change Set.range (CategoryTheory.CategoryStruct.comp f g) = _
  change Set.range (g ∘ f) = _
  rw [Set.range_comp, himage]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    obtain ⟨q, rfl⟩ :=
      (CategoryTheory.ConcreteCategory.bijective_of_isIso g.base).surjective p
    exact ⟨q, hp, rfl⟩

/-- Intersecting an affine open with the nonvanishing locus of a section of an invertible
module, or of any positive tensor power of it, gives an affine open. The nonvanishing
condition is exactly that the germ lies outside the maximal ideal times the stalk module,
as in `def-weil-pbc-ample-invertible-module`.

Source: Stacks Project, Properties, Lemma 01PV (properties-lemma-affine-cap-s-open)
(blueprint: lem-sc-affine-cap-section-open).

Proof:
1. Restrict the invertible module to the affine scheme `U = Spec R`. The affine dictionary
   (`lem-weil-pbc-affine-tilde-gamma-adjunction` and
   `lem-sc-affine-cap-section-open-dictionary`) identifies it with the sheaf of a finite
   projective rank-one module `N`, and identifies the intersection with the primes `p`
   at which the restricted section is outside `p N`.
2. Apply `lem-sc-affine-cap-section-open-algebra`: this prime locus is affine. Its affine
   model is `Spec (Sym_R N / (s - 1))`, so the intersection is affine.
3. For `n > 0`, the tensor power is invertible
   (`def-weil-pbc-ample-invertible-module`). Apply the first clause to it and to its section.
-/
theorem affine_cap_section_open (X : Scheme.{u}) (M : X.Modules) [M.IsInvertible]
    (s : M.val.presheaf.obj (Opposite.op ⊤)) (U : X.Opens) (hU : IsAffineOpen U) :
    (∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ x ∈ U ∧
      (TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial) s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x))) ∧
    (∀ n : ℕ, 0 < n → ∀ t : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
      ∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ x ∈ U ∧
        (TopCat.Presheaf.germ (M.tensorPow n).val.presheaf ⊤ x trivial) t ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              ↑(TopCat.Presheaf.stalk (M.tensorPow n).val.presheaf x))) := by
  have section_case (P : X.Modules) [P.IsInvertible]
      (a : P.val.presheaf.obj (Opposite.op ⊤)) :
      ∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X,
        x ∈ V ↔ x ∈ U ∧ x ∈ nonvanishingLocus P a := by
    let f := hU.fromSpec
    let Q := P.restrict f
    have : Q.IsInvertible :=
      IsInvertible.of_iso ((restrictFunctorIsoPullback f).app P).symm
    let b : Q.val.presheaf.obj (Opposite.op ⊤) :=
      (P.restrictAppIso f ⊤).inv (P.presheaf.map (CategoryTheory.homOfLE le_top).op a)
    obtain ⟨W, hW, hloc⟩ := affine_nonvanishing Q b
    refine ⟨f ''ᵁ W, hW.image_of_isOpenImmersion f, ?_⟩
    have hpre : (W : Set _) = f ⁻¹' nonvanishingLocus P a :=
      hloc.trans (nonvanishingLocus_restrict f P a)
    intro x
    change x ∈ f '' (W : Set _) ↔ _
    rw [hpre, Set.image_preimage_eq_inter_range, hU.range_fromSpec]
    exact and_comm
  constructor
  · exact section_case M s
  · intro n _ t
    exact section_case (M.tensorPow n) t

end AlgebraicGeometry.Scheme.Modules
