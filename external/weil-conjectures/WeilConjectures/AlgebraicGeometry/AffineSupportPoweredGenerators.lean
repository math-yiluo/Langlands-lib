/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectIntoSupportPowerTorsion
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh

/-! # Powered generators of a closed support

Source: Stacks Project, Tag 08EK, proof, first paragraph; Tag 08EJ.
(blueprint: lem-sc-affine-support-powered-generators).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private def globalFamily (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
  ⟨fun V ↦ X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op a, by
    intro V W f
    change X.presheaf.map f (X.presheaf.map _ a) = X.presheaf.map _ a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl⟩

@[simp] private theorem globalFamily_top (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    (globalFamily X a).val (op ⊤) = a := by
  dsimp [globalFamily]
  simp

/-- A closed subset of an affine scheme with quasi-compact complement is cut out by
finitely many global functions whose restrictions annihilate a given supported perfect object.
Source: Stacks Project, Tag 08EK, proof, first paragraph, and Tag 08EJ
(blueprint: lem-sc-affine-support-powered-generators).

Proof: cover the quasi-compact open complement of T by finitely many principal opens D(a_i)
contained in it. Regard a_i as compatible families of local sections on X and restrict the
families to U. The quasi-compact open U of an affine scheme is quasi-separated. The perfect
object F has quasi-coherent cohomology and is supported on V(a_i|_U), since T is contained
in V(a_i). Apply exists_pow_smul_eq_zero_of_perfect_supported on U to id_F. Choose a
positive power for each a_i (increase a zero exponent to one if necessary). These powers
annihilate F and have exactly the same principal opens as the original functions. Restriction
of section families commutes with powers, giving the asserted equality on the top open.
For T = X the empty family suffices; for T empty the argument uses the support assumption
on F, which forces F to be zero. -/
theorem exists_affine_support_powered_generators (X : Scheme.{u}) [IsAffine X]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (hFT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf x))) :
    ∃ (s : ℕ)
      (g : Fin s → RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
      (g' : Fin s →
        RingCat.sectionsSubring (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})),
      (∀ x : X, x ∉ T ↔ ∃ i : Fin s, x ∈ X.basicOpen ((g i).val (op ⊤))) ∧
      (∀ i : Fin s, (g' i).val (op ⊤) = U.ι.appTop.hom ((g i).val (op ⊤))) ∧
      (∀ i : Fin s, schemeDerivedScalar U.toScheme (g' i) (𝟙 F) = 0)  := by
  classical
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hbasic (x : V) : ∃ a : Γ(X, ⊤), X.basicOpen a ≤ V ∧ x.val ∈ X.basicOpen a :=
    (isAffineOpen_top X).exists_basicOpen_le x (by simp)
  choose a ha hx using hbasic
  obtain ⟨t, ht⟩ := hTc.elim_finite_subcover
    (fun x : V ↦ (X.basicOpen (a x) : Set X))
    (fun x ↦ (X.basicOpen (a x)).isOpen) (by
      intro x hxV
      exact Set.mem_iUnion.mpr ⟨⟨x, hxV⟩, hx ⟨x, hxV⟩⟩)
  let f : Fin t.card → Γ(X, ⊤) := fun i ↦ a ((t.equivFin.symm i).val)
  have hfcover (x : X) : x ∉ T ↔ ∃ i : Fin t.card, x ∈ X.basicOpen (f i) := by
    constructor
    · intro hxT
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hxT)
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa [f] using hxy⟩
    · rintro ⟨i, hi⟩
      exact ha _ hi
  let fX := fun i : Fin t.card ↦ globalFamily X (f i)
  let fU := fun i : Fin t.card ↦ globalFamily U.toScheme (U.ι.appTop.hom (f i))
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  let Fq : schemeDerivedQCohCategory U.toScheme :=
    ⟨F, schemeDerivedQCohProperty_of_isPerfect U.toScheme F hF⟩
  have hexp (i : Fin t.card) :
      ∃ n : ℕ, schemeDerivedScalar U.toScheme (fU i ^ n) (𝟙 F) = 0 := by
    apply exists_pow_smul_eq_zero_of_perfect_supported U.toScheme (fU i) Fq Fq (𝟙 Fq) hF
    intro n x hxzero
    apply hFT n x
    apply (hfcover x.val).mpr
    refine ⟨i, ?_⟩
    have hmem : x ∈ U.toScheme.basicOpen (U.ι.appTop.hom (f i)) := by
      simpa [fU, zeroLocus_singleton] using hxzero
    rw [← Scheme.preimage_basicOpen_top] at hmem
    exact hmem
  choose n hn using hexp
  refine ⟨t.card, (fun i ↦ fX i ^ (n i + 1)), (fun i ↦ fU i ^ (n i + 1)), ?_, ?_, ?_⟩
  · intro x
    have hp (i : Fin t.card) : X.basicOpen (f i ^ (n i + 1)) = X.basicOpen (f i) :=
      X.basicOpen_pow (f i) (by omega)
    simpa [fX, hp] using hfcover x
  · intro i
    simp [fX, fU, map_pow]
  · intro i
    have hmul : schemeDerivedScalar U.toScheme (fU i ^ (n i + 1)) (𝟙 F) =
        schemeDerivedScalar U.toScheme (fU i)
          (schemeDerivedScalar U.toScheme (fU i ^ n i) (𝟙 F)) := by
      simp [schemeDerivedScalar, pow_succ', mul_smul]
    rw [hmul, hn]
    simp [schemeDerivedScalar]


end AlgebraicGeometry.Scheme
