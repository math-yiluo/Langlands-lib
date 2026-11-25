/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import WeilConjectures.Algebra.Homology.FiniteStripAugmentation

/-! # Finite-cover augmentation for complexes with injective terms

Source: Stacks Project, Tag 08C1, proof; Tags 01EP and 01FM.
(blueprint: lem-sc-injective-terms-alternating-cech-augmentation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_isZero_column
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (p : ℤ) (hp : p < 0 ∨ (r : ℤ) ≤ p) :
    IsZero (((alternatingCechDoubleFunctor U).obj F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply (show IsZero ((((alternatingCechDoubleFunctor U).obj F).X p).X n) from ?_).eq_of_src
  change IsZero (((alternatingCechModuleFunctor U).obj (F.X n)).X p)
  change IsZero (((alternatingCechComplex U
    ((alternatingCechModulePresheaf (X := X)).obj (F.X n))).extend
      ComplexShape.embeddingUpNat).X p)
  rcases hp with hp | hp
  · apply HomologicalComplex.isZero_extend_X
    intro k
    change (k : ℤ) ≠ p
    omega
  · have hnonneg : 0 ≤ p := le_trans (by omega) hp
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    apply IsZero.of_iso _ (HomologicalComplex.extendXIso _
      ComplexShape.embeddingUpNat (i := k) rfl)
    change IsZero (alternatingCechTerms U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k)
    have : IsEmpty (Fin (k + 1) ↪o Fin r) := ⟨fun t ↦ by
      have ht := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at ht
      omega⟩
    unfold alternatingCechTerms
    exact ModuleCat.isZero_of_subsingleton _

/-- Injective terms suffice for the finite-cover augmentation; no boundedness or
K-injectivity assumption on the coefficient complex is needed.

Source: Stacks Project, Tag 08C1, first paragraph of the proof, using Tags 01EP
and 01FM (blueprint: lem-sc-injective-terms-alternating-cech-augmentation).

Proof: For each integer q, augment the alternating section complex of I.X q by
its global sections. The sheaf gluing axiom identifies the kernel in degree zero
with global sections and makes the augmentation injective. Injective module
Čech acyclicity gives zero positive cohomology for the ordered complex. The
ordered-to-increasing comparison, whose map is restriction to increasing tuples,
commutes with augmentation and identifies this with exactness of the explicit
alternating row used here. Forgetting global scalar structure detects exactness.
The cone of the section-to-total map is, up to its cone sign conventions, the
total of these augmented rows. Its Čech columns range from -1 to r-1: an increasing
(p+1)-tuple in Fin r does not exist when p >= r. For a total cocycle, exactness
supplies a horizontal preimage of its highest Čech component, since the next
column is zero. Subtract the total differential of this preimage. The highest
component disappears and the vertical part changes only the previous column.
Repeat down to column -1; injectivity of augmentation kills the final component.
Thus every cone cocycle is a boundary, even with unbounded vertical degrees,
and the augmentation is a quasi-isomorphism. If r=0, the cover implies X is empty;
the sheaf axiom makes every section module zero, and both complexes vanish. -/
theorem injectiveTerms_alternatingCech_augmentation_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    QuasiIso ((alternatingCechAugmentation U).app I) := by
  let K := (alternatingCechDoubleFunctor U).obj I
  let A := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  apply HomologicalComplex₂.quasiIso_of_finite_strip_row_augmentation K r
    (alternatingCechDouble_isZero_column U I) A
    (fun n ↦ alternatingCechZero U (I.X n))
    ((alternatingCechAugmentation U).app I) (fun _ ↦ rfl)
  intro n
  have := hI n
  exact injective_alternatingCech_row_augmentation X r U hU (I.X n)

end AlgebraicGeometry
