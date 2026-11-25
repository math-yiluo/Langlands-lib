/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeFiniteCoproduct

/-! # Etale local integral lattices

Source: Bhatt--Scholze, Proposition 6.8.4(6) and Lemma 6.8.13.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finite_affine_etale_cover_geometry
    (X : Scheme.{u}) {I : Type u} [Finite I]
    (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
    [∀ i, IsAffine (Y i)] [∀ i, Etale (p i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : Y i), p i y = x) :
    Etale (Limits.Sigma.desc p) ∧ Surjective (Limits.Sigma.desc p) ∧
      CompactSpace (∐ Y : Scheme.{u}) ∧ QuasiSeparatedSpace (∐ Y : Scheme.{u}) := by
  classical
  let f : (∐ Y) ⟶ X := Limits.Sigma.desc p
  have hf : Etale f := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Y)]
    intro i
    simpa [f] using (inferInstance : Etale (p i))
  have hsurj : Surjective f := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨i, y, hy⟩ := hcover x
    refine ⟨Limits.Sigma.ι Y i y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_comp_desc]
    exact hy
  let : IsAffine (∐ Y) := inferInstance
  exact ⟨hf, hsurj, inferInstance, inferInstance⟩

private theorem etale_lattice_of_finite_affine_lattices
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    {I : Type u} [Finite I] (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
    [∀ i, IsAffine (Y i)] [∀ i, Etale (p i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : Y i), p i y = x)
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj Λ (Y i)))
    (hM : ∀ i, IsLocallyFree (condensedRingObj Λ (Y i)) (M i))
    (e : ∀ i, Nonempty ((Mod.extendScalars (coefficientMap φ (Y i))).obj (M i) ≅
      (upperStar Λ' (p i)).obj P)) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), Etale p ∧ Surjective p ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (Λ) U),
      (IsLocallyFree (condensedRingObj (Λ) U) M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (φ) U)).obj M ≅
        (CondensedRing.upperStar (Λ') p).obj P) := by
  obtain ⟨hf, hs, hc, hq⟩ := finite_affine_etale_cover_geometry X Y p hcover
  obtain ⟨N, hN, eN⟩ := continuousLattice_finite_coproduct_of_coefficients Λ Λ' φ X P Y p M hM e
  exact ⟨∐ Y, Limits.Sigma.desc p, hf, hs, hc, hq, N, hN, eN⟩

private theorem exists_finite_affine_etale_cover_with_property
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Q : ∀ U : Scheme.{u}, (U ⟶ X) → Prop)
    (hlocal : ∀ x : X, ∃ (U : Scheme.{u}) (p : U ⟶ X),
      IsAffine U ∧ Etale p ∧ x ∈ Set.range p ∧ Q U p) :
    ∃ (I : Type u) (_ : Finite I) (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X),
      (∀ i, IsAffine (Y i)) ∧ (∀ i, Etale (p i)) ∧
      (∀ x : X, ∃ (i : I) (y : Y i), p i y = x) ∧ (∀ i, Q (Y i) (p i)) := by
  classical
  choose Y p hY hp hcover hQ using hlocal
  let (x : X) : Etale (p x) := hp x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ Set.range (p x))
    (fun x ↦ (p x).isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hcover x⟩)
  refine ⟨s, inferInstance, (fun i ↦ Y i.val), (fun i ↦ p i.val),
    (fun i ↦ hY i.val), (fun i ↦ hp i.val), ?_, (fun i ↦ hQ i.val)⟩
  intro x
  obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, y, hy⟩

/-- Integral lattices exist on a quasi-compact quasi-separated etale cover.
Source: Bhatt--Scholze, Proposition 6.8.4(6), and the first paragraph of Lemma 6.8.13.
(auxiliary; not a blueprint node)

Proof in words. Apply continuousLisse_affine_etale_lattice at every point x of X.
It encodes the rational module explicitly, applies the existing sectionwise
etale-local lattice theorem, transports the specified lattice back, and refines
to an affine neighborhood. The images of these neighborhoods are open because
the maps are etale, and they cover X because each contains its indexing point.
Noetherianity implies compactness, so choose a finite subfamily. Its scheme
coproduct U is affine, hence compact and quasi-separated. The coproduct map to X
is etale since that is Zariski local at the source, and it is surjective by the
finite covering property. Apply continuousLattice_finite_coproduct to construct
the internal integral module on U as a finite biproduct of component extensions
by zero, with its bound pro-etale free cover and rationalization isomorphism.
No compatibility among the component lattices is required. The same argument
includes zero ranks and the empty base. Only a cover and a lattice on it are
asserted; descent and stratification are separate steps. -/
theorem continuousLisse_etale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), Etale p ∧ Surjective p ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) U),
      (IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) := by
  classical
  let Q : ∀ U : Scheme.{u}, (U ⟶ X) → Prop := fun U p ↦
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) U),
      (IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)
  obtain ⟨I, hI, Y, p, hY, hp, hcover, hQ⟩ :=
    exists_finite_affine_etale_cover_with_property X Q
      (continuousLisse_affine_etale_lattice ℓ E X P hP)
  let : Finite I := hI
  let (i : I) : IsAffine (Y i) := hY i
  let (i : I) : Etale (p i) := hp i
  dsimp only [Q] at hQ
  choose M hM e using hQ
  exact etale_lattice_of_finite_affine_lattices
    (integralCoeff ℓ E) (Profinite.continuousMapRingObj E) (integralScalarMap ℓ E)
    X P Y p hcover M hM e

end AlgebraicGeometry.ProEtale.CondensedRing
