/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.MarkedCurveDiagramModel
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.MarkedCurveDiagramRefinement

/-!
# Spreading a marked curve diagram from a generic fibre

This is the descent argument with its field diagram supplied.

## References

* Stacks Project, Tag 0GK7, the radicial-extension, spreading and final shrinking paragraphs
* Stacks Project, Tag 0GK7, from the paragraph reducing the inseparable extension through the last
  paragraph
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem lift_generic_square_through_refinement
    {A C Y Y' V V' : Scheme.{u}} {h : A ⟶ Y} {a : A ⟶ C}
    {b : Y ⟶ V} {σ : C ⟶ V} (H : IsPullback h a b σ)
    {y : Y' ⟶ Y} {b' : Y' ⟶ V'} {v : V' ⟶ V}
    (H' : IsPullback y b' b v) (σ' : C ⟶ V') (hσ : σ' ≫ v = σ) :
    ∃ h' : A ⟶ Y', h' ≫ y = h ∧ IsPullback h' a b' σ' := by
  let h' := H'.lift h (a ≫ σ') (by rw [Category.assoc, hσ]; exact H.w)
  have hh : h' ≫ y = h := H'.lift_fst _ _ _
  have hb : h' ≫ b' = a ≫ σ' := H'.lift_snd _ _ _
  refine ⟨h', hh, ?_⟩
  have Houter : IsPullback (h' ≫ y) a b (σ' ≫ v) := by
    rw [hh, hσ]
    exact H
  exact Houter.of_right hb H'

set_option backward.isDefEq.respectTransparency false in
/-- Spread a specified finite diagram over a finite purely inseparable extension of a
component's generic residue field. The supplied open marks a thickening locus that meets
each normalized component densely. The output keeps the supplied number of components
and identifies their generic fibres with the supplied diagram by cartesian squares.
-/
theorem exists_spread_marked_curve_diagram
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K]
    (n : ℕ) (L : Fin n → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (A B : Fin n → Scheme.{u}) (j₀ : ∀ i, A i ⟶ B i)
    (q₀ : ∀ i, B i ⟶ Spec (.of (L i)))
    (ν₀ : (∐ A) ⟶ pullback (f.fiberToSpecResidueField η)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))))
    (hν₀ : IsFinite ν₀ ∧ Surjective ν₀)
    (hcomm : ∀ i, Sigma.ι A i ≫ ν₀ ≫ pullback.snd _ _ =
      j₀ i ≫ q₀ i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
    (hL : ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i))
    (hj₀ : ∀ i, IsOpenImmersion (j₀ i) ∧ Nonempty (A i))
    (hq₀ : ∀ i, Smooth (q₀ i) ∧ IsProper (q₀ i) ∧
      GeometricallyIrreducible (q₀ i) ∧ topologicalKrullDim (B i) ≤ 1)
    (W₀ : (pullback (f.fiberToSpecResidueField η)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))).Opens)
    (hW₀ : (∀ i, Dense ((Sigma.ι A i ≫ ν₀) ⁻¹' (W₀ : Set _))) ∧
      IsThickening (pullback.snd ν₀ W₀.ι)) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        (∃ (σK : Spec (.of K) ⟶ V)
          (hA : ∀ i, A i ⟶ Y i) (hB : ∀ i, B i ⟶ Ybar i)
          (hT : ∀ i, Spec (.of (L i)) ⟶ T i),
          σK ≫ g ≫ U.ι = Spec.map (CommRingCat.ofHom
            (algebraMap (S.residueField η) K)) ≫ S.fromSpecResidueField η ∧
          ∀ i,
            IsPullback (hA i) (j₀ i ≫ q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (j i ≫ p i ≫ t i) σK ∧
            IsPullback (hB i) (q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) (p i ≫ t i) σK ∧
            IsPullback (hT i) (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (t i) σK ∧
            hA i ≫ j i = j₀ i ≫ hB i ∧ hB i ≫ p i = q₀ i ≫ hT i) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ i, Surjective (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i)) ∧
          IsThickening (pullback.snd ν W.ι) := by
  classical
  obtain ⟨U, hηU, V, g, hgf, hgs, hgr, T, Y, Ybar, t, j, p, ν,
    hνf, hνs, hcomm', ht, hj, hp, hgeneric, W, hW, hgood⟩ :=
    exists_marked_curve_diagram_model f η hη K n L A B j₀ q₀ ν₀
      hν₀ hcomm hL hj₀ hq₀ W₀ hW₀
  obtain ⟨σK, hA, hB, hT, hσK, H⟩ := hgeneric
  have : IsFinite g := hgf
  have : Surjective g := hgs
  have : UniversallyInjective g := hgr
  have : IsFinite ν := hνf
  have : Surjective ν := hνs
  have hσpoint (z : Spec (.of K)) : (g ≫ U.ι) (σK z) = η := by
    have hz := congrArg (fun a : Spec (.of K) ⟶ S ↦ a z) hσK
    exact hz.trans (S.fromSpecResidueField_apply η _)
  obtain ⟨U', hηU', V', g', hgf', hgs', hgr', aV, σ', haV, hσ', hbase,
    T', Y', B', t', j', p', ν', hνf', hνs', hcomm'', ht', hj', hsm', hp',
    hW', aY, aB, aT, H'⟩ :=
    exists_marked_curve_diagram_refinement f U η hηU g σK hσpoint n
      T Y Ybar t j p ν hcomm' ht hj hp W hW hgood
  have (i : Fin n) : IsOpenImmersion (aB i) :=
    MorphismProperty.of_isPullback (H' i).2.1.flip haV
  have (i : Fin n) : IsOpenImmersion (aT i) :=
    MorphismProperty.of_isPullback (H' i).2.2.1.flip haV
  have hexA (i : Fin n) :=
    lift_generic_square_through_refinement (H i).1 (H' i).1 σ' hσ'
  have hexB (i : Fin n) :=
    lift_generic_square_through_refinement (H i).2.1 (H' i).2.1 σ' hσ'
  have hexT (i : Fin n) :=
    lift_generic_square_through_refinement (H i).2.2.1 (H' i).2.2.1 σ' hσ'
  choose hA' heA HA using hexA
  choose hB' heB HB using hexB
  choose hT' heT HT using hexT
  refine ⟨U', hηU', V', g', hgf', hgs', hgr', T', Y', B', t', j', p', ν',
    hνf', hνs', hcomm'', ht', hj', hsm', hp', ?_, hW'⟩
  refine ⟨σ', hA', hB', hT', ?_, fun i ↦ ⟨HA i, HB i, HT i, ?_, ?_⟩⟩
  · calc
      σ' ≫ g' ≫ U'.ι = σ' ≫ aV ≫ g ≫ U.ι := by rw [hbase]
      _ = σK ≫ g ≫ U.ι := by rw [← Category.assoc, hσ']
      _ = _ := hσK
  · apply (cancel_mono (aB i)).mp
    calc
      (hA' i ≫ j' i) ≫ aB i = hA' i ≫ aY i ≫ j i := by
        rw [Category.assoc, (H' i).2.2.2.1]
      _ = hA i ≫ j i := by rw [← Category.assoc, heA]
      _ = j₀ i ≫ hB i := (H i).2.2.2.1
      _ = (j₀ i ≫ hB' i) ≫ aB i := by rw [Category.assoc, heB]
  · apply (cancel_mono (aT i)).mp
    calc
      (hB' i ≫ p' i) ≫ aT i = hB' i ≫ aB i ≫ p i := by
        rw [Category.assoc, (H' i).2.2.2.2]
      _ = hB i ≫ p i := by rw [← Category.assoc, heB]
      _ = q₀ i ≫ hT i := (H i).2.2.2.2
      _ = (q₀ i ≫ hT' i) ≫ aT i := by rw [Category.assoc, heT]

end AlgebraicGeometry
