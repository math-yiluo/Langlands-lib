/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Pseudo-coherent complexes of finite Tor dimension are perfect

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Lemma 15.76.2
(Tag 0658) (blueprint: lem-pc-ring-pseudo-coherent-finite-tor-perfect).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A pseudo-coherent object `C` of `D(R)` with Tor amplitude in some interval `[a, b]`,
`a ≤ b`, is isomorphic in `D(R)` to a bounded complex of finitely generated projective
`R`-modules, i.e. it is perfect in the affine sense.
Source: Stacks Project, More on Algebra, Lemma 15.76.2 (Tag 0658)
(blueprint: lem-pc-ring-pseudo-coherent-finite-tor-perfect).

Proof: Use the bounded-above finite-free model `P` supplied by pseudo-coherence,
with upper bound `c`. Testing the Tor amplitude against `R` gives `H^i(P) = 0`
for `i < a`. The bounded-above flat complex `P` is K-flat, so its ordinary tensor
with every module has zero homology in degree `a - 1`. The cokernel criterion
`ObjectProperty.flat_opcycles_of_exactAt` makes `P.opcycles a` flat. It is finitely
presented: the kernel of the surjection from the finite free module `P.X a` is the
image of the finite module `P.X (a - 1)`. Hence it is finite projective. The good
truncation `P.truncGE a` has this cokernel in degree `a`, zero terms below `a`,
and the original finite free terms above `a`. It vanishes above `c` and its
canonical map from `P` is a quasi-isomorphism. Transport finite generation and
projectivity along the truncation's termwise isomorphisms and compose its derived
isomorphism with `Q.obj P ≅ C`. -/
theorem isPerfect_of_pseudoCoherent_finiteTorAmplitude
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (hPC : IsPseudoCoherent C)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat.{u} R) a b C) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite R (P.X n)) ∧
      (∀ n : ℤ, Module.Projective R (P.X n)) ∧
      Nonempty (Q.obj P ≅ C) := by
  obtain ⟨a, b, -, hTor⟩ := hTor
  obtain ⟨P, c, hPc, hP, ⟨e⟩⟩ := hPC
  have : P.IsStrictlyLE c := hPc
  have hflat (n : ℤ) : ObjectProperty.flat (P.X n) := by
    have := (hP n).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P c hflat
  have : C.IsGE a := (homologyConcentratedIn_of_torAmplitudeIn hTor).1
  have : P.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e.symm a
  have hex (F : ModuleCat.{u} R) :
      (((MonoidalCategory.tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt
        (a - 1) := by
    have := (hTor F).1
    have : (Q.obj (((MonoidalCategory.tensorRight F).mapHomologicalComplex
        (.up ℤ)).obj P)).IsGE a :=
      TStructure.t.isGE_of_iso
        ((MonoidalCategory.whiskerRightIso e _).symm ≪≫
          QObjTensorSingleFunctorObjIso P hPk F) a
    rw [isGE_Q_obj_iff] at this
    exact CochainComplex.exactAt_of_isGE _ a _
  have hop : Module.Flat R (P.opcycles a) :=
    (ModuleCat.flat_iff_flat _).1
      (ObjectProperty.flat_opcycles_of_exactAt P a (hflat _) (hflat _) hex)
  have hfin (n : ℤ) : Module.Finite R ((P.truncGE a).X n) := by
    obtain hn | rfl | hn := lt_trichotomy n a
    · have : Subsingleton ((P.truncGE a).X n) :=
        ModuleCat.isZero_iff_subsingleton.1
          (CochainComplex.isZero_of_isStrictlyGE _ a n hn)
      infer_instance
    · have := (hP n).2
      have : Module.Finite R (P.opcycles n) :=
        Module.Finite.of_surjective (P.pOpcycles n).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      exact Module.Finite.equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm
    · have := (hP n).2
      exact Module.Finite.equiv (P.truncGEXIso a n hn).toLinearEquiv.symm
  have hfp : Module.FinitePresentation R (P.opcycles a) := by
    have := (hP a).1
    have := (hP a).2
    have := (hP (a - 1)).2
    have : Module.FinitePresentation R (P.X a) :=
      Module.finitePresentation_of_projective R (P.X a)
    apply Module.finitePresentation_of_surjective (P.pOpcycles a).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    have hs := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (P.d (a - 1) a) (P.pOpcycles a) (P.d_pOpcycles _ _))
      (P.opcyclesIsCokernel (a - 1) a (by simp))
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hs
    rw [← hs]
    exact Submodule.fg_range _
  have hproj (n : ℤ) : Module.Projective R ((P.truncGE a).X n) := by
    obtain hn | rfl | hn := lt_trichotomy n a
    · have : Subsingleton ((P.truncGE a).X n) :=
        ModuleCat.isZero_iff_subsingleton.1
          (CochainComplex.isZero_of_isStrictlyGE _ a n hn)
      infer_instance
    · have : Module.Projective R (P.opcycles n) :=
        Module.Flat.projective_of_finitePresentation
      exact Module.Projective.of_equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm
    · have := (hP n).1
      exact Module.Projective.of_equiv (P.truncGEXIso a n hn).toLinearEquiv.symm
  refine ⟨P.truncGE a, ⟨a, c, ?_⟩, hfin, hproj,
    ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ e⟩⟩
  intro n hn
  rcases hn with hn | hn
  · exact CochainComplex.isZero_of_isStrictlyGE _ a n hn
  · obtain hn' | rfl | hn' := lt_trichotomy n a
    · exact CochainComplex.isZero_of_isStrictlyGE _ a n hn'
    · exact (P.truncGEXIsoOpcycles n).isZero_iff.2
        (IsZero.of_epi (P.pOpcycles n) (P.isZero_of_isStrictlyLE c n hn))
    · exact (P.truncGEXIso a n hn').isZero_iff.2 (P.isZero_of_isStrictlyLE c n hn)

end DerivedCategory
