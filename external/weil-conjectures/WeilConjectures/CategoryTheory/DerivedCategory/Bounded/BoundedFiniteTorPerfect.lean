/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel

/-! # Bounded finite Tor amplitude implies perfect

Source: Stacks Project, Tags 0658, 066E, 00NZ
(blueprint: lemma-perfect-complexes-geometric-point).
-/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace DerivedCategory

/-- A bounded complex of finite modules with Tor amplitude in `[a,b]` admits a
bounded finite-projective model in exactly that interval; over a local ring the
model can be chosen finite free.

Source: Stacks Project, Tags 0658, 066E, 00NZ
(blueprint: lemma-perfect-complexes-geometric-point).
Proof:
1. The cycles of `K` are finite by `lem-weil-pbc-noetherian-submodule-finite`;
   their quotient cohomology is finite. Boundedness gives an upper cohomological
   bound, so `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion` makes
   `Q.obj K` pseudo-coherent.
2. By `def-pc-ring-pseudo-coherent-complex`, choose a bounded-above finite-free
   representative. Its terms are flat by
   `lem-sc-affine-standard-cover-finite-free-local-fp-flat`, and it is K-flat by
   `lem-pc-module-bounded-flat-kflat`, in the sense of `def-pc-module-kflat-complex`.
   The comparison `lem-pc-source-kflat-module-tensor-model`, tested with `R[0]`,
   and the ordinary tensor-unit isomorphism show that cohomology vanishes outside
   `[a,b]`, in particular above `b`.
3. Apply `lem-pc-pseudo-coherent-bounded-finite-free-model` to obtain a finite-free
   representative `P` zero above `b`. Again it is flat and K-flat by the preceding
   flatness and K-flatness nodes. The same tensor-model comparison identifies
   `H^(a-1)(P tensor M)` with the corresponding derived tensor cohomology, zero
   for every module `M` by the Tor-amplitude hypothesis.
4. Let `Q` be the cokernel of `P^(a-1) → P^a`. It is flat by
   `lem-pc-module-flat-opcycles-tor-criterion`. Finite bases of these two terms
   give a finite presentation of `Q`, so
   `lem-weil-pbc-finitely-presented-flat-module-projective` makes it finite projective.
5. Form the quotient truncation `E`: zero below `a`, `Q` in degree `a`, and `P`
   above `a`. Its bottom differential descends since consecutive differentials
   compose to zero. The quotient chain map `P → E` preserves cohomology in degree
   `a` by the kernel modulo image formula, in degree `a+1` by surjectivity onto
   `Q`, and in all higher degrees directly; below `a` both cohomologies vanish.
   It is a quasi-isomorphism and becomes invertible by
   `def-weil-abstract-derived-category`. Since `a ≤ b`, the resulting model is
   supported in `[a,b]`. Its other terms are projective by
   `lem-weil-pbc-free-module-projective`, proving `def-pc-perfect-ring-complex`.
6. If `R` is local, `lem-weil-pbc-finite-flat-local-free` makes the bottom finite
   flat term free. Finite generation gives a finite basis, and all other terms
   already are finite free, including the zero terms with their empty bases.
-/
theorem exists_bounded_finite_projective_model_of_torAmplitudeIn
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∃ c d : ℤ, K.IsStrictlyGE c ∧ K.IsStrictlyLE d ∧
      ∀ i : ℤ, Module.Finite R (K.X i))
    (a b : ℤ) (hab : a ≤ b)
    (hTor : torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K)) :
    (∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) ∧
      (∀ i : ℤ, Module.Projective R (E.X i) ∧ Module.Finite R (E.X i)) ∧
      Nonempty (Q.obj E ≅ Q.obj K)) ∧
      IsPerfectRingComplex (Q.obj K) ∧
      (IsLocalRing R →
        ∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
          (∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) ∧
          (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
          Nonempty (Q.obj E ≅ Q.obj K)) := by
  classical
  obtain ⟨_, d, _, hKd, hKfin⟩ := hK
  have : K.IsStrictlyLE d := hKd
  have hPC : IsPseudoCoherent (Q.obj K) := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology R (Q.obj K)).2
    refine ⟨⟨d, fun i hi ↦ isZero_of_isLE (Q.obj K) d i hi⟩, ?_⟩
    intro i
    have := hKfin i
    have : Module.Finite R (K.cycles i) :=
      Module.Finite.of_injective (K.iCycles i).hom
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
    have : Module.Finite R (K.homology i) :=
      Module.Finite.of_surjective (K.homologyπ i).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    have : Module.Finite R
        ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) i).obj K) :=
      inferInstanceAs (Module.Finite R (K.homology i))
    exact Module.Finite.equiv ((homologyFunctorFactors (ModuleCat R) i).app K).toLinearEquiv.symm
  have hconc := homologyConcentratedIn_of_torAmplitudeIn hTor
  have : (Q.obj K).IsGE a := hconc.1
  have : (Q.obj K).IsLE b := hconc.2
  obtain ⟨P, hPb, hP, ⟨e⟩⟩ := exists_finiteFree_model_isStrictlyLE (Q.obj K) b hPC
    (fun i hi ↦ isZero_of_isLE (Q.obj K) b i hi)
  have : P.IsStrictlyLE b := hPb
  have hflat (n : ℤ) : ObjectProperty.flat (P.X n) := by
    have := (hP n).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hflat
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
    Module.Flat.opcycles_of_exactAt P a
      (fun n ↦ (ModuleCat.flat_iff_flat _).1 (hflat n)) hex
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
  have hzero (n : ℤ) (hn : n < a ∨ b < n) : IsZero ((P.truncGE a).X n) := by
    rcases hn with hn | hn
    · exact CochainComplex.isZero_of_isStrictlyGE _ a n hn
    · obtain hn' | rfl | hn' := lt_trichotomy n a
      · exact CochainComplex.isZero_of_isStrictlyGE _ a n hn'
      · exact (P.truncGEXIsoOpcycles n).isZero_iff.2
          (IsZero.of_epi (P.pOpcycles n) (P.isZero_of_isStrictlyLE b n hn))
      · exact (P.truncGEXIso a n hn').isZero_iff.2 (P.isZero_of_isStrictlyLE b n hn)
  let eE : Q.obj (P.truncGE a) ≅ Q.obj K :=
    (asIso (Q.map (P.πTruncGE a))).symm ≪≫ e
  have hPF (n : ℤ) := And.intro (hproj n) (hfin n)
  refine ⟨⟨P.truncGE a, hzero, hPF, ⟨eE⟩⟩, ?_, ?_⟩
  · refine ⟨P.truncGE a, a, b, inferInstance, ?_, hPF, ⟨eE.symm⟩⟩
    exact ((P.truncGE a).isStrictlyLE_iff b).2 (fun n hn ↦ hzero n (Or.inr hn))
  · intro hlocal
    have : IsLocalRing R := hlocal
    refine ⟨P.truncGE a, hzero, fun n ↦ ?_, ⟨eE⟩⟩
    refine ⟨?_, hfin n⟩
    obtain hn | rfl | hn := lt_trichotomy n a
    · have : Subsingleton ((P.truncGE a).X n) :=
        ModuleCat.isZero_iff_subsingleton.1 (hzero n (Or.inl hn))
      infer_instance
    · have : Module.Free R (P.opcycles n) := Module.free_of_flat_of_isLocalRing
      exact Module.Free.of_equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm
    · have := (hP n).1
      exact Module.Free.of_equiv (P.truncGEXIso a n hn).toLinearEquiv.symm

end DerivedCategory
