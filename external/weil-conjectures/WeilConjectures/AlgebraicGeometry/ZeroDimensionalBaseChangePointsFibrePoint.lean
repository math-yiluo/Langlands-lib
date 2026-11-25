/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry

/-! Intermediate fibre facts for zero-dimensional base change.
Source: Stacks Project, schemes.tex Lemma 01JT and algebra.tex Lemma 00P4.
(blueprint: new-zdbp-fibres-point)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Point uniqueness in the base-change fibre. Source: Stacks Project, schemes.tex Lemma 01JT
and algebra.tex Theorem 00FV. The fibre-product point correspondence identifies the fibre
over each c with Spec (κ(c) ⊗ₖ k′); the residue-field isomorphism from Nullstellensatz
identifies this ring with k′, which has one prime. (blueprint: new-zdbp-fibres-point) -/
theorem zeroDimensional_baseChange_fibre_points
    (k k' : Type v) [Field k] [Field k'] [IsAlgClosed k] [Algebra k k']
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    ∀ c : C, ∃! z : (pullback (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{v}),
      (pullback.fst (C ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base z = c := by
  classical
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  let g : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hres := (zeroDimensional_baseChange_geometry k C hC).2.2
  have hsub (T : Scheme.Pullback.Triplet f g) : Subsingleton (Spec T.tensor) := by
    let : IsIso (f.residueFieldMap T.x) := (hres T.x).2
    have : IsIso (Spec.map
        (((Spec (.of k)).residueFieldCongr T.hx).inv ≫
          f.residueFieldMap T.x)) := by
      rw [Spec.map_comp]
      infer_instance
    let : IsIso (Spec.map T.tensorInr) :=
      T.isPullback_SpecMap_tensor.isIso_snd_of_isIso
    exact (Spec.map T.tensorInr).homeomorph.injective.subsingleton
  intro c
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) c (⊥ : PrimeSpectrum k') (Subsingleton.elim _ _)
  refine ⟨z, hz, ?_⟩
  intro w hw
  apply (Scheme.Pullback.carrierEquiv (f := f) (g := g)).injective
  apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
  have hT : Scheme.Pullback.Triplet.ofPoint w = Scheme.Pullback.Triplet.ofPoint z := by
    apply Scheme.Pullback.Triplet.ext
    · exact hw.trans hz.symm
    · exact Subsingleton.elim _ _
  refine ⟨hT, ?_⟩
  let := hsub (Scheme.Pullback.Triplet.ofPoint z)
  exact Subsingleton.elim _ _

end AlgebraicGeometry
