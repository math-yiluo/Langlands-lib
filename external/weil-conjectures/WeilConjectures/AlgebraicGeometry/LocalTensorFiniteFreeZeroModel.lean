/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.LocalKoszulAugmentedCarrier
import WeilConjectures.AlgebraicGeometry.LocalKFlatTensorRoof
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Local zero-differential tensor models

Source: Stacks Project, Tags 0BQY and 068C.
(blueprint: split-local-tensor-finite-free). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The tensor pullback has a local finite-free zero model.

Source: Stacks Project, Tags 0BQY (Koszul computation) and 068C (finite free
resolution of a Koszul-regular quotient).
(blueprint: split-local-tensor-finite-free).

Proof: Write A = Gamma(Y,U) and I = ker(i)(U), and choose m and f from hU.
The Koszul complex of f resolves A/I by `exists_koszul_projective_resolution`.
Reindex its chain degrees n as cochain degrees -n, and sheafify on U. Identify
Spec(A/I) with the inverse image of U under the closed immersion. The sheafified
augmentation is a quasi-isomorphism to the restriction of i_*O_Z, by
`exists_affine_quotient_sheafified_resolution`. Call this bounded finite-free
complex K. Both K and the restriction of P are K-flat resolutions of that same
quotient sheaf. Open restriction preserves K-flatness: extension by zero of an
acyclic test complex is acyclic, and tensor commutes with this extension and
restriction. Thus the isomorphism between these resolutions in the derived
category can be represented by a roof in the K-flat complexes (take a K-flat
replacement of a common roof). Tensor pullback preserves its quasi-isomorphisms:
their cones are acyclic K-flat complexes, whose tensor with O_Z remains acyclic.
The resulting roof identifies the restriction of T with the pullback of K.
Every f_j maps to zero in A/I, so contraction defining the differential of the
pulled-back Koszul complex is zero. The exterior basis of the free rank-m
module gives its degree -n term a free basis of rank binomial(m,n), and its
terms vanish outside [-m,0]. Further restriction to V and to the over site W
is exact, hence maps the roof to quasi-isomorphisms, preserves its zero
morphisms and the bounds, and takes the displayed finite free bases to finite
free bases. This is precisely HasFiniteFreeZeroModel, with E the restricted
pulled-back Koszul complex and L the restricted vertex of the roof.
For m=0 the single degree-zero term is free of rank one; an empty W or a zero
quotient has zero modules, so the same construction still applies. -/
theorem local_tensor_has_finite_free_zero_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (_hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (_hflat : ∀ k : ℤ, SheafOfModules.IsFlat (P.X k)) :
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      HasFiniteFreeZeroModel
        (V.toScheme.ringCatSheaf.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
        ((moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))).obj T) := by
  dsimp only
  intro V U hU
  obtain ⟨m, f, hf, hreg⟩ := hU
  obtain ⟨Q, hQ⟩ := ExteriorAlgebra.exists_koszul_projective_resolution
    (Γ(Y, U.1) : Type u) (i.ker.ideal U) m f hreg hf
  obtain ⟨K, b, hK, hzero, hbound, hfree⟩ :=
    exists_local_koszul_augmented_carrier i V U m f hf Q hQ
  let F := (Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.1.ι) := inferInstance
  have : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.1.ι) := inferInstance
  have : (Scheme.Modules.restrictFunctor U.1.ι).PreservesHomology := inferInstance
  have : QuasiIso a := _hP.1
  have hPa : CochainComplex.IsKFlatTensorResolution (R := U.1.toScheme.sheaf) (F.map a) :=
    by
      refine ⟨?_, isKFlat_restrict U.1.ι P _hP.2⟩
      change QuasiIso
        (((Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)).map a)
      infer_instance
  obtain ⟨L, q, p, hq, hp⟩ :=
    exists_local_kflat_tensor_roof i V U.1 P K _ (F.map a) b hPa hK
  exact ⟨_, L, q, p, hq, hp, hzero, hbound, hfree⟩

end AlgebraicGeometry
