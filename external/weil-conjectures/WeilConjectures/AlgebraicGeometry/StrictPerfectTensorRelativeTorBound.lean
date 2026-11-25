/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorModel
import WeilConjectures.AlgebraicGeometry.OpenKFlatTensorHomologyComparison
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The relative Tor bound on a strictly perfect chart

Source: Stacks Project, Tags 0DJQ and 08CI, the local relative Tor calculation.
(blueprint: lem-pc-strict-perfect-tensor-relative-tor-bound).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem bounded_tensor_single_isZero
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasColimits C]
    (T : CochainComplex C ℤ) (F : C) (a b : ℤ)
    (hb : ∀ n : ℤ, n < a ∨ b < n → IsZero (T.X n))
    (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((CochainComplex.mapBifunctor T
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj F)
      (curriedTensor C)).homology i) := by
  let N := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj F
  let B := CochainComplex.mapBifunctor T N (curriedTensor C)
  have hz : IsZero (B.X i) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = i at hpq
    have hs : IsZero (T.X p ⊗ N.X q) := by
      by_cases hq : q = 0
      · subst q
        have hp : p = i := by omega
        subst p
        exact (tensorRight (N.X 0)).map_isZero (hb i hi)
      · exact (tensorLeft (T.X p)).map_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
    exact hs.eq_of_src _ _
  exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A strictly perfect chart of amplitude `[a,b]` gives the relative tensor bound
`[a+c,b+d]` on that chart, for any global relative K-flat model of the tensor.
Source: Stacks Project, Tag 0DJQ, proof, and Tag 08CI, implication (2) to (1).

Proof: On U, represent E by L. Its terms are retracts of finite free modules,
so they are flat over O_U. Since L is bounded, it is K-flat over O_U, and
L tensor G|_U represents the restriction of E tensor^L G. Its degree n term
is the finite direct sum of L^p tensor G^q for p+q=n. If n is outside
[a+c,b+d], every summand vanishes by one of the two degree bounds.
For relative flatness, choose an affine neighbourhood V of f(x). On affine
neighbourhoods W of x inside f^{-1}V the sections of G^q are flat over O_S(V).
Their filtered colimit is flat over O_S(V), and localization gives flatness
over O_{S,f(x)}. Thus G^q restricted to U is flat over (f^{-1}O_S)|_U.
Tensoring with L^p makes a retract of a finite sum of these flat modules;
finite sums and retracts preserve flatness. The bounded total complex is
therefore K-flat over (f^{-1}O_S)|_U. The quasi-isomorphism q and the model
isomorphisms identify its relative derived tensors with those computed by
P|_U. Open restriction is exact, preserves total tensors and K-flatness,
and hence identifies the restriction of each homology sheaf with the local
homology. Tensoring the bounded flat model with F[0] leaves its degree
bounds unchanged, so the homology sheaf restricts to zero on U. Its sections
on every V <= U are zero. This also covers empty U, zero complexes, and
reversed degree bounds, when the bounded complex in question is zero.
(blueprint: lem-pc-strict-perfect-tensor-relative-tor-bound). -/
theorem strictPerfect_tensor_relativeTor_bound
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L)
    (a b c d : ℤ)
    (hLb : ∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∀ (P : CochainComplex (SheafOfModules.{u} A) ℤ),
      CochainComplex.IsKFlatTensor (R := R) P →
      ∀ q : P ⟶ ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
              (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K,
        QuasiIso q → ∀ (F : SheafOfModules.{u} A) (i : ℤ),
          i < a + c ∨ b + d < i → ∀ (V : X.Opens), V ≤ U →
            IsZero ((SheafOfModules.evaluation A (Opposite.op V)).obj
              ((CochainComplex.mapBifunctor P
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) := by
  dsimp only
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  obtain ⟨T, H, hb, hT, s, t, hs, ht⟩ :=
    strictPerfect_relativeTensor_model f E G K eK U L hL eL a b c d hLb hGb hGflat
  intro P hP q hq F i hi V hVU
  obtain ⟨e⟩ := CochainComplex.open_kFlat_tensor_homology_comparison
    R U P _ hP q hq T H hT s t hs ht F i
  let C := SheafOfModules.{u} ((sheafCompose
    ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))
  let : MonoidalCategory C := SheafOfModules.monoidalCategory (R.over U)
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
  have hz := bounded_tensor_single_isZero (C := C) T
    ((SheafOfModules.overFunctor.{u} A U).obj F) (a + c) (b + d) hb i hi
  have hlocal := hz.of_iso e
  let ev := SheafOfModules.evaluation (A.over U)
    (Opposite.op (Over.mk (homOfLE hVU)))
  exact ev.map_isZero hlocal


end AlgebraicGeometry.Scheme
