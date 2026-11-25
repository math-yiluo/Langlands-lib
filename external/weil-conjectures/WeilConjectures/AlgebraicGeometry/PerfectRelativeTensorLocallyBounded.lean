/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.AlgebraicGeometry.StalkTorDimensionLocallyUniform
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Local relative Tor bounds for perfect complexes

Source: Stacks Project, Tags 069C and 0B6G, verification of condition (3).
(blueprint: lem-pc-perfect-relative-tensor-locally-bounded).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Any K-flat model of the scalar restriction of a perfect complex has relative
Tor bounds uniform on a neighbourhood of each point. No compactness is assumed.
Source: Stacks Project, Tag 069C, implication (3) to (2), and Tag 0B6G,
verification of condition (3); Cohomology, Tags 08CG and 09U9.

Proof: local finite type over a Noetherian base makes the morphism pseudo-coherent.
Tag 069C therefore gives an open neighbourhood on which the structure sheaf has
Tor amplitude [-d,0] over the inverse-image structure sheaf. Intersect it with a
strictly perfect neighbourhood of E, shrinking to an affine neighbourhood if needed.
Let [r,s] contain the degrees of this bounded model. Its terms are retracts of finite
free modules, so each term has amplitude [-d,0]. The finite filtration of the model
by its terms and the long exact cohomology sequences of derived tensor give amplitude
[r-d,s]. Enlarge this interval to make its endpoints ordered.
Apply the K-flat stalk criterion to the ringed space (X, f⁻¹O_Y), so P has
K-flat stalks. Exact restriction transports the representative isomorphism to the
strictly perfect neighbourhood. At each stalk, q identifies P with that bounded
model after scalar restriction in the derived category. A common K-flat replacement
and invariance of tensor under quasi-isomorphisms between K-flat complexes show
that P computes the same derived tensor. Taking stalks is exact and commutes with
tensor and its total complex,
so this amplitude means that every indicated stalk of its tensor homology vanishes.
The interval and neighbourhood are chosen before the test module F, hence work for
all F. A zero local model admits [0,0]; there is no point to consider on an empty X.
(blueprint: lem-pc-perfect-relative-tensor-locally-bounded). -/
theorem perfect_relativeTensor_locally_bounded
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj K ≅ E))
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := TopCat.Sheaf.inverseImageRing f.base Y.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) (hq : QuasiIso q) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, a ≤ b ∧
      ∀ F : SheafOfModules.{u} ((sheafCompose
          (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)),
        ∀ i : ℤ, i < a ∨ b < i → ∀ y : X, y ∈ U →
          IsZero ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
              ((SheafOfModules.toSheaf _).obj
                ((CochainComplex.mapBifunctor P
                  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                  (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
                    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i))) := by
  intro x
  obtain ⟨U, hxU, d, hU⟩ := stalkTorDimension_locally_uniform f hperfect x
  obtain ⟨V, hxV, L, hL, ⟨eL⟩⟩ := hE x
  obtain ⟨r, s, hdegrees⟩ := hL.1
  obtain ⟨eK⟩ := e
  have eKL : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj L) :=
    ⟨((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.mapIso eK) ≪≫ eL⟩
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, min (r - (d : ℤ)) s, s, min_le_right _ _, ?_⟩
  intro F i hi y hy
  apply strictlyPerfect_relativeTensor_stalk_bound f K V L hL eKL r s hdegrees
    y hy.2 d (hU y hy.1) P hP q hq F i
  rcases hi with hi | hi
  · exact Or.inl (lt_of_lt_of_le hi (min_le_left _ _))
  · exact Or.inr hi


end AlgebraicGeometry.Scheme
