/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.PerfectRelativeTensorLocallyBounded
import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Relative finite Tor dimension of a perfect complex

Source: Stacks Project, More on Morphisms, Tag 0B6G, verification of condition (3),
and `more-morphisms-lemma-check-perfect-stalks`.
(blueprint: lem-pc-perfect-relative-finite-tor).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact source locally of finite type over a Noetherian base,
stalkwise finite Tor dimension of the morphism gives relative finite Tor dimension
of every perfect complex. Properness and derived direct image are not needed.
Source: Stacks Project, More on Morphisms, Tag 0B6G, condition (3), and
`more-morphisms-lemma-check-perfect-stalks`, implication (3) to (2).

Proof: a locally finite-type map to a Noetherian scheme is pseudo-coherent.
The stalk criterion for perfect morphisms upgrades the pointwise bounds to finite
Tor bounds on neighbourhoods; this step uses pseudo-coherence, not just compactness.
Thus the structure sheaf locally has finite Tor dimension over the inverse-image
structure sheaf. Intersect this cover with the strictly perfect neighbourhoods of E.
If a representative has terms in [r,s] and the structure sheaf has Tor amplitude
[-d,0], its finite free terms have that amplitude, their retracts do too, and the
finite complex has amplitude [r-d,s], by its filtration by terms. Quasi-compactness
selects finitely many such neighbourhoods and gives one interval [a,b] on X.
Choose a complex K representing E and a K-flat resolution P of its restriction of
scalars. Tensoring P with any inverse-image-structure-sheaf module computes the
relative derived tensor. The stalkwise bounds imply its homology vanishes outside
[a,b], for every module. Enlarge the interval if necessary to have a ≤ b.
For empty X, use [0,0]; the zero complex likewise has amplitude in [0,0].
(blueprint: lem-pc-perfect-relative-finite-tor). -/
theorem perfect_hasFiniteTorDimensionOver
    {X Y : Scheme.{u}} [CompactSpace X] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    HasFiniteTorDimensionOver f E := by
  classical
  let K := DerivedCategory.Q.objPreimage E
  have e : Nonempty (DerivedCategory.Q.obj K ≅ E) :=
    ⟨DerivedCategory.Q.objObjPreimageIso E⟩
  obtain ⟨P, q, hP, _, hq, _⟩ := CochainComplex.exists_isKFlatResolution
    (((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
  have hloc := perfect_relativeTensor_locally_bounded f hperfect E hE K e P hP q hq
  choose U hx a b hab hvanish using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have bounds : ∀ s : Finset X, ∃ c d : ℤ, c ≤ d ∧
      ∀ x ∈ s, c ≤ a x ∧ b x ≤ d := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, 0, le_rfl, by simp⟩
    | @insert x s _ ih =>
      obtain ⟨c, d, hcd, hs⟩ := ih
      refine ⟨min c (a x), max d (b x),
        (min_le_left _ _).trans (hcd.trans (le_max_left _ _)), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ⟨(min_le_left _ _).trans (hs y hy).1,
          (hs y hy).2.trans (le_max_left _ _)⟩
  obtain ⟨c, d, hcd, hbounds⟩ := bounds t
  refine ⟨K, e, P, hP, q, hq, c, d, hcd, ?_⟩
  intro F i hi
  have hz : IsZero ((SheafOfModules.toSheaf _).obj
      ((CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
          (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i)) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro y
    obtain ⟨x, hx', hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    apply hvanish x F i _ y hy
    rcases hi with hi | hi
    · exact Or.inl (hi.trans_le (hbounds x hx').1)
    · exact Or.inr (((hbounds x hx').2).trans_lt hi)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (SheafOfModules.toSheaf _).map_injective
  simp only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

end AlgebraicGeometry.Scheme
