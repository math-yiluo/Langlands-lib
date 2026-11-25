/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Conservativity of covering restrictions with condensed coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3
and the proof of Lemma 4.5 (auxiliary; not a blueprint node).

The module-object presentation is the published category of modules over
`coefficientRing X Λ`, whose underlying ring object is `condensedRingObj Λ.X X`.
These are ordinary unbounded derived categories, with no completion.
`CondensedRing.upperStar` uses extension along the actual coefficient isomorphism
`condensedPullbackHom`. Its exact termwise derived functor is canonically the total
left derived inverse image by `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`.
For an object of the small pro-etale site, localization and the inverse-image
comparison identify this functor with restriction, transporting the coefficient action.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem isIso_of_condensed_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)}
    (f : M ⟶ N) (hf : ∀ i, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).map f)) :
    IsIso f := by
  have hweak (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀) ⟨i⟩
  have : IsIso ((Mod.forget (condensedRingObj Λ.X X)).map f) := by
    apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀
    intro i
    let e : CondensedRing.upperStar Λ.X (𝒰.f i) ⋙ Mod.forget _ ≅
        Mod.forget (condensedRingObj Λ.X X) ⋙ upperStar Ab.{u + 1} (𝒰.f i) :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod (condensedRingObj Λ.X X))
          (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X (𝒰.f i))))
        (Mod.forget _)
    have h := hf i
    have h' : IsIso ((upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
      (NatIso.isIso_map_iff e f).1 (by
        change IsIso ((Mod.forget _).map ((CondensedRing.upperStar Λ.X (𝒰.f i)).map f))
        infer_instance)
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) (hweak i)) f.hom).1 h'
  exact isIso_of_reflects_iso f (Mod.forget _)

/-- Derived restrictions along any pro-etale covering family jointly detect isomorphisms
and zero objects for arbitrary commutative condensed coefficients.
Source: HRS Section 3 and Lemma 4.5, proof, conservativity of restriction
(auxiliary; not a blueprint node).

Proof plan:
1. By lem-weil-proetale-weakly-etale-localization the site of each cover member is
   the slice site. Clause 1 of lem-sfb-proetale-object-inverse-image-restriction
   identifies inverse image of arbitrary ring and abelian sheaves with restriction.
   Compose the coefficient comparison with alpha_u = condensedPullbackHom.
   Scalar extension along this isomorphism just transports the action: the tensor
   comparison sends m tensor r to alpha_u.inv(r)m, with inverse m to m tensor 1.
   Thus the exact inverse image of prose-03-02 is restriction,
   and its derived functor is exact termwise restriction. No constant-ring clause is used.
2. For each site object V, proposition-topos-functoriality--1 gives the covering by
   V times_X U_i. Every member maps to U_i. The sieve of objects admitting a map
   to some U_i is therefore covering, the CoversTop hypothesis of
   lem-sfb-sheaf-cover-local-isomorphism.
3. Apply that criterion to the underlying abelian-sheaf map of a module map whose
   restrictions are invertible. Its inverse is linear: applying the original map
   to b(ry) and r b(y) gives ry in both cases, and injectivity cancels the map.
   This is an inverse in the module category of situation-conventions.
4. The natural cohomology comparison of lem-weil-pbc-exact-functor-complex-cohomology
   descends through the localization of def-weil-abstract-derived-category:
   naturality for chain maps also holds for inverses of quasi-isomorphisms, hence
   for all derived morphisms. Thus H^n(u_i^* f) is the restriction of H^n(f).
5. If all u_i^* f are invertible, step 4 and step 3 make every H^n(f) invertible.
   Apply lem-weil-pbc-unbounded-derived-iso-cohomology to conclude IsIso f.
   Conversely each restriction is a functor and preserves isomorphisms.
6. If all restrictions of K are zero, apply step 5 to K to 0: additive exact
   restriction preserves zero objects. This proves K is zero. The empty covering
   of the empty scheme is included, since its sheaf condition forces zero modules.
No boundedness, quasi-compactness, nonemptiness or finiteness condition is used. -/
theorem condensed_cover_restriction_conservative
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (f : K ⟶ L),
      IsIso f ↔ ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      (∀ i : 𝒰.I₀,
        IsZero ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) →
      IsZero K) := by
  have hIso {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))}
      (f : K ⟶ L)
      (hf : ∀ i, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) :
      IsIso f := by
    rw [DerivedCategory.isIso_iff]
    intro n
    apply isIso_of_condensed_cover Λ X 𝒰
    intro i
    exact (NatIso.isIso_map_iff
      ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f))
        have := hf i
        infer_instance)
  constructor
  · intro K L f
    exact ⟨fun _ i ↦ inferInstance, fun hf ↦ hIso f hf⟩
  · intro K hK
    open ZeroObject in
    have h : IsIso (0 : K ⟶ 0) := hIso _ fun i ↦
      (hK i).isIso
        ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map_isZero
          (isZero_zero _)) _
    exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

end AlgebraicGeometry.ProEtale
