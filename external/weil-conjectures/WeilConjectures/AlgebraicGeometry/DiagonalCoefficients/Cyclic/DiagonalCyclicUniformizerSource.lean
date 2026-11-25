/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteSquare
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPadicTorsionLinearity
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicUniformizerSourceEquation

/-! # The constant-source endpoint of cyclic coefficient continuation

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-cyclic-uniformizer-source).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction CondensedRing.lowerStar
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  HasDerivedCategory.standard Profinite.continuousMapRingSheaf
  upperStarFromPoint

-- Read the endpoint predicate from the proved criterion's stored type.
-- The emitted signature is its ordinary quantified endpoint formula.
local elab "criterionHypothesis% " i:num f:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm f none
  let mut t ← Lean.Meta.inferType e
  for _ in [:i.getNat] do
    let .forallE _ _ body _ ← Lean.Meta.whnf t
      | throwError "criterion has fewer proof arguments"
    t := body
  let .forallE _ domain _ _ ← Lean.Meta.whnf t
    | throwError "criterion has fewer proof arguments"
  if domain.hasLooseBVars then
    throwError "endpoint predicate depends on an earlier proof"
  return domain

private def inverseUnderlyingNatIso
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) :
    e.F.asEquivalence.inverse ⋙ Mod.forget _ ≅
      sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1}) :=
  (Functor.isoWhiskerLeft e.F.asEquivalence.inverse e.underlying).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.F.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _

private theorem inverseUnderlyingNatIso_app
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (inverseUnderlyingNatIso e).app M = UniformizerSquareData.inverseUnderlying e M := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext V x
  rfl

private theorem ordinary_torsion
    (l : ℕ) (n : ℕ) (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((l ^ (n + 1) : ℕ) : ℤ) • 𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj M) = 0 := by
  apply Sheaf.hom_ext
  ext V x
  change ((l ^ (n + 1) : ℕ) : ℤ) • x = 0
  let y : M.obj.obj V := x
  have hy : ((l ^ (n + 1) : ℕ) : ℤ) • y = 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
  exact hy

private theorem lift_forget_iso_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {C : Type*} [Category C]
    (F G : C ⥤ Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
    (e : F ⋙ Mod.forget _ ≅ G ⋙ Mod.forget _) (r : ℕ)
    (hG : ∀ M, ((l ^ r : ℕ) : ℤ) • 𝟙 (G.obj M).X = 0) :
    ∃ s : F ≅ G, ∀ M, (s.hom.app M).hom = e.hom.app M := by
  let s : F ≅ G := NatIso.ofComponents (fun M ↦ Mod.isoMk (e.app M)
    (condensedPadicTorsionLinearity l X (e.app M).hom r (hG M)).smul_hom)
    (by intro M N f; apply Mod.hom_ext; exact e.hom.naturality f)
  exact ⟨s, fun _ ↦ rfl⟩

private theorem torsion_of_iso
    {C : Type*} [Category C] [Preadditive C] {M N : C}
    (v : M ≅ N) (k : ℤ) (h : k • 𝟙 N = 0) : k • 𝟙 M = 0 := by
  apply (cancel_mono v.hom).mp
  simp only [Preadditive.zsmul_comp, Category.id_comp, zero_comp]
  rw [← Category.comp_id v.hom, ← Preadditive.comp_zsmul, h, comp_zero]

private theorem ordinary_restriction_exists
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    ∃ s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight, q.RestrictionNormalized s := by
  let U := Mod.forget (C := Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))
  let e : q.quotientRight ⋙ U ≅ (q.restriction ⋙ q.cyclicRight) ⋙ U :=
    inverseUnderlyingNatIso q.eW ≪≫
      (Functor.isoWhiskerLeft q.restriction (inverseUnderlyingNatIso q.cyclic.eW)).symm
  have torsion (M : Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
      (ModuleCat.{u + 1} A)) :
      ((l ^ (n + 1) : ℕ) : ℤ) • 𝟙 (((q.restriction ⋙ q.cyclicRight).obj M).X) = 0 := by
    let v := UniformizerSquareData.inverseUnderlying q.cyclic.eW (q.restriction.obj M)
    have hv : ((l ^ (n + 1) : ℕ) : ℤ) • 𝟙
        ((sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).obj
            (q.restriction.obj M)) = 0 :=
      ordinary_torsion l n (diagonalSurface Y) (diagonalResidue.{u} l n)
        (cartierResidue_cast l (n + 1)) (q.restriction.obj M)
    change ((l ^ (n + 1) : ℕ) : ℤ) •
      𝟙 (q.cyclic.eW.F.asEquivalence.inverse.obj (q.restriction.obj M)).X = 0
    exact torsion_of_iso v _ hv
  let v (M : Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
      (ModuleCat.{u + 1} A)) :=
    UniformizerSquareData.inverseUnderlying q.eW M ≪≫
      (UniformizerSquareData.inverseUnderlying q.cyclic.eW (q.restriction.obj M)).symm
  have hv (M) : v M = e.app M := by
    apply Iso.ext
    change _ = (inverseUnderlyingNatIso q.eW).hom.app M ≫
      (inverseUnderlyingNatIso q.cyclic.eW).inv.app (q.restriction.obj M)
    have hA' := congrArg Iso.hom (inverseUnderlyingNatIso_app q.eW M)
    have hR' := congrArg Iso.inv
      (inverseUnderlyingNatIso_app q.cyclic.eW (q.restriction.obj M))
    exact congrArg₂ (· ≫ ·) hA'.symm hR'.symm
  obtain ⟨s, hs⟩ := lift_forget_iso_exists l (diagonalSurface Y)
    q.quotientRight (q.restriction ⋙ q.cyclicRight) e (n + 1) torsion
  refine ⟨s, ?_⟩
  intro M
  exact (hs M).trans (congrArg Iso.hom (hv M).symm)

private theorem ordinary_restriction_unique
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA)
    (s t : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) (ht : q.RestrictionNormalized t) : s = t := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  exact (hs M).trans (ht M).symm

/-- The two ordinary restriction functors have a unique underlying-identity
comparison; its derived mate has the prescribed supported constant endpoint.
There is no equality involving a diagonal arrow in this statement.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), composition of coefficient
extensions and their scalar units; the source normalization in the parent
coefficient-square proof, steps 1 and 2.
(blueprint: lem-diagonal-cyclic-uniformizer-source).

Proof: use the underlying and counit isomorphisms of each inverse finite
realization to identify its underlying abelian sheaf with the given ordinary
module. The two resulting Z_l actions coincide: the coefficient isomorphisms
are unital, hA annihilates l^(n+1), and the induced map from the cyclic quotient
is cartierResidueAlgebra. Equivalently, pull the ring maps to W, factor through
the sheafified cyclic quotient and test on its constant generators. Transporting
the identity between the two underlying sheaves therefore gives a module
isomorphism. Its naturality follows after faithful forgetting, where it is the
naturality of the two underlying isomorphisms. Faithful forgetting also proves
uniqueness. Derive this ordinary comparison and take its mate under the actual
composite scalar adjunctions. Endpoint.normalization says that each supported
endpoint is the adjoint of supportMap of its regular coefficient unit.
FiniteSourceComparison.normalization and FiniteRealization.unit_normalization
identify its finite realization with the ordinary pushed constant unit. The
normalization of maps.source agrees with that unit on every constant section;
sheafification's universal property makes the maps equal. Naturality of exact
single comparisons transports this equality to SourceEquation. These arguments
use no root endpoint or diagonal arrow. For an empty base every map is unique;
for the zero coefficient ring the supported map has zero target. -/
theorem diagonalCyclic_uniformizerSource
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    criterionHypothesis% 0 (UniformizerSquareData.endpointSquare l Y E π n A hA q)
       := by
  obtain ⟨s, hs⟩ := ordinary_restriction_exists l Y E π n A hA q
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · exact diagonalCyclic_uniformizerSource_equation l Y E π n A hA q s hs
  · intro t ht
    exact ordinary_restriction_unique l Y E π n A hA q t s ht.1 hs

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
