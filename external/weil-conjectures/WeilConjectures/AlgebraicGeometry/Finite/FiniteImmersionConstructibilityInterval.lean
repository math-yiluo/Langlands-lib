/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianStratumModuleRestriction
import WeilConjectures.AlgebraicGeometry.Sf.SfClosedPartitionModuleTest
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite-stage immersion constructibility and unchanged cohomological intervals

Source: main-20261015, proof of proposition-extension-zero-restriction-closed-subscheme--8,
finite-stage paragraph; Stacks Tags 09AA, 09BM, 09AH, 093R and 015F
(blueprint: lem-sf-finite-immersion-constructibility-interval).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The restriction clause of a constructibility witness, using the existing local
constancy and geometric stalk definitions. This merely names the clause for a supplied
immersion, without choosing or changing its domain.
Source: finite-stage paragraph of proposition-extension-zero-restriction-closed-subscheme--8; Stacks
093R (blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionStratum (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (s : S ⟶ X) (M : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf S A (proEtaleConstantModulePullback s A M) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
      Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing S A)
        (proEtaleConstantModulePullback s A M))

/-- The actual fibre-product partition of a supplied constructibility witness still
witnesses constructibility after inverse image. `Stratification.pullback` retains the
index set and uses the schemes `S.domain ν ×[X] Y` with their second projections.
Source: finite-stage paragraph of proposition-extension-zero-restriction-closed-subscheme--8; Stacks
093R (blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionPullbackPartitions (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (S : Stratification X),
    (∀ ν : Fin S.n, sfFiniteImmersionStratum A (S.immersion ν) M) →
      ∀ ν : Fin (S.pullback g).n,
        sfFiniteImmersionStratum A ((S.pullback g).immersion ν)
          (proEtaleConstantModulePullback g A M)

private theorem locallyConstant_universes {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    (h : IsLocallyConstantProEtaleModuleSheaf Y A M) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A M := by
  obtain ⟨I, V, f, hf, h⟩ := h
  exact ⟨I, V, f, hf, fun a ↦ by obtain ⟨N, e⟩ := h a; exact ⟨N, trivial, e⟩⟩

private theorem locallyConstant_of_universes {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    (h : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A M) :
    IsLocallyConstantProEtaleModuleSheaf Y A M := by
  obtain ⟨I, V, f, hf, h⟩ := h
  exact ⟨I, V, f, hf, fun a ↦ by obtain ⟨N, _, e⟩ := h a; exact ⟨N, e⟩⟩

private theorem stratum_of_iso (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (s : S ⟶ X) {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ≅ N) (h : sfFiniteImmersionStratum A s N) :
    sfFiniteImmersionStratum A s M := by
  let es := (proEtaleConstantRingPullback A s).mapIso e
  constructor
  · obtain ⟨I, V, f, hf, hv⟩ := h.1
    refine ⟨I, V, f, hf, fun a ↦ ?_⟩
    obtain ⟨L, ⟨eL⟩⟩ := hv a
    exact ⟨L, ⟨(SheafOfModules.overFunctor _ (V a)).mapIso es ≪≫ eL⟩⟩
  · intro Ω _ _ y
    have : Finite ((geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).obj
        ((proEtaleConstantRingPullback A s).obj N)) := h.2 Ω y
    let et := (geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).mapIso es
    exact Finite.of_injective et.hom (ConcreteCategory.bijective_of_isIso et.hom).1

private theorem constructible_of_iso (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ≅ N) (h : IsConstructibleProEtaleModuleSheaf X A N) :
    IsConstructibleProEtaleModuleSheaf X A M := by
  obtain ⟨S, hp, hS⟩ := h
  exact ⟨S, hp, fun a ↦ stratum_of_iso A (S.immersion a) e (hS a)⟩

private theorem pullback_partitions (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : Y ⟶ X) : sfFiniteImmersionPullbackPartitions A g := by
  intro M S hS a
  have := S.isImmersion a
  obtain ⟨_, _, _, _, _, h⟩ :=
    proEtale_cartesianStratum_moduleRestriction (S.immersion a) g A
  obtain ⟨hl, hs⟩ := h M ⟨locallyConstant_universes (hS a).1, (hS a).2⟩
  exact ⟨locallyConstant_of_universes hl, hs⟩

private theorem pullback_constructible (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (hM : IsConstructibleProEtaleModuleSheaf X A M) :
    IsConstructibleProEtaleModuleSheaf Y A ((proEtaleConstantRingPullback A g).obj M) := by
  obtain ⟨S, hp, hS⟩ := hM
  exact ⟨S.pullback g, hp, pullback_partitions A g M S hS⟩

section DerivedAssembly

private abbrev modules_abelian (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian (proEtaleRingModules X (proEtaleConstantRing X A)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (ProEt.topology X) (A := AddCommGrpCat.{u + 1}))

attribute [local instance] modules_abelian proEtaleRingModules_hasDerivedCategory

end DerivedAssembly

end AlgebraicGeometry.Scheme
