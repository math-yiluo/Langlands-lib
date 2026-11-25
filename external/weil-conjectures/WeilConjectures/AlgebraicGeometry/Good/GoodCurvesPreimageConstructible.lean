/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesPreimageBoundary

/-!
# Constructibility on the open part of a good-curves compactification

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof after
replacing the dense open by its inverse image under the finite good-curves cover.
(blueprint: lem-weil-pbc-good-curves-preimage-constructible)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private noncomputable def constantSinglePullbackIso
    {X S : Scheme.{u}} (f : X ⟶ S) {Λ : Type (u + 1)} [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusSingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).app M)

private theorem binary_support
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U Z X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : ModuleCat.{u + 1} Λ) (c : Compactification f)
    (cU : Compactification (j ≫ f)) (cZ : Compactification (i ≫ f))
    (hU : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))
    (hZ : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))))) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT, _⟩ :=
    exists_compactSupport_openClosed_triangle Λ f j i
      hij K c cU cZ
  let P := _root_.DerivedCategory.homologyProperty
    (constructibleSheaf (ModuleCat.{u + 1} Λ) S)
  have h₁ : P T.obj₁ := P.prop_of_iso
    (e₁ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).mapIso
        (constantSinglePullbackIso j M))).symm hU
  have h₃ : P T.obj₃ := P.prop_of_iso
    (e₃ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).mapIso
        (constantSinglePullbackIso i M))).symm hZ
  exact P.prop_of_iso e₂ (P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃)

private def CSP (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : ModuleCat.{u + 1} Λ) : Prop :=
  ∀ (c : Compactification f) (q : ℤ), Scheme.IsConstructibleSheaf
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))

private theorem finite_support
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (S : Scheme.{u}) [IsNoetherian S] (M : ModuleCat.{u + 1} Λ) :
    ∀ (n : ℕ) (C : Fin n → Scheme.{u}) [IsNoetherian (∐ C)]
      (f : (∐ C) ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
      (∀ k, CSP Λ (Limits.Sigma.ι C k ≫ f) M) → CSP Λ f M := by
  intro n
  induction n with
  | zero =>
    intro C _ f _ _ _ h c q
    have : IsEmpty (∐ C : Scheme.{u}) :=
      ⟨fun x ↦ by
        obtain ⟨k, y, hy⟩ := (sigmaOpenCover C).exists_eq x
        exact Fin.elim0 k⟩
    have hz := Scheme.Etale.isZero_sheaf_of_isEmpty
      ((constantSheaf (∐ C).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    exact Scheme.IsConstructibleSheaf.of_isZero
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).map_isZero
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).map_isZero
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map_isZero hz)))
  | succ n ih =>
    intro C _ f _ _ _ h c
    let G : Fin n → Scheme.{u} := fun k ↦ C k.succ
    let j : C 0 ⟶ ∐ C := Limits.Sigma.ι C 0
    let i : (∐ G) ⟶ ∐ C := Limits.Sigma.desc fun k ↦ Limits.Sigma.ι C k.succ
    have : IsOpenImmersion i := isOpenImmersion_sigmaDesc G (fun k ↦ Limits.Sigma.ι C k.succ) (by
      intro a b hab
      exact TopologicalSpace.Opens.coe_disjoint.mpr
        (disjoint_opensRange_sigmaι C a.succ b.succ (by
          intro he; exact hab (Fin.succ_injective n he))))
    have hrange : Set.range i = (Set.range j)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩ ⟨v, hv⟩
        obtain ⟨k, z, hz⟩ := (sigmaOpenCover G).exists_eq y
        change Limits.Sigma.ι G k z = y at hz
        rw [← hz] at hv
        have he : Limits.Sigma.ι C 0 v = Limits.Sigma.ι C k.succ z := by
          simpa [j, i, ← Scheme.Hom.comp_apply] using hv
        have hk := congrArg Sigma.fst ((sigmaι_eq_iff C _ _ _ _).mp he)
        exact Fin.succ_ne_zero k hk.symm
      · intro hx
        obtain ⟨k, z, hz⟩ := (sigmaOpenCover C).exists_eq x
        change Limits.Sigma.ι C k z = x at hz
        rw [← hz] at hx ⊢
        cases k using Fin.cases with
        | zero => exact (hx ⟨z, rfl⟩).elim
        | succ k =>
          refine ⟨Limits.Sigma.ι G k z, ?_⟩
          simp [i, ← Scheme.Hom.comp_apply]
          rfl
    have : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i (by
      rw [hrange]
      exact j.isOpenEmbedding.isOpen_range.isClosed_compl)
    have : IsLocallyNoetherian (∐ G) := isLocallyNoetherian_of_isOpenImmersion i
    have : TopologicalSpace.NoetherianSpace (∐ G : Scheme.{u}) :=
      (TopologicalSpace.noetherianSpace_iff_of_homeomorph
        i.isEmbedding.toHomeomorph).2 inferInstance
    have : IsNoetherian (∐ G) := {}
    have : TopologicalSpace.NoetherianSpace (C 0) :=
      (TopologicalSpace.noetherianSpace_iff_of_homeomorph
        j.isEmbedding.toHomeomorph).2 inferInstance
    have : HasCompactification f := c.hasCompactification
    have : HasCompactification (i ≫ f) :=
      HasCompactification.comp_of_isOpenImmersion f i
    have : HasCompactification (j ≫ f) :=
      HasCompactification.comp_of_isOpenImmersion f j
    let ci := HasCompactification.compactification (i ≫ f)
    let cj := HasCompactification.compactification (j ≫ f)
    apply binary_support Λ f j i hrange M c cj ci
    · exact h 0 cj
    · apply ih G (i ≫ f)
      intro k
      have he : Limits.Sigma.ι G k ≫ (i ≫ f) = Limits.Sigma.ι C k.succ ≫ f := by
        simp [i]
      rw [he]
      exact h k.succ

/-- A finite constant module has constructible cohomology in every degree.

This helper is shared by the constant-shriek proof and is stated publicly so
that the latter does not duplicate the same theorem in its own module. -/
theorem constantSingle_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have : Module.Finite Λ M := Module.Finite.of_finite
  have : Scheme.IsFiniteSheaf F := by
    constructor
    intro Ω _ _ s
    have : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ((ModuleCat.isFinitelyGenerated_iff M).mpr inferInstance).of_iso
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso M).symm
  have : Scheme.IsFiniteLocallyConstantSheaf F := {}
  have : Scheme.IsConstructibleSheaf F :=
    ⟨Scheme.Stratification.trivial X, fun _ ↦
      Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩
  intro q
  have := (DerivedCategory.boundedConstructible_singleFunctor_obj
    F 0).2 q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app F).symm)

/-- Constructibility on each proper model implies constructibility on the inverse image
of a fibrewise dense open in a finite good-curves diagram.

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof from
"Let Z' be the complement" through the finite sum of the proper smooth families.
(blueprint: lem-weil-pbc-good-curves-preimage-constructible)

Proof: The geometric preimage-boundary theorem gives an open immersion of the
pullback P into the proper Noetherian coproduct C, over V, whose closed
complement Z is quasi-finite over V. The finite constant complex on Z has
constructible cohomology, so quasi-finite shriek preserves its constructibility.

Assemble constructibility on C by induction on the finite component family. The
empty coproduct has no points; every sheaf and the resulting compact-support object
are zero. In the successor case, the first component is open and its complementary
finite coproduct is both open and closed. The disjoint component ranges and their
open cover prove the complement equality. The induction hypothesis, hmodels for the
first component, and the open-closed compact-support triangle give constructibility
on C. This avoids a separate Mayer-Vietoris or compactification-independence lemma.

Finally apply the open-closed triangle to P in C and Z. Constant-pullback
isomorphisms identify the three constant complexes. Its second and third vertices
have constructible cohomology by the two preceding arguments. The Serre homology
property is triangulated and hence contains its first vertex, giving the result
for every prescribed compactification cW. -/
theorem goodCurvesPreimage_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hmodels : ∀ (i : Fin n) (ci : Compactification (p i ≫ t i)) (q : ℤ),
      Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ci).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf (Ybar i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))
    (cW : Compactification (Limits.pullback.snd ν W.ι ≫ W.ι ≫ f)) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf (Limits.pullback ν W.ι).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let C : Scheme.{u} := ∐ Ybar
  let fc : C ⟶ V := Limits.Sigma.desc fun i ↦ p i ≫ t i
  obtain ⟨hCnoeth, hfc, O, e, Z, i, hi, hrange, he, hqf⟩ :=
    goodCurvesPreimage_boundary f n T Y Ybar t j p ν hcomm ht hj hjp hp W hWi
  have : IsNoetherian C := hCnoeth
  have : IsProper fc := hfc
  have : IsClosedImmersion i := hi
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsNoetherian Z := {}
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (O : Set C))
  let w : Limits.pullback ν W.ι ⟶ C := e.hom ≫ O.ι
  have : IsOpenImmersion w := inferInstance
  have : QuasiCompact w := inferInstance
  have hw : Set.range w = (O : Set C) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.hom y).2
    · intro hx
      obtain ⟨y, hy⟩ := e.hom.surjective ⟨x, hx⟩
      refine ⟨y, ?_⟩
      change O.ι (e.hom y) = x
      rw [hy]
      rfl
  have hmodels' : ∀ i, CSP Λ (Limits.Sigma.ι Ybar i ≫ fc) M := by
    intro i
    have he' : Limits.Sigma.ι Ybar i ≫ fc = p i ≫ t i := by simp [fc]
    rw [he']
    exact hmodels i
  have hC := finite_support Λ V M n Ybar fc hmodels'
  let cC := HasCompactification.compactification fc
  let cZ := HasCompactification.compactification (i ≫ fc)
  have : QuasiCompact cZ.i := cZ.quasiCompact_openImmersion inferInstance
  have hZ : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M)))) := by
    intro q
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (constructibleCohomology_lowerShriek_of_quasiFinite Λ
        (i ≫ fc) hqf
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))
        (constantSingle_constructible Λ _ M) cZ q)
  have hP : CSP Λ (w ≫ fc) M := by
    intro cP
    let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    obtain ⟨Q, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hQ, _⟩ :=
      exists_compactSupport_openClosed_triangle Λ fc w i
        (by rw [hrange, hw]) K cC cP cZ
    let P := _root_.DerivedCategory.homologyProperty
      (constructibleSheaf (ModuleCat.{u + 1} Λ) V)
    have h₂ : P Q.obj₂ := P.prop_of_iso e₂.symm (hC cC)
    have h₃ : P Q.obj₃ := P.prop_of_iso
      (e₃ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).mapIso
          (constantSinglePullbackIso i M))).symm hZ
    exact P.prop_of_iso
      (e₁ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cP).mapIso
          (constantSinglePullbackIso w M)))
      (P.ext_of_isTriangulatedClosed₁ Q hQ h₂ h₃)
  have hew : w ≫ fc = Limits.pullback.snd ν W.ι ≫ W.ι ≫ f := by
    simpa only [w, Category.assoc] using he
  rw [hew] at hP
  exact hP cW

end AlgebraicGeometry.Etale
