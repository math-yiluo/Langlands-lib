/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineBaseChangeOrdinaryStalkComparison
import WeilConjectures.Algebra.Homology.AffineTensorPullbackStalkCoordinates

/-! # AffineBaseChangeTildeStalkComparison

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-stalk-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

private theorem localizedModule_comp_apply
    {D : Type u} [CommRing D] (S : Submonoid D) {U V W : ModuleCat.{u} D}
    (a : U ⟶ V) (b : V ⟶ W) (x : LocalizedModule S U) :
    LocalizedModule.map S (a ≫ b).hom x =
      LocalizedModule.map S b.hom (LocalizedModule.map S a.hom x) :=
  congrArg (fun z ↦ z x)
    (IsLocalizedModule.map_comp' S
      (LocalizedModule.mkLinearMap S U)
      (LocalizedModule.mkLinearMap S V)
      (LocalizedModule.mkLinearMap S W) a.hom b.hom)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localization of the explicit tensor cohomology arrow agrees with the stalk arrow.
Source: Stacks Project, perfect.tex, Tag 0DJ8, last displayed localization identity;
Tags 06Y6, 01HV and 08IB.
(blueprint: lem-pc-affine-base-change-tilde-stalk-comparison).

Proof: identify A tensor_R R' with A' by the cartesian square and localize its source
cohomology at p. Derived tensor localization identifies this module with the derived
cohomology over the three stalk rings, extended to the fourth ring. This comparison
is determined by the universal derived counits and the commuting A and R' actions,
so it applies to the supplied model m, not only to a particular resolution.
Localize the same K-flat span used for its comparison. Exact localization commutes
with homology, and tilde stalks identify localized M with the stalk complex of its
termwise tilde. Tensor associativity identifies the localized ordinary target with
the stalk of tensor pullback. The equation m.localized_eq says that the localized
arrow is induced by the same termwise coefficient map; m.comparison_eq identifies
its derived counit with the one in the stalk model. Compose with tensorStalkIso,
affineRepresentativeStalkIso and the inverse pullback counit followed by e. These
are precisely the factors defining affineBaseChangeIntoPullback. On the target,
the tilde/Gamma counit and exact tilde homology comparison give precisely
affineDerivedCohomologyStalkIso (with its canonical localization map). Thus both
paths are equal and the source identification is lU. All comparisons are natural
and hold in every degree. Empty prime spectra give no obligations; zero complexes,
identity localizations and zero rings need no exceptional hypotheses. -/
theorem affineBaseChangeTildeModuleMap_localized
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M A') :
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let a := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b
    ∀ p : PrimeSpectrum A',
      let r := affineBaseChangeIntoPullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom φf'))
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom φg'))
        sq K ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) e hc p i
      ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk r).left,
        ∀ x, affineDerivedCohomologyStalkIso A' i p L
          (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = r (lU x)  := by
  have _ := hK
  dsimp only
  intro p
  obtain ⟨lU, hlU⟩ := exists_affineBaseChangeOrdinaryStalkComparison
    R A R' A' φg' φf' hφg' hφf' sq M hM i m p
  refine ⟨lU, ?_⟩
  intro x
  let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
  let V := (affineDerivedCohomologyModules A' i).obj
    (⟨_, hL⟩ : schemeDerivedQCohCategory (Spec (.of A')))
  let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
  let a₀ := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i
    (C.homology i) (Iso.refl _)
  have ha : affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b =
      a₀ ≫ b.hom := by
    dsimp only [affineBaseChangeTildeModuleMap, affineBaseChangeTildeModule, a₀,
      Iso.refl_hom]
    erw [Category.comp_id, Category.assoc]
  have hloc : LocalizedModule.map p.asIdeal.primeCompl
      (affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b).hom x =
        LocalizedModule.map p.asIdeal.primeCompl b.hom.hom
          (LocalizedModule.map p.asIdeal.primeCompl a₀.hom x) := by
    exact (congrArg (fun a ↦ LocalizedModule.map p.asIdeal.primeCompl
      (ModuleCat.Hom.hom a) x) ha).trans
        (localizedModule_comp_apply p.asIdeal.primeCompl a₀ b.hom x)
  rw [hloc]
  rw [affineTensorPullbackHomologyStalkIso_coordinates A A' φg' K hL M e hc i p]
  rw [hlU]
  have hid : ∀ X, ((Spec (.of A')).toRingedSpace.moduleStalkFunctor p).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).map
      ((DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace))).map
      (((Scheme.Modules.tensorPullback
        (Spec.map (CommRingCat.ofHom φg'))).mapHomotopyCategoryFactors (.up ℤ)).inv.app X))) =
        𝟙 _ := fun _ ↦
    (congrArg _ ((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans (CategoryTheory.Functor.map_id _ _)
  simp only [affineBaseChangeIntoPullback, Category.assoc, Functor.map_comp, hid,
    Functor.comp_obj]
  rfl

end AlgebraicGeometry
