/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison
import WeilConjectures.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels

/-! # Base and second-factor localization after taking the affine input stalk

Source: Stacks Project, Tags 0DJ8 and 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local irreducible] AlgebraicGeometry.SingleComplexBaseChange.tensorMap
  AlgebraicGeometry.SingleComplexBaseChange.cohomologyModel
  ModuleCat.baseDerivedTensorCohomologyModel
noncomputable section
namespace AlgebraicGeometry

/-- Restriction by the identity ring map fixes all underlying elements. -/
private def identityRestrictionComplexIso
    (S : Type u) [CommRing S] (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars (RingHom.id S)).mapHomologicalComplex (.up ℤ)).obj Q ≅ Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j ↦ (ModuleCat.restrictScalarsId S).app (Q.X j))
    (fun j k _ ↦ ((ModuleCat.restrictScalarsId S).hom.naturality (Q.d j k)).symm)

private theorem identityHomologyIso
    (S : Type u) [CommRing S] (K : ShortComplex (ModuleCat.{u} S)) :
    (K.mapHomologyIso (𝟭 (ModuleCat.{u} S))).hom = 𝟙 _ := by
  let γ : ShortComplex.LeftHomologyMapData (𝟙 K)
      K.homologyData.left (K.homologyData.left.map (𝟭 (ModuleCat.{u} S))) :=
    { φK := 𝟙 _
      φH := 𝟙 _ }
  have hg := γ.homologyMap_comm
  simpa [γ, ShortComplex.mapHomologyIso, ShortComplex.LeftHomologyData.homologyIso,
    ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso,
    ← ShortComplex.leftHomologyMap'_comp] using hg

private theorem identityRestrictionHomology
    (S : Type u) [CommRing S] (Q : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    HomologicalComplex.homologyMap (identityRestrictionComplexIso S Q).inv i ≫
        ((Q.sc i).mapHomologyIso (ModuleCat.restrictScalars (RingHom.id S))).hom =
      (ModuleCat.restrictScalarsId S).inv.app (Q.homology i) := by
  have h := NatTrans.app_homology (ModuleCat.restrictScalarsId S).inv (Q.sc i)
  have hId := identityHomologyIso S (Q.sc i)
  have hInv : ((Q.sc i).mapHomologyIso (𝟭 (ModuleCat.{u} S))).inv = 𝟙 _ := by
    rw [← cancel_epi ((Q.sc i).mapHomologyIso (𝟭 (ModuleCat.{u} S))).hom]
    rw [Iso.hom_inv_id, hId, Category.comp_id]
  rw [hInv, Category.id_comp] at h
  exact h.symm

/-- Identify models in different derived-category universes, retaining the tensor action. -/
private theorem modelUniverseComparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [hR : HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [hB : HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [hR' : HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [hB' : HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : @ModuleCat.BaseDerivedTensorCohomologyModel.{u, u, u, u, u, w}
      R A B _ _ _ _ _ hR hB Q D _ _)
    (n : @ModuleCat.BaseDerivedTensorCohomologyModel.{u, u, u, u, u, wM}
      R A B _ _ _ _ _ hR' hB' Q D _ _)
    (i : ℤ) :
    ∃ e : (@ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
        R A B _ _ _ _ _ hR hB Q D _ _ m i) ≅ n.cohomology i,
      e.hom ≫ n.comparison i = (@ModuleCat.BaseDerivedTensorCohomologyModel.comparison
        R A B _ _ _ _ _ hR hB Q D _ _ m i) := by
  let K := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let q := (identityRestrictionComplexIso A Q).symm
  let s := (identityRestrictionComplexIso (A ⊗[R] B) K).symm
  obtain ⟨kB, hA, hsquare⟩ :=
    @ModuleCat.exists_baseDerivedTensor_restricted_ring_comparison.{u, w, wM}
    R A B D R A B D _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hB hR' hB' Q Q m n
    (RingEquiv.refl R) (RingEquiv.refl A) (RingEquiv.refl B)
    (by ext; rfl) (by ext; rfl) q (RingEquiv.refl (A ⊗[R] B))
    (fun _ _ ↦ rfl) s (fun _ _ _ ↦ rfl) i
  let v : (@ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
        R A B _ _ _ _ _ hR hB Q D _ _ m i) ≃+ n.cohomology i := kB.toLinearEquiv.toAddEquiv
  have hBscalar (b : B) (x : (@ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
        R A B _ _ _ _ _ hR hB Q D _ _ m i)) :
      v ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • v x :=
    kB.hom.hom.map_smul b x
  have hlinear (r : A ⊗[R] B) (x : (@ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
        R A B _ _ _ _ _ hR hB Q D _ _ m i)) : v (r • x) = r • v x := by
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      have ht : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        change a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht, mul_smul, mul_smul]
      exact (hA a _).trans (congrArg
        (fun y : n.cohomology i ↦ (Algebra.TensorProduct.includeLeft (S := R) a) • y)
        (hBscalar b x))
    | add r t hr ht => simp only [add_smul, map_add, hr, ht]
  let e : (@ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
        R A B _ _ _ _ _ hR hB Q D _ _ m i) ≃ₗ[A ⊗[R] B] n.cohomology i :=
    { __ := v
      map_smul' := hlinear }
  refine ⟨e.toModuleIso, ?_⟩
  ext x
  have h := congrArg
    (((K.sc i).mapHomologyIso (ModuleCat.restrictScalars (RingHom.id (A ⊗[R] B)))).hom)
    (hsquare x)
  have hJ := identityRestrictionHomology (A ⊗[R] B) K i
  have hJx := ConcreteCategory.congr_hom hJ
    ((@ModuleCat.BaseDerivedTensorCohomologyModel.comparison
        R A B _ _ _ _ _ hR hB Q D _ _ m i) x)
  change _ = ((K.sc i).mapHomologyIso
    (ModuleCat.restrictScalars (RingHom.id (A ⊗[R] B)))).hom
      (HomologicalComplex.homologyMap s.hom i
        ((@ModuleCat.BaseDerivedTensorCohomologyModel.comparison
        R A B _ _ _ _ _ hR hB Q D _ _ m i) x)) at h
  have hinv := ConcreteCategory.congr_hom
    (((K.sc i).mapHomologyIso
      (ModuleCat.restrictScalars (RingHom.id (A ⊗[R] B)))).inv_hom_id)
    (n.comparison i (v x))
  exact hinv.symm.trans (h.trans hJx)

/-- Scalar adjunction transports the ordinary model comparison to the localized one. -/
private theorem localizedModelUniverseComparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [hR : HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [hB : HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [hR' : HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [hB' : HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : @ModuleCat.BaseDerivedTensorCohomologyModel.{u, u, u, u, u, w}
      R A B _ _ _ _ _ hR hB Q D _ _)
    (n : @ModuleCat.BaseDerivedTensorCohomologyModel.{u, u, u, u, u, wM}
      R A B _ _ _ _ _ hR' hB' Q D _ _)
    (i : ℤ) :
    let Hm := @ModuleCat.BaseDerivedTensorCohomologyModel.cohomology
      R A B _ _ _ _ _ hR hB Q D _ _ m i
    let lm := @ModuleCat.BaseDerivedTensorCohomologyModel.localizedComparison
      R A B _ _ _ _ _ hR hB Q D _ _ m i
    ∃ e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj Hm ≅
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (n.cohomology i),
      e.hom ≫ n.localizedComparison i = lm := by
  intro Hm lm
  obtain ⟨e, he⟩ := @modelUniverseComparison.{u, w, wM}
    R A B D _ _ _ _ _ _ _ hR hB hR' hB' Q m n i
  let om := @ModuleCat.BaseDerivedTensorCohomologyModel.ordinaryToLocalized
    R A B _ _ _ _ _ hR hB Q D _ _ m
  have hot : om = n.ordinaryToLocalized := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (@ModuleCat.BaseDerivedTensorCohomologyModel.ordinaryToLocalized_tmul
      R A B _ _ _ _ _ hR hB Q D _ _ m j 1 x).trans
      (n.ordinaryToLocalized_tmul j 1 x).symm
  let J := ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap (A ⊗[R] B) D)
  have hm := @ModuleCat.BaseDerivedTensorCohomologyModel.localized_eq
    R A B _ _ _ _ _ hR hB Q D _ _ m i
  refine ⟨J.mapIso e, ?_⟩
  apply (adj.homEquiv _ _).injective
  dsimp only [Functor.mapIso_hom]
  rw [adj.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit]
  rw [n.localized_eq, hm]
  rw [← Category.assoc, ← Category.assoc, he]
  erw [← hot]
  simp only [Category.assoc]
  rfl

private theorem spectrumStalkCongr
    (R : Type u) [CommRing R] (x y : PrimeSpectrum R) (h : x = y) :
    StructureSheaf.toStalk R x ≫
        ((Spec (.of R)).presheaf.stalkCongr (.of_eq h)).hom =
      StructureSheaf.toStalk R y := by
  subst y
  simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.comp_id]

/-- Changing equal coefficient maps fixes pure tensors. -/
@[irreducible] private def equalCoefficientComplexIso
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : S →+* T ↦ ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

private theorem equalCoefficientComplexIso_tmul
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalCoefficientComplexIso S T f g h Q).hom.f j (d ⊗ₜ[S, f] x) = d ⊗ₜ[S, g] x := by
  subst g
  unfold equalCoefficientComplexIso
  rfl

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localize only the base and second factor of an already stalk-localized input.
Source: Stacks Project, Tag 0DJ8, base and second-factor part of the localization
identity; Tag 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison).

Proof: the maps from R and R' to their spectrum stalks are prime localizations.
Their maps into the A-stalk and D agree by stalk-map naturality and the cartesian
square. The two restriction equations for psi identify its coefficient actions
with those of the actual tensor-to-stalk map. Apply base and second-factor
localization to Q, keeping the A-stalk unchanged. First compare m with a model
over R and R' in the standard universe using
exists_baseDerivedTensor_restricted_ring_comparison with identity ring equivalences.
Its scalar-action clause and tensor induction upgrade the second-ring-linear
isomorphism to Aq tensor_R R'-linearity. Its ordinary comparison clause,
localized_eq and scalar-extension adjunction give the localized square. Now
apply derivedTensor_base_second_localization_models in that standard universe.
These comparisons preserve the A-stalk action by cohomologyIso_smul.
Extend the resulting tensor-algebra-linear isomorphism to D. The augmentations
of the common resolutions yield a commuting localizedComparison square.
The ordinary targets have the same A-stalk-to-D map, so their canonical chain
isomorphism sends d tensor q to d tensor q. For a compatible tau, set sigma to beta inverse
followed by tau. The formula for beta and its inverse identity show that sigma
agrees with the canonical map on 1 tensor germs of M. These generate C1: beta is an isomorphism, and
1 tensor x generate C. ExtendScalars.hom_ext and D-linearity prove equality
of the chain maps. Taking homology gives the equation for every such sigma.
Zero complexes and identity localizations give the same comparison; a zero A'
has no prime p. No first-factor localization is asserted or used here. -/
theorem exists_affineStalkBaseSecondLocalizationComparison
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
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (p : PrimeSpectrum A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      let Aq : Type u := (Spec.structureSheaf A).presheaf.stalk (g' p)
      let κA := (StructureSheaf.toStalk A (g' p)).hom
      let α := (g'.stalkMap p).hom
      letI : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
      (ψ : Aq ⊗[R] R' →+* D) →
      ψ.comp (algebraMap Aq (Aq ⊗[R] R')) = α →
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom = κ.comp φf' →
      letI := ψ.toAlgebra
      let Q := SingleComplexBaseChange.stalkComplex g' p P
      (m : ModuleCat.BaseDerivedTensorCohomologyModel R Aq R' Q D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let φ₁ := ψ.comp (algebraMap Aq (Aq ⊗[R] R'))
      let C₁ := ((ModuleCat.extendScalars φ₁).mapHomologicalComplex (.up ℤ)).obj Q
      (β : C ≅ C₁) →
      (∀ (j : ℤ) (x : M.X j),
        β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
          (1 : D) ⊗ₜ[Aq, φ₁]
            (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
              (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : (ModuleCat.extendScalars ψ).obj (m.cohomology i) ≅ (Arrow.mk l).left,
        ∀ τ : C ≅ SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          m.localizedComparison i ≫ HomologicalComplex.homologyMap
            (β.inv ≫ τ.hom) i = e.hom ≫ l := by
  intro P f f' g g' D κ Aq κA α ψ hψA hψB Q m C φ₁ C₁ β hβ ρ l
  have _ := hφg'
  have _ := hφf'
  let : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
  let : Algebra (Aq ⊗[R] R') D := ψ.toAlgebra
  let Rp := SingleComplexBaseChange.R f g' p
  let Bp := SingleComplexBaseChange.B f' p
  let κR := (StructureSheaf.toStalk R (f (g' p))).hom
  let κB := (StructureSheaf.toStalk R' (f' p)).hom
  let : Algebra R Rp := κR.toAlgebra
  let : Algebra R' Bp := κB.toAlgebra
  let : Algebra R Bp := (κB.comp (algebraMap R R')).toAlgebra
  let : Algebra Rp Aq := SingleComplexBaseChange.leftAlgebra f g' p
  let : Algebra Rp Bp := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  let : Algebra (SingleComplexBaseChange.R f g' p) (SingleComplexBaseChange.A g' p) :=
    SingleComplexBaseChange.leftAlgebra f g' p
  let : Algebra (SingleComplexBaseChange.R f g' p) (SingleComplexBaseChange.B f' p) :=
    SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  let : IsLocalization (f (g' p)).asIdeal.primeCompl Rp :=
    StructureSheaf.IsLocalization.to_stalk (R := R) (f (g' p))
  let : IsLocalization (f' p).asIdeal.primeCompl Bp :=
    StructureSheaf.IsLocalization.to_stalk (R := R') (f' p)
  let : Algebra (Aq ⊗[Rp] Bp) D :=
    (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  let : Algebra (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
      SingleComplexBaseChange.B f' p)
      (SingleComplexBaseChange.C (X' := Spec (.of A')) p) :=
    (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  let : Algebra Aq D := α.toAlgebra
  let : Algebra R' D := (κ.comp φf').toAlgebra
  let : Algebra Bp D := (f'.stalkMap p).hom.toAlgebra
  have hRpA : IsScalarTower R Rp Aq := IsScalarTower.of_algebraMap_eq' (by
    exact (congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom (algebraMap R A))
        (g' p))).symm)
  have hRB : IsScalarTower R R' Bp := IsScalarTower.of_algebraMap_eq' rfl
  have hRpB : IsScalarTower R Rp Bp := IsScalarTower.of_algebraMap_eq' (by
    have heq := congrArg (fun k : Spec (.of A') ⟶ Spec (.of R) ↦ k p) sq.w
    have hc := spectrumStalkCongr R (f (g' p)) (g (f' p)) heq
    have hn := AlgebraicGeometry.stalkMap_toStalk
      (CommRingCat.ofHom (algebraMap R R')) (f' p)
    exact (congrArg CommRingCat.Hom.hom
      ((congrArg (fun k ↦ k ≫ g.stalkMap (f' p)) hc).trans hn)).symm)
  have hAD : IsScalarTower Aq (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψA.symm
  have hBD : IsScalarTower R' (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψB.symm
  have hleft : (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
      (algebraMap Aq (Aq ⊗[Rp] Bp)) = α := by
    unfold SingleComplexBaseChange.tensorMap
    exact (Classical.choose_spec
      (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).1
  have hright : (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
      Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap p).hom := by
    unfold SingleComplexBaseChange.tensorMap
    exact (Classical.choose_spec
      (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).2
  have hApD : IsScalarTower Aq (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq' hleft.symm
  have hBpD : IsScalarTower Bp (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq' hright.symm
  have hBBpD : IsScalarTower R' Bp D := IsScalarTower.of_algebraMap_eq' (by
    exact (congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom φf') p)).symm)
  have hcoeff : φ₁ = ρ := hψA.trans hleft.symm
  let δ := equalCoefficientComplexIso Aq D φ₁ ρ hcoeff Q
  let hRorig : HasDerivedCategory.{wM} (ModuleCat.{u} R) := inferInstance
  let hBorig : HasDerivedCategory.{wM} (ModuleCat.{u} R') := inferInstance
  let hRstd := HasDerivedCategory.standard (ModuleCat.{u} R)
  let hBstd := HasDerivedCategory.standard (ModuleCat.{u} R')
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := hRstd
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R') := hBstd
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} Rp) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} Bp) := HasDerivedCategory.standard _
  let n := ModuleCat.baseDerivedTensorCohomologyModel R Aq R' Q D
  obtain ⟨e₀, he₀⟩ := @localizedModelUniverseComparison.{u, wM, u + 1}
    R Aq R' D _ _ _ _ _ _ _ hRorig hBorig hRstd hBstd Q m n i
  obtain ⟨eLoc, hLoc, _⟩ :=
    RingTensorCohomology.derivedTensor_base_second_localization_models.{u, u + 1}
      R Aq R' Rp Bp D (f (g' p)).asIdeal.primeCompl (f' p).asIdeal.primeCompl i
  let k := SingleComplexBaseChange.cohomologyModel f f' g g' sq p P
  have hloc := hLoc Q n k δ (equalCoefficientComplexIso_tmul Aq D φ₁ ρ hcoeff Q)
  refine ⟨e₀ ≪≫ eLoc Q n k, ?_⟩
  intro τ hτ
  have hchain : β.hom ≫ δ.hom = τ.hom := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change δ.hom.f j (β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x)) = _
    have hb := congrArg (fun z ↦ δ.hom.f j z) (hβ j x)
    exact hb.trans
      ((equalCoefficientComplexIso_tmul Aq D φ₁ ρ hcoeff Q j 1 _).trans (hτ j x).symm)
  have hσ : β.inv ≫ τ.hom = δ.hom := (β.inv_comp_eq).2 hchain.symm
  exact (congrArg
    (fun t ↦ (@ModuleCat.BaseDerivedTensorCohomologyModel.localizedComparison
      R Aq R' _ _ _ _ _ hRorig hBorig Q D _ _ m i) ≫
        HomologicalComplex.homologyMap t i) hσ).trans
    ((congrArg (fun t ↦ t ≫ HomologicalComplex.homologyMap δ.hom i) he₀.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t ↦ e₀.hom ≫ t) hloc).trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry
