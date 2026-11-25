/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # Finite-sheet coordinates for the two canonical adjunction maps -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem weaklyEtalePullback_faithful
    {X U : Scheme.{u}} (p : U ⟶ X) [WeaklyEtale p] [QuasiCompact p] [Surjective p] :
    (ProEtale.upperStar Ab.{u + 1} p).Faithful := by
  let L := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)
  have : L.IsCoverDense (Scheme.ProEt.topology X) := by
    apply Functor.isCoverDense_of_generate_singleton_functor_π_mem
    intro V
    let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj V
    let π : L.obj W ⟶ V :=
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ p inferInstance trivial).counit.app V
    refine ⟨W, π, Scheme.ProEt.mem_topology_iff.mpr
      ⟨Presieve.singleton π, ?_, Sieve.le_generate _⟩⟩
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton (pullback.fst V.hom p) ∈ Scheme.proetalePrecoverage V.left
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale _)
  have : (ProEtale.localizationRestriction Ab.{u + 1} p inferInstance).Faithful := by
    constructor
    intro F G α β h
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    let G' := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj G
    apply Functor.IsCoverDense.ext L G' V.unop
    intro W f
    change G.obj.map f.op (α.hom.app V x) = G.obj.map f.op (β.hom.app V x)
    have hnα := congrArg (fun z ↦ z x) (α.hom.naturality f.op)
    have hnβ := congrArg (fun z ↦ z x) (β.hom.naturality f.op)
    have hh := congrArg (fun z ↦ z.hom.app (Opposite.op W)) h
    change α.hom.app (Opposite.op (L.obj W)) = β.hom.app (Opposite.op (L.obj W)) at hh
    change α.hom.app (Opposite.op (L.obj W)) (F.obj.map f.op x) =
      G.obj.map f.op (α.hom.app V x) at hnα
    change β.hom.app (Opposite.op (L.obj W)) (F.obj.map f.op x) =
      G.obj.map f.op (β.hom.app V x) at hnβ
    rw [← hnα, ← hnβ, hh]
  exact Functor.Faithful.of_iso
    (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} p inferInstance).symm
private theorem weaklyEtaleUnit_mono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X U : Scheme.{u}} (p : U ⟶ X) [WeaklyEtale p] [QuasiCompact p] [Surjective p]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((upperStarLowerStarAdjunction Λ p).unit.app P) := by
  have : (ProEtale.upperStar Ab.{u + 1} p).Faithful := weaklyEtalePullback_faithful p
  let T := (ProEtale.upperStar Ab.{u + 1} p).mapMod (condensedRingObj Λ X) ⋙
    Mod.comap (inv (condensedPullbackHom Λ p))
  have : T.Faithful := by dsimp [T]; infer_instance
  have : (upperStar Λ p).Faithful := Functor.Faithful.of_iso
    (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ p))).symm
  infer_instance

/-- Freeness of `g^* M` is inherited by `(f ≫ g)^* M`. -/
private lemma isFree_upperStar_comp {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree _ (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj M)) :
    Mod.IsFree _ (((ProEtale.upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) :=
  (ProEtale.free_pullback_comp_iff f g M).mpr (free_pullback f h)

/-- Three properties of maps to `X` that hold on pro-étale covers and are stable under
precomposition hold together on one cover by affine (hence compact) schemes. -/
private theorem commonCompactCover {X : Scheme.{u}}
    (PA PB PD : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hPA : ∀ {Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X), PA g → PA (f ≫ g))
    (hPB : ∀ {Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X), PB g → PB (f ≫ g))
    (hPD : ∀ {Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X), PD g → PD (f ≫ g))
    (hA : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀, PA (C.f s))
    (hB : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀, PB (C.f s))
    (hD : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀, PD (C.f s)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      CompactSpace (C.X s) ∧ PA (C.f s) ∧ PB (C.f s) ∧ PD (C.f s) := by
  obtain ⟨C₁, h₁⟩ := hA
  obtain ⟨C₂, h₂⟩ := hB
  obtain ⟨C₃, h₃⟩ := hD
  let C₁₂ := C₁.bind (fun i ↦ C₂.pullback₁ (C₁.f i))
  have h₁₂ (s : C₁₂.I₀) : PA (C₁₂.f s) ∧ PB (C₁₂.f s) := by
    rcases s with ⟨i, j⟩
    constructor
    · exact hPA _ _ (h₁ i)
    · change PB (pullback.fst (C₁.f i) (C₂.f j) ≫ C₁.f i)
      rw [pullback.condition]
      exact hPB _ _ (h₂ j)
  let C₁₂₃ := C₁₂.bind (fun i ↦ C₃.pullback₁ (C₁₂.f i))
  have h₁₂₃ (s : C₁₂₃.I₀) : PA (C₁₂₃.f s) ∧ PB (C₁₂₃.f s) ∧ PD (C₁₂₃.f s) := by
    rcases s with ⟨i, j⟩
    refine ⟨hPA _ _ (h₁₂ i).1, hPB _ _ (h₁₂ i).2, ?_⟩
    change PD (pullback.fst (C₁₂.f i) (C₃.f j) ≫ C₁₂.f i)
    rw [pullback.condition]
    exact hPD _ _ (h₃ j)
  let C := C₁₂₃.bind (fun i ↦
    (C₁₂₃.X i).affineCover.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage)
  refine ⟨C, fun s ↦ ?_⟩
  rcases s with ⟨i, j⟩
  refine ⟨?_, hPA _ _ (h₁₂₃ i).1, hPB _ _ (h₁₂₃ i).2.1, hPD _ _ (h₁₂₃ i).2.2⟩
  change CompactSpace (((C₁₂₃.X i).affineCover).X j)
  infer_instance

/-- The pullback of module objects over `Λ` is the pullback of underlying sheaves followed by
restriction along the inverse of the comparison of coefficient rings. -/
private noncomputable def normalizedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    upperStar Λ f ≅ (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X) ⋙
      Mod.comap (inv (condensedPullbackHom Λ f)) :=
  Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

private theorem localizedAdjoint_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X Y : Scheme.{u})
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) [T.Additive]
    [PreservesColimitsOfShape ℕ T]
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (D : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (D' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y))
    (k : T.obj ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj D) ≅
      (Mod.comap (coefficientMap (integralScalarMap ℓ E) Y)).obj D')
    (f : B ⟶ (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj D)
    [IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap ℓ E) X)).homEquiv B D).symm f)] :
    IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap ℓ E) Y)).homEquiv (T.obj B) D').symm
        (T.map f ≫ k.hom)) := by
  let a := integralScalarMap ℓ E
  let UX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap a X)
  let UY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap a Y)
  let adjX := Mod.extendRestrictAdjunction (coefficientMap a X)
  let adjY := Mod.extendRestrictAdjunction (coefficientMap a Y)
  let q := (adjX.homEquiv B D).symm f
  let q' := (adjY.homEquiv (T.obj B) D').symm (T.map f ≫ k.hom)
  have hq : adjX.unit.app B ≫ UX.map q = f :=
    (adjX.homEquiv B D).apply_symm_apply f
  have hq' : adjY.unit.app (T.obj B) ≫ UY.map q' = T.map f ≫ k.hom :=
    (adjY.homEquiv (T.obj B) D').apply_symm_apply _
  let c := integralModuleLocalizationCocone ℓ E X B
  let σ := Mod.smulSequenceCompIso T B ℓ
  let d₀ := (Cocone.precompose σ.inv).obj (T.mapCocone c)
  let v : d₀.pt ≅ UY.obj D' := T.mapIso (UX.mapIso (asIso q)) ≪≫ k
  let d := d₀.extend v.hom
  obtain ⟨hc⟩ := integralModuleLocalization_isColimit ℓ E X B
  have hd₀ : IsColimit d₀ :=
    (IsColimit.precomposeHomEquiv σ.symm _).symm (isColimitOfPreserves T hc)
  have hd : IsColimit d :=
    hd₀.ofIsoColimit (Cocone.ext v (by intro n; rfl))
  let c' := integralModuleLocalizationCocone ℓ E Y (T.obj B)
  obtain ⟨hc'⟩ := integralModuleLocalization_isColimit ℓ E Y (T.obj B)
  have := module_nsmul_isIso ℓ E Y D'
  have : IsIso (ℓ • 𝟙 d.pt) := mappedScalar_isIso ℓ UY D'
  have hz : c'.ι.app 0 ≫ UY.map q' = d.ι.app 0 := by
    have hz₀ : d₀.ι.app 0 = T.map (adjX.unit.app B) := by
      simp only [d₀, σ, Mod.smulSequenceCompIso, NatIso.ofComponents_inv_app, Iso.refl_inv,
        Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app, c,
        integralModuleLocalizationCocone, scalarLocalizationUnitCocone, pow_zero,
        End.one_asHom, CategoryTheory.Functor.map_id]
      exact Category.id_comp _
    change c'.ι.app 0 ≫ UY.map q' = d₀.ι.app 0 ≫ v.hom
    rw [hz₀]
    change adjY.unit.app (T.obj B) ≫ UY.map q' =
      T.map (adjX.unit.app B) ≫ T.map (UX.map q) ≫ k.hom
    rw [hq', ← Category.assoc, ← T.map_comp, hq]
  let z : c' ⟶ d :=
    ⟨UY.map q', integralLocalization_coconeLegs ℓ c' d (UY.map q') hz⟩
  have : IsIso z := IsColimit.hom_isIso hc' hd z
  have : IsIso (UY.map q') := (Cocone.forget _).map_isIso z
  have : IsIso ((Mod.forget _).map q') := by
    change IsIso ((Mod.forget _).map (UY.map q'))
    infer_instance
  exact isIso_of_reflects_iso q' (Mod.forget _)

private noncomputable def integralFreeExtensionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (Y : Scheme.{u}) (n : ℕ) :
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj
      (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) Y) n) ≅
        Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj E) Y) n :=
  (Mod.extendScalars _).mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso _)

private theorem map_conjugate_naturality
    {C₀ C₁ C₂ C₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    (GX : C₀ ⥤ C₁) (T : C₁ ⥤ C₃) (H : C₀ ⥤ C₂) (G : C₂ ⥤ C₃)
    (k : GX ⋙ T ≅ H ⋙ G) {P D : C₀} (η : P ⟶ D)
    {A B : C₂} (e : H.obj P ≅ A) (d : H.obj D ≅ B) :
    (k.app P ≪≫ G.mapIso e).hom ≫ G.map (e.inv ≫ H.map η ≫ d.hom) =
      T.map (GX.map η) ≫ (k.app D ≪≫ G.mapIso d).hom := by
  change (k.hom.app P ≫ G.map e.hom) ≫ G.map _ =
    T.map (GX.map η) ≫ (k.hom.app D ≫ G.map d.hom)
  have hi : e.hom ≫ (e.inv ≫ H.map η ≫ d.hom) = H.map η ≫ d.hom := by
    simp only [Iso.hom_inv_id_assoc]
  rw [Category.assoc, ← G.map_comp, hi, G.map_comp, ← Category.assoc]
  have hk := k.hom.naturality η
  change T.map (GX.map η) ≫ k.hom.app D = k.hom.app P ≫ G.map (H.map η) at hk
  exact (congrArg (fun z ↦ z ≫ G.map d.hom) hk.symm).trans (Category.assoc _ _ _)

private theorem adjoint_coordinate_equation
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    {B B' : C} {V : D} (q : F.obj B ⟶ V) [IsIso q] (b : B ≅ B')
    {Z : C} (c : B ⟶ Z) (g : Z ⟶ G.obj V)
    (hq : adj.unit.app B ≫ G.map q = c ≫ g) :
    b.hom ≫ adj.unit.app B' =
      c ≫ (g ≫ G.map ((asIso q).symm ≪≫ F.mapIso b).hom) := by
  rw [← Category.assoc, ← hq, Category.assoc, ← G.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_inv, IsIso.hom_inv_id_assoc]
  exact adj.unit.naturality b.hom

/-- The counit formula identifies the adjoint with the given invertible map.
Source: `Adjunction.homEquiv_counit`. Rewrite by the counit formula and the supplied equality. -/
private theorem adjoint_isIso_of_rationalization
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    {B : C} {V : D} (g : B ⟶ G.obj V)
    (q : F.obj B ⟶ V) [IsIso q]
    (h : F.map g ≫ adj.counit.app V = q) :
    IsIso ((adj.homEquiv B V).symm g) := by
  rw [Adjunction.homEquiv_counit, h]
  infer_instance

/-- Local trivializations of the two canonical maps attached to a finite etale cover.
Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph; agent finite-sheet variant.
(auxiliary; not a blueprint node)

Proof. First prove that a finite etale surjective pushforward preserves local finite
freeness, and that the cokernel of its rational adjunction unit is locally finite
free. Over an etale splitting cover the canonical product comparison identifies
this unit with a diagonal. Subtracting one coordinate identifies its cokernel
with the sum over the other sheets. Finite common refinements of the supplied
free covers give free bases of each product and quotient.

The rational unit is mono: inverse image along a surjective weakly etale map is
faithful, as restriction along a cover-dense localization functor, and its
adjunction unit is therefore mono. Refine the local free covers of P, p_*M and
the unit's cokernel together, then by affine opens, obtaining compact members.
Use the supplied rational basis, the integral basis, and the quotient basis.

The adjoint of the pushed lattice embedding is an isomorphism by the integral
scalar/pushforward comparison and e. After normalized inverse image its adjoint
remains invertible: express scalar localization as the colimit of repeated
multiplication by the prime, preserve that colimit under inverse image, and use
the zeroth-leg equation and uniqueness of all remaining legs. This gives eD.
The rational basis gives eA and the integral basis gives eB. Conjugate the pulled
rational unit by these bases to define i; exactness of inverse image and the
quotient basis give its finite free cokernel. The two required map equations
follow from naturality of the coefficient comparison and the extension unit.
Raw inverse-image coefficient rings are normalized along condensedPullbackHom.
No equality between sheet ranks, dimension hypothesis on E, or noetherian
hypothesis on X is used. -/
theorem continuousLatticeIntersection_splitData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      CompactSpace (C.X s) ∧
      let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
      let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
      let F := Mod.extendScalars
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let adj := Mod.extendRestrictAdjunction
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      ∃ (r n m : ℕ) (i : F.obj (Mod.finiteFree R r) ⟶ F.obj (Mod.finiteFree R n)),
        Mono i ∧ Nonempty (cokernel i ≅ F.obj (Mod.finiteFree R m)) ∧
        ∃ (eA : T.obj ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj P) ≅
              G.obj (F.obj (Mod.finiteFree R r)))
          (eB : T.obj ((lowerStar (integralCoeff ℓ E) p).obj M) ≅ Mod.finiteFree R n)
          (eD : T.obj ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
              ((lowerStar (Profinite.continuousMapRingObj E) p).obj
                ((upperStar (Profinite.continuousMapRingObj E) p).obj P))) ≅
              G.obj (F.obj (Mod.finiteFree R n))),
          eA.hom ≫ G.map i =
            T.map (latticeIntersectionUnit (integralScalarMap ℓ E) X P p) ≫ eD.hom ∧
          eB.hom ≫ adj.unit.app (Mod.finiteFree R n) =
            T.map (latticePushedEmbedding (integralScalarMap ℓ E) X P p M e) ≫ eD.hom := by
  classical
  obtain ⟨C, hC⟩ := commonCompactCover
    (fun g ↦ Mod.IsFree _ (((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj P))
    (fun g ↦ Mod.IsFree _ (((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj
      ((lowerStar (integralCoeff ℓ E) p).obj M)))
    (fun g ↦ Mod.IsFree _ (((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj
      (cokernel ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p).unit.app P))))
    (fun f g ↦ isFree_upperStar_comp f g) (fun f g ↦ isFree_upperStar_comp f g)
    (fun f g ↦ isFree_upperStar_comp f g)
    hP ((finiteEtale_locallyFree_models (integralCoeff ℓ E) p).1 M hM)
    ((finiteEtale_locallyFree_models (Profinite.continuousMapRingObj E) p).2 P hP)
  have : Mono ((upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj E) p).unit.app P) :=
    weaklyEtaleUnit_mono (Profinite.continuousMapRingObj E) p P
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨hc, hPs, hBs, hQs⟩ := hC s
  let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
  let F := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (C.X s))
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
    (coefficientMap (integralScalarMap ℓ E) (C.X s))
  let GX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralScalarMap ℓ E) X)
  let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
      (condensedRingObj (integralCoeff ℓ E) X) ⋙
    Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
  let H := upperStar (Profinite.continuousMapRingObj E) (C.f s)
  let k : GX ⋙ T ≅ H ⋙ G :=
    Functor.isoWhiskerLeft GX (normalizedPullbackIso (integralCoeff ℓ E) (C.f s)).symm ≪≫
      (comapUpperStarIso (integralScalarMap ℓ E) (C.f s)).symm
  obtain ⟨r, ⟨bP⟩⟩ := (isFree_mapMod_iff (Profinite.continuousMapRingObj E) (C.f s) P).1 hPs
  obtain ⟨n, ⟨bB⟩⟩ := free_comap
    (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s))) hBs
  obtain ⟨m, ⟨bQ⟩⟩ := (isFree_mapMod_iff (Profinite.continuousMapRingObj E) (C.f s)
    (cokernel ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p).unit.app P))).1
    hQs
  let eP := bP ≪≫ (integralFreeExtensionIso ℓ E (C.X s) r).symm
  let eQ := (PreservesCokernel.iso H
      ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p).unit.app P)).symm ≪≫
    bQ ≪≫ (integralFreeExtensionIso ℓ E (C.X s) m).symm
  let g := latticePushedEmbedding (integralScalarMap ℓ E) X P p M e
  have : IsIso ((pushHom (integralScalarMap ℓ E) p).app M) :=
    integralScalarUnderivedPushHom_isIso ℓ E p M
  have : IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap ℓ E) X)).homEquiv
      ((lowerStar (integralCoeff ℓ E) p).obj M)
      ((lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P))).symm g) := by
    exact adjoint_isIso_of_rationalization _ _ _ g
      ((pushHom (integralScalarMap ℓ E) p).app M ≫
        (lowerStar (Profinite.continuousMapRingObj E) p).map e.hom)
      (latticePushedEmbedding_rationalization (integralScalarMap ℓ E) X P p M e)
  have : PreservesColimitsOfShape ℕ T :=
    preservesColimitsOfShape_of_natIso (normalizedPullbackIso (integralCoeff ℓ E) (C.f s))
  let adj := Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap ℓ E) (C.X s))
  let q : F.obj (T.obj ((lowerStar (integralCoeff ℓ E) p).obj M)) ⟶
      H.obj ((lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P)) :=
    (adj.homEquiv (T.obj ((lowerStar (integralCoeff ℓ E) p).obj M))
      (H.obj ((lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P)))).symm
      (T.map g ≫ k.hom.app ((lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P)))
  have : IsIso q := localizedAdjoint_isIso ℓ E X (C.X s) T
    ((lowerStar (integralCoeff ℓ E) p).obj M)
    ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))
    (H.obj ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P)))
    (k.app ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))) g
  let d : H.obj ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P)) ≅
      F.obj (Mod.finiteFree R n) := (asIso q).symm ≪≫ F.mapIso bB
  let i : F.obj (Mod.finiteFree R r) ⟶ F.obj (Mod.finiteFree R n) :=
    eP.inv ≫ H.map
      ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p).unit.app P) ≫ d.hom
  have : Mono (H.map ((upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj E) p).unit.app P)) := inferInstance
  have : Mono i := by dsimp [i]; infer_instance
  let eA := k.app P ≪≫ G.mapIso eP
  let eD := k.app ((lowerStar (Profinite.continuousMapRingObj E) p).obj
    ((upperStar (Profinite.continuousMapRingObj E) p).obj P)) ≪≫ G.mapIso d
  refine ⟨hc, r, n, m, i, inferInstance, ?_, eA, bB, eD, ?_, ?_⟩
  · exact ⟨cokernelEpiComp eP.inv _ ≪≫ cokernelCompIsIso
      (H.map ((upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj E) p).unit.app P)) d.hom ≪≫ eQ⟩
  · exact map_conjugate_naturality GX T H G k
      ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p).unit.app P) eP d
  · have hq : adj.unit.app (T.obj ((lowerStar (integralCoeff ℓ E) p).obj M)) ≫ G.map q =
        T.map g ≫ k.hom.app ((lowerStar (Profinite.continuousMapRingObj E) p).obj
          ((upperStar (Profinite.continuousMapRingObj E) p).obj P)) :=
      (adj.homEquiv (T.obj ((lowerStar (integralCoeff ℓ E) p).obj M))
        (H.obj ((lowerStar (Profinite.continuousMapRingObj E) p).obj
          ((upperStar (Profinite.continuousMapRingObj E) p).obj P)))).apply_symm_apply _
    exact adjoint_coordinate_equation F G adj q bB (T.map g)
      (k.hom.app ((lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P))) hq

end AlgebraicGeometry.ProEtale.CondensedRing
