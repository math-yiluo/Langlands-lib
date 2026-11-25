/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalHigher
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalSections
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.ConstantCoefficients

/-!
# Acyclicity of the affine line over a field

For a field `k` and a finite coefficient ring `Λ` whose exponent is invertible in `k`, the unit
`K ⟶ Rπ_* π^* K` of the projection `π : 𝔸¹_k ⟶ Spec k` is an isomorphism for every bounded below
complex `K` of étale sheaves of `Λ`-modules on `Spec k`
(`AlgebraicGeometry.Etale.affineLineAcyclicAt_of_field`).

## The argument

* By base change along the field extension `k ⊆ k̄` to an algebraic closure
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_affineLine_of_fieldExtension`, from
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`) and the surjectivity of
  `Spec k̄ ⟶ Spec k`, it suffices to treat `k` algebraically closed
  (`AlgebraicGeometry.Etale.AffineLineAcyclicAt.of_surjective`).
* Over an algebraically closed field `Ω` every sheaf is constant, and it suffices to treat a
  constant sheaf `M` placed in degree `0`
  (`AlgebraicGeometry.Etale.affineLineAcyclicAt_iff_singleFunctor`).
* In degree `0`, the unit induces on sections over `Spec Ω` the pullback
  `Hom(Λ, M) ⟶ Hom(Λ, M_{𝔸¹})`, which is bijective since `𝔸¹_Ω` is connected.
* In degrees `q > 0`, the sheaf `Rᵠπ_* M` on `Spec Ω` is zero as soon as its global sections
  `Hᵠ(𝔸¹_Ω, M)` are; the latter vanish for `M` finite by the Kummer computation
  `AlgebraicGeometry.AffineSpace.subsingleton_sheafH_constantSheaf_line`, and in general since
  `M` is the filtered colimit of its finite submodules and `Rᵠπ_*` commutes with filtered
  colimits (`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

/-- An additive functor out of modules vanishes at a module `V` if it vanishes at all finitely
generated submodules of `V` and preserves the colimit of the system they form. -/
theorem CategoryTheory.Functor.isZero_obj_of_forall_fg {R : Type*} [Ring R] {D : Type*}
    [Category* D] [Preadditive D] (Φ : ModuleCat.{u} R ⥤ D) (V : ModuleCat.{u} R)
    [PreservesColimitsOfShape {N : Submodule R V // N.FG} Φ]
    (h : ∀ N : {N : Submodule R V // N.FG}, IsZero (Φ.obj (ModuleCat.of R N.1))) :
    IsZero (Φ.obj V) := by
  classical
  have : Nonempty {N : Submodule R V // N.FG} := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  have hc := isColimitOfPreserves Φ
    (ModuleCat.directLimitIsColimit (fun N : {N : Submodule R V // N.FG} ↦ N.1)
      (Module.fgSystem R V))
  have hz : IsZero (Φ.obj (ModuleCat.directLimitCocone
      (fun N : {N : Submodule R V // N.FG} ↦ N.1) (Module.fgSystem R V)).pt) := by
    rw [IsZero.iff_id_eq_zero]
    exact hc.hom_ext fun N ↦ (h N).eq_of_src _ _
  exact hz.of_iso (Φ.mapIso (Module.fgSystem.equiv R V).toModuleIso.symm)

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section FieldExtension

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [HasInvertibleExponent Λ (Spec (.of k))]

/-- **Base change of the affine line along a field extension `k ⊆ L`**: the derived base change
map of the projection `π : 𝔸¹_k ⟶ Spec k` along `Spec L ⟶ Spec k` is an isomorphism at every
bounded below complex. -/
theorem isIso_baseChange_app_affineLine_of_fieldExtension
    (K : DerivedCategory.Plus (Sheaf (𝔸(ULift.{u} (Fin 1); Spec (.of k))).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    IsIso ((baseChange (ModuleCat.{u + 1} Λ) (AffineSpace.isPullback_map
      (n := ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom (algebraMap k L)))).toCommSq).app
        K) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of k))
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) ι
  refine DerivedCategory.Plus.isIso_app_of_forall_homology _ ⊤ (fun F _ ↦ ?_)
    (fun K n _ q hq ↦ isZero_homologyFunctor_baseChangeSource_obj Λ ι _ K n q hq)
    (fun K n _ q hq ↦ isZero_homologyFunctor_baseChangeTarget_obj Λ _ _ K n q hq) K
    (fun _ ↦ trivial)
  have : IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F :=
    IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu F
  exact (isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
    isIso_baseChangeHomologyMap_of_fieldExtension Λ (𝟙 _) _ ι (𝟙 _) (IsPullback.id_vert ι) sq q F

end FieldExtension

section StrictlyHenselian

variable (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- Over a strictly henselian local ring `R`, for `t : X ⟶ Spec R` such that the constant sheaf
functor on `X` is fully faithful, the pullback `t^*` is bijective on morphisms
`Λ[Spec R] ⟶ M_{Spec R}` into a constant sheaf. -/
lemma bijective_upperStar_map_freeSheaf_constantSheaf_of_fullyFaithful {X : Scheme.{u}}
    (t : X ⟶ Spec (.of R))
    (hX : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).FullyFaithful)
    (M : ModuleCat.{u + 1} Λ) :
    Function.Bijective ((t)^*[ModuleCat.{u + 1} Λ].map :
      ((freeSheaf Λ _).obj (Scheme.etaleTerminal R) ⟶
        (constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) → _) :=
  Functor.bijective_map_of_iso_left _
    (freeSheafObjIsoOfIsTerminal Λ (Scheme.isTerminalEtaleTerminal R))
    (Functor.bijective_map_of_fullyFaithful_of_iso
      (constantSheafAdj _ _ (Scheme.isTerminalEtaleTerminal R)).fullyFaithfulLOfIsIsoUnit
      hX (F' := 𝟭 _) (Scheme.upperStarConstantSheafIso _ t ≪≫ (Functor.leftUnitor _).symm)
      Function.bijective_id)

/-- Degree zero: over a strictly henselian local ring `R`, for `t : X ⟶ Spec R` such that the
constant sheaf functor on `X` is fully faithful, the unit `M ⟶ Rt_* t^* M` at a constant sheaf
`M` induces a bijection on the sections over `Spec R` of `H⁰`. -/
lemma isIso_homologyFunctor_zero_map_unit_app_etaleTerminal_of_fullyFaithful {X : Scheme.{u}}
    (t : X ⟶ Spec (.of R))
    (hX : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).FullyFaithful)
    (M : ModuleCat.{u + 1} Λ) :
    IsIso (((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            M)))).hom.app (op (Scheme.etaleTerminal R))) := by
  let adj := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let S := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((freeSheaf Λ _).obj (Scheme.etaleTerminal R))
  have h₂ : Function.Bijective (D+((t)^*[ModuleCat.{u + 1} Λ]).map :
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((freeSheaf Λ _).obj (Scheme.etaleTerminal R)) ⟶ K) → _) :=
    Functor.bijective_map_of_fullyFaithful_of_iso (Functor.FullyFaithful.ofFullyFaithful _)
      (Functor.FullyFaithful.ofFullyFaithful _)
      ((t)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0)
      (bijective_upperStar_map_freeSheaf_constantSheaf_of_fullyFaithful Λ R t hX M)
  have h₃ : (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) =
      (adj.homEquiv _ _) ∘ (D+((t)^*[ModuleCat.{u + 1} Λ]).map :
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((freeSheaf Λ _).obj (Scheme.etaleTerminal R)) ⟶ K) → _) :=
    funext fun β ↦ by
      rw [Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality β
  have h₄ : Function.Bijective (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) := by
    rw [h₃]
    exact (adj.homEquiv _ _).bijective.comp h₂
  have key : ⇑(((DerivedCategory.Plus.homologyFunctor _ 0).map (adj.unit.app K)).hom.app
      (op (Scheme.etaleTerminal R))) ∘ derivedHomToSections (Scheme.etaleTerminal R) K =
      derivedHomToSections (Scheme.etaleTerminal R) _ ∘
        (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) :=
    funext fun β ↦ (derivedHomToSections_comp _ _ β).symm
  rw [ConcreteCategory.isIso_iff_bijective,
    ← Function.Bijective.of_comp_iff _ (bijective_derivedHomToSections R K), key]
  exact (bijective_derivedHomToSections R _).comp h₄

/-- **Global sections of higher direct images over a strictly local base.** For
`f : X ⟶ T` with `T ≅ Spec R`, `R` strictly henselian local, if `Hᵠ(X, F) = 0` then the sheaf
`Rᵠf_* F` has no nonzero global sections: by the Leray isomorphism and the exactness of the
global sections functor of `T`, `Hᵠ(X, F) = Γ(T, Rᵠf_* F)`. -/
theorem isZero_Γ_higherDirectImage_of_isZero_cohomology {X T : Scheme.{u}} (f : X ⟶ T)
    (e : T ≅ Spec (.of R)) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (hF : IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))) :
    IsZero ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (higherDirectImage Λ f q F)) := by
  have := preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (Λ := Λ) e
  let K := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
    F
  let L := ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj K
  have hL : IsZero ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.homologyFunctor _ q).obj L)) :=
    hF.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ f).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((Sheaf.Γ T.smallEtaleTopology _).rightDerivedFunctorIsoMapDerivedCategory.app L) ≪≫
    (((Sheaf.Γ T.smallEtaleTopology _).mapDerivedCategoryHomologyFunctorIso q).app L).symm).symm
  exact hL.of_iso ((Sheaf.Γ T.smallEtaleTopology _).mapIso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))

end StrictlyHenselian

section SepClosed

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Over a separably closed field `Ω`, a sheaf on `Spec Ω` whose image under the global sections
functor is zero is zero. -/
lemma isZero_of_isZero_Γ_of_isSepClosed
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsZero ((Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj G)) :
    IsZero G :=
  isZero_of_subsingleton_sections_of_isSepClosed G (ModuleCat.isZero_iff_subsingleton.1
    (h.of_iso ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).app G).symm))

/-- The constant sheaf functor on the affine line over a connected scheme is fully faithful. -/
noncomputable def fullyFaithfulConstantSheafAffineLine (S : Scheme.{u}) [ConnectedSpace S] :
    (constantSheaf 𝔸(ULift.{u} (Fin 1); S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).FullyFaithful :=
  have := connectedSpace_affineLine_of_connectedSpace S
  have : IsIso (constantSheafAdj 𝔸(ULift.{u} (Fin 1); S).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _)).unit :=
    NatIso.isIso_of_isIso_app _
  (constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _)
    ).fullyFaithfulLOfIsIsoUnit

/-- Degree zero over a separably closed field: the unit `M ⟶ Rπ_* π^* M` at a constant sheaf
is an isomorphism on `H⁰`. -/
theorem isIso_homologyFunctor_zero_map_unit_app_constantSheaf_affineLine
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  have := connectedSpace_spec_of_isLocalRing Ω
  have := isIso_homologyFunctor_zero_map_unit_app_etaleTerminal_of_fullyFaithful Λ Ω
    (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))
    (fullyFaithfulConstantSheafAffineLine Λ (Spec (.of Ω))) M
  exact isIso_of_isIso_app_etalePoint Λ _ (hφ := this)

end SepClosed

section AlgClosed

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of Ω))]

omit [Finite Λ] in
/-- Positive degrees over an algebraically closed field, for finite coefficients: for a finite
`Λ`-module `M`, `Rᵠπ_* M = 0` for `q > 0`, `π : 𝔸¹_Ω ⟶ Spec Ω`. Its global sections are
`Hᵠ(𝔸¹_Ω, M)`, which vanishes by the Kummer computation on the affine line. -/
theorem isZero_higherDirectImage_constantSheaf_affineLine_of_finite (M : ModuleCat.{u + 1} Λ)
    [Finite M] (q : ℕ) (hq : 0 < q) :
    IsZero (higherDirectImage Λ (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω)) q
      ((constantSheaf 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M)) := by
  refine isZero_of_isZero_Γ_of_isSepClosed Λ _
    (isZero_Γ_higherDirectImage_of_isZero_cohomology Λ Ω _ (Iso.refl _) _ q ?_)
  rw [isZero_cohomology_singleFunctor_iff_subsingleton_H]
  obtain ⟨n, hn, hA⟩ := exists_natCast_ne_zero_nsmul_eq_zero Λ Ω
  have : Finite ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M) :=
    inferInstanceAs (Finite M)
  have hΛ : (n : Λ) = 0 := by simpa [nsmul_eq_mul] using hA (1 : Λ)
  have h := AffineSpace.subsingleton_sheafH_constantSheaf_line
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M) hn
    (fun a ↦ show n • (show M from a) = 0 by rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]) q hq
  exact @Function.Surjective.subsingleton _ _ _ h
    (bijective_sheafHMap_hom ((constantSheafSheafComposeForget₂Iso Λ).app M).symm q).2

/-- Positive degrees over an algebraically closed field: for every `Λ`-module `M`,
`Rᵠπ_* M = 0` for `q > 0`, `π : 𝔸¹_Ω ⟶ Spec Ω`. The module `M` is the filtered colimit of its
finitely generated, hence finite, submodules, and `Rᵠπ_*` commutes with filtered colimits. -/
theorem isZero_higherDirectImage_constantSheaf_affineLine (M : ModuleCat.{u + 1} Λ) (q : ℕ)
    (hq : 0 < q) :
    IsZero (higherDirectImage Λ (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω)) q
      ((constantSheaf 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M)) := by
  have : EssentiallySmall.{u + 1} {N : Submodule Λ M // N.FG} :=
    essentiallySmallSelf.{u + 1} _
  have : Nonempty {N : Submodule Λ M // N.FG} := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  have := preservesColimitsOfShape_higherDirectImage Λ
    (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω)) q {N : Submodule Λ M // N.FG}
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (constantSheaf 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) :=
    (constantSheafAdj _ (ModuleCat.{u + 1} Λ) terminalIsTerminal).leftAdjoint_preservesColimits
  refine Functor.isZero_obj_of_forall_fg (higherDirectImageConstantFunctor Λ
    (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω)) q) M fun N ↦ ?_
  have : Module.Finite Λ N.1 := Module.Finite.iff_fg.2 N.2
  have : Finite (ModuleCat.of Λ N.1) := Module.finite_of_finite Λ
  exact isZero_higherDirectImage_constantSheaf_affineLine_of_finite Λ _ q hq

/-- **Acyclicity of the affine line over an algebraically closed field.** -/
theorem affineLineAcyclicAt_of_isAlgClosed : AffineLineAcyclicAt Λ (Spec (.of Ω)) := by
  rw [affineLineAcyclicAt_iff_singleFunctor]
  intro F
  let c := constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  refine (NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso (c.objObjPreimageIso F))).1 ?_
  rw [isIso_unit_app_singleFunctor_iff]
  refine ⟨isIso_homologyFunctor_zero_map_unit_app_constantSheaf_affineLine Λ _, fun q hq ↦ ?_⟩
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  exact (isZero_higherDirectImage_constantSheaf_affineLine Λ (c.objPreimage F) q
    (by exact_mod_cast hq)).of_iso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      (R+((𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))_*[ModuleCat.{u + 1} Λ]).mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
          ((Scheme.upperStarConstantSheafIso _ _).app _))))

end AlgClosed

/-- **Acyclicity of the affine line over a field** (SGA 4 XV 2.2 over a field): for a field `k`
and a finite coefficient ring `Λ` whose exponent is invertible in `k`, the unit
`K ⟶ Rπ_* π^* K` of `π : 𝔸¹_k ⟶ Spec k` is an isomorphism for every `K ∈ D⁺(k_ét, Λ)`. -/
theorem affineLineAcyclicAt_of_field [Finite Λ] (k : Type u) [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] : AffineLineAcyclicAt Λ (Spec (.of k)) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Surjective ι := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
  exact AffineLineAcyclicAt.of_surjective Λ ι
    (fun K ↦ isIso_baseChange_app_affineLine_of_fieldExtension Λ _)
    (affineLineAcyclicAt_of_isAlgClosed Λ)

end Etale

end AlgebraicGeometry
