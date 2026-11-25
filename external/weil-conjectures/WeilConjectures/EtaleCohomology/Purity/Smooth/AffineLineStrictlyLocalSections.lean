/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-!
# Degree-zero cohomology of the affine line over a strictly henselian local ring

Let `φ : A ⟶ B` be a local homomorphism of strictly henselian local rings and `M` a locally
constant sheaf of `Λ`-modules on `Spec A`. We show that the pullback map
`H⁰(𝔸¹_A, p_A^* M) ⟶ H⁰(𝔸¹_B, p_A^* M|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective.

* A locally constant sheaf on the small étale site of a strictly henselian local scheme is
  constant: a trivialising étale cover has a member through the closed point, which has a
  section (`AlgebraicGeometry.Scheme.isConstant_of_isStrictlyHenselianLocalRing`).
* The constant sheaf functor to abelian sheaves on a connected scheme is fully faithful, the
  global sections of the constant sheaf `N` being `N`
  (`AlgebraicGeometry.Scheme.bijective_constantSheaf_map_of_connectedSpace`).
* Hence for a morphism `f : X ⟶ Y` of connected schemes the pullback map on `H⁰` of a constant
  abelian sheaf is bijective (`AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_constantSheaf`).
* The affine line over a connected scheme is connected.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Scheme

section Constant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- A locally constant sheaf on the small étale site of the spectrum of a strictly henselian
local ring is constant: a member of a trivialising cover whose image contains the closed point
has a section `σ`, and the sheaf is the pullback along `σ` of its constant restriction. -/
theorem isConstant_of_isStrictlyHenselianLocalRing {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] (F : Sheaf (Spec (.of R)).smallEtaleTopology A)
    [IsLocallyConstantSheaf F] : F.IsConstant (Spec (.of R)).smallEtaleTopology := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint R)
  have : AlgebraicGeometry.Etale (𝒰.f j) := 𝒰.map_prop j
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing (𝒰.f j) y hy
  have : ((Etale.upperStar A (𝒰.f j)).obj F).IsConstant (𝒰.X j).smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have : ((Etale.upperStar A (𝒰.f j) ⋙ Etale.upperStar A σ).obj F).IsConstant
      (Spec (.of R)).smallEtaleTopology :=
    Sheaf.IsConstant.upperStar A σ ((Etale.upperStar A (𝒰.f j)).obj F)
  exact Sheaf.isConstant_congr _
    (((Etale.upperStarComp A σ (𝒰.f j) (𝟙 _) hσ.symm).app F).symm ≪≫
      (Etale.upperStarId A _).app F)

end Constant

variable (X : Scheme.{u}) [ConnectedSpace X]

/-- The unit `N ⟶ Γ(X, N_X)` of the constant sheaf adjunction on the small étale site of a
connected scheme is bijective. -/
lemma bijective_constantSheafAdj_unit_app_addCommGrp (N : AddCommGrpCat.{u + 1}) :
    Function.Bijective ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).unit.app N) := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    sheafificationAdjunction_unit_app]
  exact bijective_toSheafify_app_terminal X N

/-- The constant sheaf functor to abelian sheaves on the small étale site of a connected scheme
is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).FullyFaithful :=
  have : IsIso (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).unit :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun N ↦ (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_constantSheafAdj_unit_app_addCommGrp X N))
  (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).fullyFaithfulLOfIsIsoUnit

end Scheme

namespace Etale

/-- For a morphism `f : X ⟶ Y` of connected schemes, the pullback map
`H⁰(Y, N_Y) ⟶ H⁰(X, f^* N_Y)` on the cohomology of a constant abelian sheaf is bijective: both
sides are `Hom(ℤ, N)`. -/
theorem bijective_cohomologyMap_zero_constantSheaf {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (N : AddCommGrpCat.{u + 1}) :
    Function.Bijective (cohomologyMap f
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N) 0) := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let cX := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let cY := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let e := upperStarConstantSheafIso AddCommGrpCat.{u + 1} f
  let ΦY : (Z ⟶ N) → Sheaf.H (cY.obj N) 0 := fun ψ ↦ Abelian.Ext.mk₀ (cY.map ψ)
  let ΦX : (Z ⟶ N) → Sheaf.H ((f)^*[AddCommGrpCat.{u + 1}].obj (cY.obj N)) 0 :=
    fun ψ ↦ Abelian.Ext.mk₀ (cX.map ψ ≫ e.inv.app N)
  have hΦY : Function.Bijective ΦY :=
    (Abelian.Ext.homEquiv₀.symm.bijective).comp ((fullyFaithfulConstantSheaf Y).map_bijective Z N)
  have hΦX : Function.Bijective ΦX :=
    (Abelian.Ext.homEquiv₀.symm.bijective).comp
      (((Iso.refl _).homCongr (e.app N).symm).bijective.comp
        ((fullyFaithfulConstantSheaf X).map_bijective Z N))
  have h : cohomologyMap f (cY.obj N) 0 ∘ ΦY = ΦX := by
    funext ψ
    simp only [Function.comp_apply, ΦY, ΦX, cohomologyMap_apply,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    exact (e.inv.naturality ψ).symm
  rw [← h] at hΦX
  refine ⟨fun a b hab ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hΦY.2 a
    obtain ⟨b, rfl⟩ := hΦY.2 b
    exact congrArg ΦY (hΦX.1 hab)
  · obtain ⟨a, rfl⟩ := hΦX.2 c
    exact ⟨_, rfl⟩

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

/-- The spectrum of a local ring is connected: every point specialises to the closed point. -/
lemma connectedSpace_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (Spec (.of R)) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨IsLocalRing.closedPoint R⟩, fun s hs ↦ ?_⟩
  by_cases h : IsLocalRing.closedPoint R ∈ s
  · exact Or.inr (Set.eq_univ_of_forall fun x ↦
      (IsLocalRing.specializes_closedPoint x).mem_open hs.isOpen h)
  · exact Or.inl (Set.eq_empty_of_forall_notMem fun x hx ↦
      h ((IsLocalRing.specializes_closedPoint x).mem_closed hs.isClosed hx))

/-- The affine line over a connected scheme is connected: its projection is geometrically
irreducible and open. -/
lemma connectedSpace_affineLine_of_connectedSpace (S : Scheme.{u}) [ConnectedSpace S] :
    ConnectedSpace 𝔸(ULift.{u} (Fin 1); S) :=
  have : GeometricallyConnected (𝔸(ULift.{u} (Fin 1); S) ↘ S) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  have : Smooth (𝔸(ULift.{u} (Fin 1); S) ↘ S) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin 1))) _
  GeometricallyConnected.connectedSpace (𝔸(ULift.{u} (Fin 1); S) ↘ S)
    (𝔸(ULift.{u} (Fin 1); S) ↘ S).isOpenMap

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Degree zero of the acyclicity of the affine line over strictly henselian local rings.**
For a homomorphism `φ : A ⟶ B` from a strictly henselian local ring to a local ring and a
locally constant sheaf `M` of `Λ`-modules on `Spec A`, the pullback map
`H⁰(𝔸¹_A, p_A^* M) ⟶ H⁰(𝔸¹_B, p_A^* M|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective: `M` is constant
(`AlgebraicGeometry.Scheme.isConstant_of_isStrictlyHenselianLocalRing`), so is `p_A^* M`, and
both affine lines are connected. -/
theorem bijective_cohomologyMap_zero_affineLine_of_strictlyHenselian
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) 0) := by
  have : IsStrictlyHenselianLocalRing A := { isSepClosed_residueField := inferInstance }
  have := connectedSpace_spec_of_isLocalRing A
  have := connectedSpace_spec_of_isLocalRing B
  have := connectedSpace_affineLine_of_connectedSpace (Spec (.of A))
  have := connectedSpace_affineLine_of_connectedSpace (Spec (.of B))
  obtain ⟨N, ⟨e⟩⟩ := (isConstant_of_isStrictlyHenselianLocalRing M).mem_essImage
  let p := 𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A)
  refine bijective_cohomologyMap_of_iso _
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      ((p)^*[ModuleCat.{u + 1} Λ].mapIso e.symm ≪≫
        (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) p).app N) ≪≫
      (constantSheafSheafComposeForget₂Iso Λ).app N).symm 0 ?_
  exact bijective_cohomologyMap_zero_constantSheaf _ _

end Etale

end AlgebraicGeometry
