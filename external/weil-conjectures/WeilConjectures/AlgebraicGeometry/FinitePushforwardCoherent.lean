/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Coherence of finite direct images

Source: Stacks Project, Cohomology of Schemes, Tags 01Y6 and 01XZ
(blueprint: lem-weil-pbc-finite-pushforward-coherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction preserves finite type: pull the local generating cover back along
`Over.forget U`; its local maps preserve colimits and the unit, hence carry each finite
family of generators to a finite family. Source: Stacks Project, Modules, Tag 01B5,
the locality of finite type used in the finite-pushforward argument
(blueprint: lem-weil-pbc-finite-pushforward-coherent). -/
private theorem isFiniteType_over (X : Scheme.{u}) (F : X.Modules)
    [F.IsFiniteType] (U : X.Opens) : (F.over U).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let G := Over.forget U
  let J := Opens.grothendieckTopology X
  let K := J.over U
  let S := X.ringCatSheaf.over U
  let φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj X.ringCatSheaf := 𝟙 _
  let d : (F.over U).LocalGeneratorsData :=
    { I := Σ (V : Over U) (i : q.I), G.obj V ⟶ q.X i
      X := fun i ↦ i.1
      coversTop := fun V ↦ by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj V)))
        intro W g ⟨i, ⟨v⟩⟩
        exact ⟨⟨W, i, v⟩, ⟨𝟙 _⟩⟩
      generators := fun i ↦ by
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        have : G'.IsContinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          Functor.isContinuous_comp _ _ _ (J.over _) _
        have : G'.IsCocontinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          isCocontinuous_comp _ _ _ (J.over _)
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (q.X i.2.1))).obj (X.ringCatSheaf.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          SheafOfModules.isLeftAdjoint_pushforward_of_isIso.{u} ψ
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) (Iso.refl _) }
  apply SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf.over U)
  refine ⟨d, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.1
  dsimp only [d]
  infer_instance

/-- A finite direct image of a coherent module is coherent, with finite sections on every
 affine open. Source: Stacks Project, Tags 01Y6 and 01XZ
(blueprint: lem-weil-pbc-finite-pushforward-coherent).

Proof:
1. A finite morphism is locally of finite type. Mathlib's
   `LocallyOfFiniteType.isLocallyNoetherian` makes Y locally Noetherian.
2. Apply `isCoherent_iff_isQuasicoherent_and_isFiniteType` on Y to get
   quasi-coherence and finite type of F. Restrict its finite local generators to
   each inverse-image affine open using the proved helper `isFiniteType_over`.
3. The affine finite-type criterion gives finite sections over the coordinate ring
   of each inverse image. `f.finite_app` makes that ring finite over the base ring.
   The direct-image sections are definitionally the same abelian group; their scalar
   action is restriction of scalars. `Module.Finite.trans` gives finite base modules.
4. The proved source-library theorem `isQuasicoherent_pushforward_of_isAffineHom`
   gives quasi-coherence of the direct image, without using a base-change theorem.
5. Apply the affine finite-type criterion on the covering of all affine opens of X,
   then the coherence criterion on X. Pair this with the definitional sections equality
   and the finite-section calculation. -/
theorem isCoherent_pushforward_of_isFinite {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward f).obj F) ∧
      ∀ (U : X.Opens), IsAffineOpen U →
        Γ((pushforward f).obj F, U) = Γ(F, f ⁻¹ᵁ U) ∧
          Module.Finite Γ(X, U) Γ((pushforward f).obj F, U) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType Y F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  have hp : ((pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f F
  have hs (U : X.Opens) (hU : IsAffineOpen U) :
      Module.Finite Γ(X, U) Γ((pushforward f).obj F, U) := by
    have hV := hU.preimage f
    have : (F.over (f ⁻¹ᵁ U)).IsFiniteType := isFiniteType_over Y F _
    have hM : Module.Finite Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U) :=
      (((quasicoherent_finite_type_affine.{u, u} Y).2 F hq).1 _ hV).1.mp inferInstance
    let := (f.app U).hom.toAlgebra
    let : Module Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) :=
      inferInstanceAs (Module Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U))
    have : Module.Finite Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) := hM
    have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
    exact Module.Finite.trans Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U)
  have hft : ((pushforward f).obj F).IsFiniteType :=
    ((((quasicoherent_finite_type_affine.{u, u} X).2 _ hp).2.1)
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X)
      (fun U ↦ U.2) (fun U ↦ hs U.1 U.2)).1
  exact ⟨(isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr ⟨hp, hft⟩,
    fun U hU ↦ ⟨rfl, hs U hU⟩⟩

/-- The structure sheaf in the finite-direct-image statement satisfies its coherence
hypothesis. Source: Stacks Project, Tags 01Y6, 01XZ and 01T6
(blueprint: lem-weil-pbc-finite-pushforward-coherent).

Proof (the structure-sheaf step of the node): Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian` makes Y locally Noetherian. The structure
sheaf is invertible and hence finite locally free; the proved source-library instances
make it finitely presented, quasi-coherent and finite type. Apply the coherence
criterion on Y. -/
theorem isCoherent_unit_of_finite_to_locallyNoetherian {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] :
    RingedSpace.IsCoherent Y.toRingedSpace (SheafOfModules.unit Y.ringCatSheaf) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation := by
    have : (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u}
      (SheafOfModules.unit Y.ringCatSheaf)
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
    ⟨SheafOfModules.isQuasicoherent_unit.{u, u, u},
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} _⟩

end AlgebraicGeometry.Scheme.Modules
