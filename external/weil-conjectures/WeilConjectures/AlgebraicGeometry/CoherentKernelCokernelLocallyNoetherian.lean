/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Coherent kernels, cokernels, sums and quasi-coherent submodules

Source: Stacks Project, Cohomology of Schemes, Tags 01Y0 and 01Y1
(blueprint: lem-weil-pbc-coherent-kernel-cokernel-locnoeth).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction to a slice site preserves finite type for an arbitrary sheaf of rings.
Pull the local generating cover back along
`Over.forget U`; its local maps preserve colimits and the unit, hence carry each finite
family of generators to a finite family. Source: Stacks Project, Modules, Tag 01B5,
the locality of finite type used in the affine submodule argument. This generalizes
the scheme-only helper to sites with binary products and pullbacks; only weak sheafification
is assumed on the first-level slices, and sheafification on the iterated slices.
(blueprint: lem-weil-pbc-coherent-kernel-cokernel-locnoeth). -/
private theorem isFiniteType_over.{u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (V : C) (W : Over V), HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ (V : C) (W : Over V),
      ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) [F.IsFiniteType] (U : C) :
    (F.over U).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let G := Over.forget U
  let K := J.over U
  let S := R.over U
  let φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R := 𝟙 _
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
              (J.over (q.X i.2.1))).obj (R.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) (Iso.refl _) }
  apply SheafOfModules.IsFiniteType.mk (R := R.over U)
  refine ⟨d, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.1
  dsimp only [d]
  infer_instance

/-- On a locally Noetherian scheme, kernels and cokernels of maps between coherent modules,
binary direct sums of coherent modules, and quasi-coherent submodules of coherent modules
and their quotients are coherent. A submodule inclusion is represented by a monomorphism.
Source: Stacks Project, Cohomology of Schemes, Tags 01Y0 and 01Y1
(blueprint: lem-weil-pbc-coherent-kernel-cokernel-locnoeth).

Proof:
1. Apply `lem-weil-pbc-coherent-modules-kernel-cokernel-sum` to the underlying ringed
   space for kernels and cokernels. Its extension clause applied to the canonical
   split short exact sequence `F → F ⊞ G → G` proves binary sum closure (01Y0).
2. For the submodule clause, coherence of `F` gives quasi-coherence and finite type by
   `pqf-lem-coherent-ft-locnoeth`. Restrict its finite local generators to any affine
   open `U` using the private restriction lemma. The affine criterion
   `lem-weil-pbc-quasi-coherent-finite-type-affine` makes `Γ(F, U)` finite.
3. The ring `Γ(X, U)` is Noetherian by local Noetherianity. Evaluation preserves
   monomorphisms, so the section map of `i` is injective. Mathlib's
   `isNoetherian_of_isNoetherianRing_of_finite` and `Module.Finite.of_injective` make
   `Γ(F', U)` finite. This is the finite-submodule argument of 01Y1.
4. Apply the affine-cover clause of the same finite-type criterion to `F'` on the
   cover by all affine opens. Its assumed quasi-coherence and the resulting finite
   type give coherence by `pqf-lem-coherent-ft-locnoeth`. The general cokernel closure
   from step 1 now proves coherence of the quotient.
-/
theorem isCoherent_kernel_cokernel_biprod_and_submodule
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (∀ (F G : X.Modules),
      RingedSpace.IsCoherent X.toRingedSpace F →
      RingedSpace.IsCoherent X.toRingedSpace G →
      (∀ (φ : F ⟶ G),
        RingedSpace.IsCoherent X.toRingedSpace (kernel φ) ∧
        RingedSpace.IsCoherent X.toRingedSpace (cokernel φ)) ∧
      RingedSpace.IsCoherent X.toRingedSpace (F ⊞ G)) ∧
    (∀ (F F' : X.Modules) (i : F' ⟶ F),
      RingedSpace.IsCoherent X.toRingedSpace F →
      Mono i → SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F' →
      RingedSpace.IsCoherent X.toRingedSpace F' ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel i)) := by
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  constructor
  · intro F G hF hG
    refine ⟨fun φ ↦ hclosure.1 F G φ hF hG, ?_⟩
    exact (hclosure.2.1 _ (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact).2.1 hF hG
  · intro F F' i hF hi hq
    have hqc := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
    have : F.IsQuasicoherent := hqc.1
    have : F.IsFiniteType := hqc.2
    have hfinite (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(F', U.1) := by
      have := IsLocallyNoetherian.component_noetherian U
      have : (F.over U.1).IsFiniteType :=
        isFiniteType_over (_root_.Opens.grothendieckTopology X) X.ringCatSheaf F U.1
      have : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
        ((quasicoherent_finite_type_affine.{u, u} X).2 F hqc.1).1 U.1 U.2 |>.1.mp inferInstance
      have : _root_.IsNoetherian Γ(X, U.1) Γ(F, U.1) :=
        isNoetherian_of_isNoetherianRing_of_finite _ _
      let L : Γ(F', U.1) →ₗ[Γ(X, U.1)] Γ(F, U.1) := (i.val.app (.op U.1)).hom
      have hm : Mono (i.val.app (.op U.1)) :=
        (SheafOfModules.evaluation X.ringCatSheaf (.op U.1)).map_mono i
      exact Module.Finite.of_injective L ((ModuleCat.mono_iff_injective _).mp hm)
    have ht : F'.IsFiniteType :=
      (((quasicoherent_finite_type_affine.{u, u} X).2 F' hq).2.1 X.affineOpens
        (fun U ↦ U.1) (iSup_affineOpens_eq_top X) (fun U ↦ U.2) hfinite).1
    have hc := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F').mpr ⟨hq, ht⟩
    exact ⟨hc, (hclosure.1 F' F i hc hF).2⟩

end AlgebraicGeometry.Scheme.Modules
