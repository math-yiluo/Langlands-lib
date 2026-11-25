/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Finite global generators on an affine scheme

Source: Stacks Project, Properties, Tag 01PB, and Schemes, Tags 01IA and 01HV
(blueprint: lem-weil-pbc-affine-finite-type-generating-sections).
-/

@[expose] public section

universe u

open CategoryTheory

open SheafOfModules in
private theorem finiteType_of_data
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits SheafOfModules in
private theorem finiteType_pushforward
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type*} [Category D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  let Q : ((pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
          pushforward (𝟙 _)
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        let e : (pushforward.{u} (F := G') ψ).obj (unit (R.over (P.X i.2.1))) ≅
            unit (S.over i.1) := overS.mapIso η
        letI : PreservesColimitsOfSize.{u, u} (pushforward.{u} (F := G') ψ) := h _ _ _
        exact (P.generators i.2.1).map (pushforward.{u} (F := G') ψ) e.symm }
  have : Q.IsFiniteType := ⟨fun i ↦ by
    have := hP.isFiniteType i.2.1
    dsimp [Q]
    infer_instance⟩
  exact finiteType_of_data Q

open CategoryTheory.Limits SheafOfModules in
private theorem finiteType_pushforward_leftAdjoint
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type*} [Category D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  apply +allowSynthFailures finiteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance


namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasi-coherent module on an affine scheme has finitely generated global
sections and a finite family of global generators. Every finite family spanning its module
of global sections generates the sheaf. A section in `G.sections` is a compatible family
on opens, determined by its value at `⊤`; `freeHomEquiv.symm` is the map sending the free
basis to the specified sections. Its being epi means surjectivity as a map of sheaves.

Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01IA and 01HV
(blueprint: lem-weil-pbc-affine-finite-type-generating-sections).

Proof:
1. Transport along an affine isomorphism to `Spec R`, with `R = Γ(U, ⊤)`
   (`def-pc-scheme`). By `lem-weil-pbc-quasi-coherent-finite-type-affine` (a), finite type
   (`pqf-def-coherent`) implies that `M = Γ(G, ⊤)` is a finite R-module. Choose a finite
   generating family; existence of sheaf generators follows from the assertion for any
   such family proved below (`def-weil-pbc-generating-sections`).
2. By `lem-weil-pbc-spec-module-tilde-sections` and the counit isomorphism of
   `lem-weil-pbc-affine-tilde-gamma-adjunction` (3), `G ≅ M~`, compatibly with global
   sections and their germs.
3. At a prime p, the local ring is the localization of R
   (`lem-weil-pbc-spec-domain-stalks-function-field` (1)), and the stalk is the localization
   of M (`lem-weil-pbc-spec-tilde-stalk-localization`). Every stalk element is m/s.
   Express m in the chosen generators h_j, so m/s is the sum of their germs with
   coefficients r_j/s. Thus the free-sheaf map is surjective on every stalk.
4. By `lem-weil-pbc-locally-surjective-iff-stalks`, stalkwise surjectivity is surjectivity
   as a map of sheaves, hence the family generates (`def-weil-pbc-generating-sections`). -/
theorem affine_finiteType_generatingSections (U : Scheme.{u}) [IsAffine U]
    (G : U.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    Module.Finite Γ(U, ⊤) Γ(G, ⊤) ∧
      (∃ σ : SheafOfModules.GeneratingSections G, Finite σ.I) ∧
      (∀ (k : ℕ) (s : ULift.{u} (Fin k) → G.sections),
        Submodule.span (M := Γ(G, ⊤)) Γ(U, ⊤)
          (Set.range (fun i => (s i).1 (.op ⊤))) = ⊤ →
          Epi (G.freeHomEquiv.symm s)) := by
  classical
  have : (G.over ⊤).IsFiniteType := by
    exact finiteType_pushforward_leftAdjoint (Over.forget (⊤ : U.Opens)) (𝟙 _)
      (Iso.refl _)
  have hfinite : Module.Finite Γ(U, ⊤) Γ(G, ⊤) := by
    exact (((quasicoherent_finite_type_affine.{u, u} U).2 G inferInstance).1
      ⊤ (isAffineOpen_top U)).1.mp inferInstance
  have hepi {I : Type u} (s : I → G.sections)
      (hs : Submodule.span (M := Γ(G, ⊤)) Γ(U, ⊤) (Set.range (fun i ↦ (s i).1 (.op ⊤))) = ⊤) :
      Epi (G.freeHomEquiv.symm s) := by
    let φ : (SheafOfModules.free (R := U.ringCatSheaf) I : U.Modules) ⟶ G :=
      G.freeHomEquiv.symm s
    apply epi_of_surjective_app φ (fun _ : Unit ↦ ⊤)
      (fun _ ↦ isAffineOpen_top U) (by simp)
    intro _
    let L : Γ(SheafOfModules.free (R := U.ringCatSheaf) I, ⊤) →ₗ[Γ(U, ⊤)] Γ(G, ⊤) :=
      { toFun := Hom.app φ ⊤
        map_add' := fun x y ↦ (Hom.app φ ⊤).hom.map_add x y
        map_smul' := fun r x ↦ Hom.app_smul φ r x }
    change Function.Surjective L
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨(SheafOfModules.freeSection (R := U.ringCatSheaf) i).1 (.op ⊤), ?_⟩
    exact congrArg (fun t : G.sections ↦ t.1 (.op ⊤))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)
  let := hfinite
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := Γ(U, ⊤)) (M := Γ(G, ⊤))
  let s : ULift.{u} (Fin k) → G.sections := fun i ↦
    PresheafOfModules.sectionsMk
      (fun V ↦ G.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op (t i.down))
      (fun V W f ↦ by
        change G.presheaf.map f _ = _
        rw [← Functor.map_comp_apply]
        rfl)
  have hs : Submodule.span (M := Γ(G, ⊤)) Γ(U, ⊤)
      (Set.range (fun i ↦ (s i).1 (.op ⊤))) = ⊤ := by
    convert ht using 1
    congr 1
    ext x
    simp [s]
  refine ⟨hfinite, ⟨?_, ?_⟩⟩
  · exact ⟨{ I := ULift.{u} (Fin k), s := s, epi := hepi s hs }, inferInstance⟩
  · intro k s hs
    exact hepi s hs

end AlgebraicGeometry.Scheme.Modules
