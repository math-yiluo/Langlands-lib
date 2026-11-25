/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineCapture
import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluing

/-! # The finite-type submodule on the union with an affine open

Source: Stacks Project, Properties, Lemma 01PF, affine reduction and gluing.
(blueprint: lem-weil-pbc-module-finite-type-affine-union).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem finiteType_of_iso.{u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  apply SheafOfModules.IsFiniteType.mk (R := R)
  refine ⟨q', ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := q') (fun i ↦ ?_)
  have := hq.isFiniteType i
  exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType


set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_pushforward.{u₁, u₂, v₁, v₂}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.Limits.HasPullbacks D]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J] [G.IsLeftAdjoint]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R) [IsIso φ]
    (η : (SheafOfModules.pushforward.{u} φ).obj (unit R) ≅ unit S)
    (M : SheafOfModules.{u} R) [M.IsFiniteType] :
    ((SheafOfModules.pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let d : ((SheafOfModules.pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : q.I), G.obj X ⟶ q.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let F := Over.post (X := i.1) G ⋙ Over.map i.2.2
        have : F.IsContinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          Functor.isContinuous_comp _ _ _ (J.over _) _
        have : F.IsCocontinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          isCocontinuous_comp _ _ _ (J.over _)
        let ψ : S.over i.1 ⟶
            (F.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (q.X i.2.1))).obj (R.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          isLeftAdjoint_pushforward_of_isIso ψ
        let e := (overFunctor S i.1).mapIso η
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) e.symm }
  apply SheafOfModules.IsFiniteType.mk (R := S)
  refine ⟨d.shrink, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d.shrink) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.choose.2.1
  dsimp [LocalGeneratorsData.shrink, d]
  infer_instance

/-- Construct the finite-type submodule on the union, before extending it to X.

Source: Stacks Project, Properties, Lemma 01PF, proof, affine reduction and gluing
(https://stacks.math.columbia.edu/tag/01PF).
(blueprint: lem-weil-pbc-module-finite-type-affine-union).

Proof: Quasi-separatedness makes the overlap W intersect V quasi-compact. Identify
H on V with the tilde of its sections. Finite type on W restricts to finite type on
this overlap. Choose a finite cover of the overlap by principal opens D(f_i) with
finitely generated localized modules of sections. Write finitely many generators
as fractions and span their numerators in H(V), obtaining a finitely generated
submodule N. Localization of N includes every chosen generator, so its inclusion
into H(V) becomes an isomorphism on each D(f_i). Tilde is exact, hence tilde N is
a quasi-coherent finite-type submodule on V agreeing with H on the overlap.
Glue this inclusion with the identity inclusion of H on W: sections on an open
of W union V are sections of H whose restrictions to V belong to tilde N.
The sheaf gluing axiom gives the prescribed restrictions and a monomorphism into
H on the union. Quasi-coherence and finite type are local, so the glued module
has both properties. Its restriction to W is H, and its inclusion there is an
isomorphism. If the overlap is empty, use the zero submodule on V and the empty
set of numerators. If W or V is empty the same construction still applies.
This statement constructs only a module on the union; extension to X and the
image of the extended map are separate steps. -/
theorem exists_finiteType_affine_union
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V.1)),
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ ∃ (φ : G ⟶ H.over (W ⊔ V.1)),
        Mono φ ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V.1 from le_sup_left))).map φ) := by
  let R := moduleRings X.toRingedSpace
  let K : X.Opens := W ⊓ V.1
  have hK : IsCompact (K : Set X) :=
    show IsCompact ((W : Set X) ∩ (V.1 : Set X)) from
      QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.1.isOpen V.2.isCompact
  let f : K ⟶ W := homOfLE inf_le_left
  let : (Over.map f).Faithful :=
    { map_injective := fun h ↦ by
        ext
        exact congrArg (fun g ↦ g.left) h }
  let : (Over.map f).Full :=
    { map_surjective := fun {A B} g ↦
        ⟨Over.homMk g.left (by
          apply (cancel_mono f).mp
          have hg := g.w
          change g.left ≫ (B.hom ≫ f) = A.hom ≫ f at hg
          simpa only [Category.assoc] using hg), rfl⟩ }
  let J := _root_.Opens.grothendieckTopology X
  have (T : Over K) : (Over.post (X := T) (Over.map f)).IsContinuous
      ((J.over K).over T) ((J.over W).over ((Over.map f).obj T)) := by
    let F := Over.post (X := T) (Over.map f)
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfDownwardsClosed _ F ?_)
      ((GrothendieckTopology.over_map_coverPreserving J f).overPost T)
    intro c d a
    let d' : Over K := Over.mk (d.hom.left ≫ T.hom)
    let c' : Over T := Over.mk (Over.homMk d.hom.left : d' ⟶ T)
    exact ⟨c', Over.isoMk (Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
      (by ext; exact Subsingleton.elim _ _)⟩
  have hfinite : ((SheafOfModules.overMap R f).obj (H.over W)).IsFiniteType := by
    exact finiteType_pushforward (Over.map f) _
      (SheafOfModules.overMapUnitIso f) (H.over W)
  let : ((SheafOfModules.overFunctor R W ⋙ SheafOfModules.overMap R f).obj H).IsFiniteType :=
    hfinite
  have : (H.over K).IsFiniteType :=
    finiteType_of_iso.{u, u, u} ((SheafOfModules.overFunctorMap R f).app H)
  obtain ⟨Q, hQ, hQft, ι, hι, hιK⟩ := exists_finiteType_affine_capture X V K hK inf_le_right H
  have : Q.IsQuasicoherent := hQ
  have : Q.IsFiniteType := hQft
  have : Mono ι := hι
  have : IsIso ((SheafOfModules.overMap R
      (homOfLE (show W ⊓ V.1 ≤ V.1 from inf_le_right))).map ι) := hιK
  exact exists_submodule_binary_gluing X W V.1 H Q ι

end AlgebraicGeometry.Scheme.Modules
