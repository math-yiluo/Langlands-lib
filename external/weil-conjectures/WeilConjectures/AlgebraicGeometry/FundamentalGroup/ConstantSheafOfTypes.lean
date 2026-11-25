/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TrivialCover
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant sheaves of sets on the small étale site

For a discrete space `S`, the constant sheaf of sets with value `S` on the small étale site of a
scheme `Y` is the sheaf `U ↦ C(U, S)` of locally constant functions
(`AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheafOfTypes`); this is the
analogue for sheaves of sets of `AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheaf`.

Consequently, if a sheaf of sets `E` is constant over an étale `Y`-scheme `T`, with value `S`,
its sections over every `Z` over `T` are the locally constant functions `Z → S`. If moreover
`T` is nonempty and the stalks of `E` are finite, `S` is finite, and the restriction of `E` to
étale schemes over any `W ⟶ T` is represented by the trivial cover `∐_{s ∈ S} W`
(`AlgebraicGeometry.Scheme.Etale.exists_representableBy_trivialOver_of_isConstant`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace Etale

variable (Y : Scheme.{u}) (S : Type (u + 1)) [TopologicalSpace S]

/-- The sheaf of sets `U ↦ C(U, S)` of continuous functions with values in a topological space
`S`, on the small étale site of `Y`. It is the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheaf`. -/
noncomputable def continuousMapSheafOfTypes : Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  ((toProEt Y ⋙ ProEt.forget Y ⋙ Over.forget Y).sheafPushforwardContinuous _ _
    proetaleTopology).obj
    ⟨continuousMapPresheaf.{u + 1, u} S,
      .of_le proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf S)⟩

lemma continuousMapSheafOfTypes_obj_obj (U : Y.Etale) :
    (continuousMapSheafOfTypes Y S).obj.obj (op U) = C(U.left, S) :=
  rfl

lemma continuousMapSheafOfTypes_obj_map_apply {U V : Y.Etale} (f : U ⟶ V) (s : C(V.left, S)) :
    (continuousMapSheafOfTypes Y S).obj.map f.op s = s.comp f.left.base.hom :=
  rfl

variable [DiscreteTopology S]

/-- The constant functions, as a map from the constant presheaf with value `S` to the sheaf of
continuous functions `U ↦ C(U, S)`. -/
noncomputable def constToContinuousMapOfTypes :
    (Functor.const Y.Etaleᵒᵖ).obj S ⟶ (continuousMapSheafOfTypes Y S).obj where
  app _ := TypeCat.ofHom fun a ↦ ContinuousMap.const _ a
  naturality _ _ _ := rfl

/-- A continuous function to a discrete space is locally constant. -/
instance : Presheaf.IsLocallySurjective Y.smallEtaleTopology
    (constToContinuousMapOfTypes Y S) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, S) := s₀
    let V (m : S) : Y.Etale := Etale.mk ((U.left.fiberOpens s m).ι ≫ U.hom)
    let ι (m : S) : V m ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens s m).ι rfl
    refine Y.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨m⟩
      refine ⟨m, ContinuousMap.ext fun x ↦ ?_⟩
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective Y.smallEtaleTopology
    (constToContinuousMapOfTypes Y S) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact Y.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (Y.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left :=
        ⟨fun x ↦ hab (congr_arg (fun f : C(U.unop.left, S) ↦ f x) h)⟩
      refine Y.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

/-- The map from the constant sheaf with value `S` to the sheaf `U ↦ C(U, S)` sending the
constant section `a` to the constant function `a`. -/
noncomputable def constantSheafToContinuousMapSheafOfTypes :
    (constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj S ⟶
      continuousMapSheafOfTypes Y S :=
  ((sheafificationAdjunction Y.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
    (constToContinuousMapOfTypes Y S)

omit [DiscreteTopology S] in
lemma toSheafify_constantSheafToContinuousMapSheafOfTypes :
    toSheafify Y.smallEtaleTopology _ ≫ (constantSheafToContinuousMapSheafOfTypes Y S).hom =
      constToContinuousMapOfTypes Y S := by
  have h := ((sheafificationAdjunction Y.smallEtaleTopology (Type (u + 1))).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj S)
      (continuousMapSheafOfTypes Y S)).apply_symm_apply (constToContinuousMapOfTypes Y S)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (constantSheafToContinuousMapSheafOfTypes Y S) := by
  have h := toSheafify_constantSheafToContinuousMapSheafOfTypes Y S
  refine (Sheaf.isLocallyBijective_iff_isIso (constantSheafToContinuousMapSheafOfTypes Y S)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify Y.smallEtaleTopology _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify Y.smallEtaleTopology _), h]
    infer_instance

/-- **The constant sheaf of sets is the sheaf of locally constant functions.** For a discrete
space `S`, the constant sheaf with value `S` on the small étale site of `Y` is isomorphic to the
sheaf `U ↦ C(U, S)`, by the map sending the constant section `a` to the constant function
`a`. -/
noncomputable def constantSheafIsoContinuousMapSheafOfTypes :
    (constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj S ≅ continuousMapSheafOfTypes Y S :=
  asIso (constantSheafToContinuousMapSheafOfTypes Y S)

variable {Y}

/-- If a sheaf of sets `E` is constant over an étale `Y`-scheme `T`, then for some discrete
space `S` its sections over every `Z` over `T` are the locally constant functions `Z → S`,
naturally in `Z`. -/
theorem exists_iso_continuousMapSheafOfTypes_of_isConstant
    (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (T : Y.Etale)
    (h : (E.over T).IsConstant (Y.smallEtaleTopology.over T)) :
    ∃ (S : Type (u + 1)) (_ : TopologicalSpace S) (_ : DiscreteTopology S),
      Nonempty ((Over.forget T).op ⋙ E.obj ≅
        (Over.forget T).op ⋙ (continuousMapSheafOfTypes Y S).obj) := by
  obtain ⟨S, ⟨i⟩⟩ := (E.over T).mem_essImage_of_isConstant
  let _ : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let j : E.over T ≅ (continuousMapSheafOfTypes Y S).over T :=
    i.symm ≪≫ ((Y.smallEtaleTopology.overPullbackConstantSheafIso (Type (u + 1)) T).app S).symm ≪≫
      (Y.smallEtaleTopology.overPullback (Type (u + 1)) T).mapIso
        (constantSheafIsoContinuousMapSheafOfTypes Y S)
  exact ⟨S, _, this, ⟨(sheafToPresheaf _ _).mapIso j⟩⟩

/-- If a sheaf of sets `E` with finite stalks has sections `C(Z, S)` over all `Z` over a
nonempty étale `Y`-scheme `T`, naturally in `Z`, then `S` is finite: distinct constant
functions give distinct elements of the stalk at a geometric point of `T`. -/
theorem finite_of_iso_continuousMapSheafOfTypes
    (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (hE : IsFiniteSheaf E) (T : Y.Etale)
    (t : T.left) {S : Type (u + 1)} [TopologicalSpace S] [DiscreteTopology S]
    (e : (Over.forget T).op ⋙ E.obj ≅
      (Over.forget T).op ⋙ (continuousMapSheafOfTypes Y S).obj) :
    Finite S := by
  let K := T.left.residueField t
  let Ω := AlgebraicClosure K
  let s' : Spec (.of Ω) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ T.left.fromSpecResidueField t
  let s : Spec (.of Ω) ⟶ Y := s' ≫ T.hom
  let Φ := pointSmallEtale s
  let t' : Φ.fiber.obj T := Over.homMk s' rfl
  have hfin : Finite (ToType (Φ.sheafFiber.obj E)) :=
    (ConcreteCategory.isFinitelyGenerated_iff_finite _).1
      (hE.isFinitelyGenerated_sheafFiber Ω s)
  let ψ : S → ToType (Φ.sheafFiber.obj E) := fun a ↦
    Φ.toPresheafFiber T t' E.obj (e.inv.app (op (Over.mk (𝟙 T))) (ContinuousMap.const _ a))
  refine Finite.of_injective ψ fun a b hab ↦ ?_
  obtain ⟨V, f, v, -, hv⟩ := (Φ.toPresheafFiber_eq_iff' T t' _ _).1 hab
  let g : Over.mk f ⟶ Over.mk (𝟙 T) := Over.homMk f (by simp)
  have key (c : S) : e.hom.app (op (Over.mk f))
      (E.obj.map f.op (e.inv.app (op (Over.mk (𝟙 T))) (ContinuousMap.const _ c))) =
        ContinuousMap.const _ c := by
    have h₁ := NatTrans.naturality_apply e.hom g.op
      (e.inv.app (op (Over.mk (𝟙 T))) (ContinuousMap.const _ c))
    refine h₁.trans ?_
    simp only [Iso.inv_hom_id_app_apply]
    rfl
  have := congr_arg (e.hom.app (op (Over.mk f))) hv
  rw [key, key] at this
  exact congr_arg (fun φ : C(V.left, S) ↦ φ (v.left (IsLocalRing.closedPoint Ω))) this

/-- Postcomposition with a bijection of discrete spaces. -/
def continuousMapEquivOfEquiv {X : Type*} [TopologicalSpace X] {S S₀ : Type*} [TopologicalSpace S]
    [DiscreteTopology S] [TopologicalSpace S₀] [DiscreteTopology S₀] (σ : S ≃ S₀) :
    C(X, S) ≃ C(X, S₀) where
  toFun c := (ContinuousMap.mk σ continuous_of_discreteTopology).comp c
  invFun c := (ContinuousMap.mk σ.symm continuous_of_discreteTopology).comp c
  left_inv c := by ext; simp
  right_inv c := by ext; simp

/-- The restriction of `E` to étale schemes over `W` is represented by the trivial cover
`∐_{s ∈ S} W`, if `W` maps to an étale `Y`-scheme `T` over which the sections of `E` are the
locally constant functions with values in a discrete space `S₀ ≃ S`. -/
noncomputable def representableByTrivialOver (E : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    {T : Y.Etale} {S₀ : Type (u + 1)} [TopologicalSpace S₀] [DiscreteTopology S₀]
    (e : (Over.forget T).op ⋙ E.obj ≅
      (Over.forget T).op ⋙ (continuousMapSheafOfTypes Y S₀).obj)
    {S : Type u} [TopologicalSpace S] [DiscreteTopology S] (σ : S ≃ S₀) {W : Y.Etale}
    (a : W ⟶ T) :
    ((Over.forget W).op ⋙ E.obj).RepresentableBy (trivialOver S W) where
  homEquiv {Z} := (trivialOverHomEquiv Z).trans
    ((continuousMapEquivOfEquiv σ).trans (e.app (op (Over.mk (Z.hom ≫ a)))).symm.toEquiv)
  homEquiv_comp {Z' Z} f t := by
    let g : Over.mk (Z'.hom ≫ a) ⟶ Over.mk (Z.hom ≫ a) :=
      Over.homMk f.left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w f])
    have h := NatTrans.naturality_apply e.inv g.op
      (continuousMapEquivOfEquiv σ (trivialOverHomEquiv Z t))
    change e.inv.app (op (Over.mk (Z'.hom ≫ a)))
      (continuousMapEquivOfEquiv σ (trivialOverHomEquiv Z' (f ≫ t))) = _
    rw [trivialOverHomEquiv_comp]
    exact h

/-- **Constant sheaves with finite stalks are represented by trivial covers.** If a sheaf of
sets `E` with finite stalks is constant over a nonempty étale `Y`-scheme `T`, there is a finite
set `S` such that for every `W ⟶ T` the restriction of `E` to étale schemes over `W` is
represented by the trivial cover `∐_{s ∈ S} W`. -/
theorem exists_representableBy_trivialOver_of_isConstant
    (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (hE : IsFiniteSheaf E) (T : Y.Etale)
    (t : T.left) (h : (E.over T).IsConstant (Y.smallEtaleTopology.over T)) :
    ∃ (S : Type u) (_ : Finite S), ∀ {W : Y.Etale} (_ : W ⟶ T),
      Nonempty (((Over.forget W).op ⋙ E.obj).RepresentableBy (trivialOver S W)) := by
  obtain ⟨S₀, _, _, ⟨e⟩⟩ := exists_iso_continuousMapSheafOfTypes_of_isConstant E T h
  have := finite_of_iso_continuousMapSheafOfTypes E hE T t e
  let S : Type u := ULift.{u} (Fin (Nat.card S₀))
  let _ : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let σ : S ≃ S₀ := Equiv.ulift.trans (Finite.equivFin S₀).symm
  exact ⟨S, inferInstance, fun a ↦ ⟨representableByTrivialOver E e σ a⟩⟩

/-- If the sections of a sheaf of sets `E` over all `Z` over an étale `Y`-scheme `T` are the
locally constant functions `Z → S` to a discrete space `S`, naturally in `Z`, then `E` is
constant over `T`. -/
theorem isConstant_over_of_iso_continuousMapSheafOfTypes
    (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) {T : Y.Etale} {S : Type (u + 1)}
    [TopologicalSpace S] [DiscreteTopology S]
    (e : (Over.forget T).op ⋙ E.obj ≅
      (Over.forget T).op ⋙ (continuousMapSheafOfTypes Y S).obj) :
    (E.over T).IsConstant (Y.smallEtaleTopology.over T) := by
  let j : E.over T ≅ (continuousMapSheafOfTypes Y S).over T :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (X := E.over T)
      (Y := (continuousMapSheafOfTypes Y S).over T) e
  exact Sheaf.isConstant_of_iso _ (j ≪≫
    (Y.smallEtaleTopology.overPullback (Type (u + 1)) T).mapIso
      (constantSheafIsoContinuousMapSheafOfTypes Y S).symm ≪≫
    (Y.smallEtaleTopology.overPullbackConstantSheafIso (Type (u + 1)) T).app S)

end Etale

end AlgebraicGeometry.Scheme
