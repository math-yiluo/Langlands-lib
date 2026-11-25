/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constant sheaves of sets on the small étale site and trivial covers

For a discrete set `S`, the constant sheaf of sets with value `S` on the small étale site of a
scheme `X` is the sheaf `V ↦ C(V, S)` of locally constant functions
(`AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheafType`). When `S` is in
bijection with a type `S'` in the universe of `X`, this sheaf is represented by the trivial
cover `∐_{S'} X ⟶ X`: a morphism `V ⟶ ∐_{S'} X` over `X` is the same as a locally constant
function `V → S'` (`AlgebraicGeometry.Scheme.sigmaHomEquiv`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section ContinuousMap

variable (X : Scheme.{u}) (A : Type (u + 1)) [TopologicalSpace A]

/-- The sheaf of sets `U ↦ C(U, A)` of continuous functions with values in a topological space
`A`, on the small étale site of `X`. It is the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheaf`. -/
noncomputable def Etale.continuousMapSheafType : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ((toProEt X ⋙ ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _
    proetaleTopology).obj
    ⟨continuousMapPresheaf.{u + 1, u} A,
      .of_le proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf A)⟩

/-- The sections of `U ↦ C(U, A)` over `U` are the continuous functions on `U`. -/
lemma Etale.continuousMapSheafType_obj_obj (U : X.Etale) :
    (Etale.continuousMapSheafType X A).obj.obj (op U) = C(U.left, A) :=
  rfl

/-- The restriction maps of `U ↦ C(U, A)` are given by precomposition. -/
lemma Etale.continuousMapSheafType_obj_map_apply {U V : X.Etale} (f : U ⟶ V)
    (s : C(V.left, A)) :
    (Etale.continuousMapSheafType X A).obj.map f.op s = s.comp f.left.base.hom :=
  rfl


variable [DiscreteTopology A]

/-- The constant functions, as a map from the constant presheaf with value `A` to the sheaf of
continuous functions `U ↦ C(U, A)`. -/
noncomputable def Etale.constToContinuousMapType :
    (Functor.const X.Etaleᵒᵖ).obj A ⟶ (Etale.continuousMapSheafType X A).obj where
  app _ := ↾fun a ↦ ContinuousMap.const _ a
  naturality _ _ _ := rfl

/-- A continuous function to a discrete space is locally constant: it is constant on the open
fibres, which cover. -/
instance : Presheaf.IsLocallySurjective X.smallEtaleTopology
    (Etale.constToContinuousMapType X A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀
    let V (m : A) : X.Etale := Etale.mk ((U.left.fiberOpens s m).ι ≫ U.hom)
    let ι (m : A) : V m ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens s m).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨m⟩
      refine ⟨m, ContinuousMap.ext fun x ↦ ?_⟩
      change m = s x.1
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective X.smallEtaleTopology
    (Etale.constToContinuousMapType X A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (X.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left :=
        ⟨fun x ↦ hab (by have := congr_arg (fun f : C(U.unop.left, A) ↦ f x) h; exact this)⟩
      refine X.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

/-- The map from the constant sheaf of sets with value `A` to the sheaf of continuous functions
`U ↦ C(U, A)` sending the constant section `a` to the constant function `a`. -/
noncomputable def Etale.constantSheafToContinuousMapSheafType :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj A ⟶
      Etale.continuousMapSheafType X A :=
  ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
    (Etale.constToContinuousMapType X A)

omit [DiscreteTopology A] in
/-- The map from the constant sheaf to `U ↦ C(U, A)` restricts to the constant functions. -/
lemma Etale.toSheafify_constantSheafToContinuousMapSheafType [DiscreteTopology A] :
    toSheafify X.smallEtaleTopology _ ≫ (Etale.constantSheafToContinuousMapSheafType X A).hom =
      Etale.constToContinuousMapType X A := by
  have h := ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv
    ((Functor.const X.Etaleᵒᵖ).obj A)
      (Etale.continuousMapSheafType X A)).apply_symm_apply (Etale.constToContinuousMapType X A)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

/-- The map from the constant sheaf to `U ↦ C(U, A)` is an isomorphism: it is locally bijective.
-/
instance : IsIso (Etale.constantSheafToContinuousMapSheafType X A) := by
  have h := Etale.toSheafify_constantSheafToContinuousMapSheafType X A
  refine (Sheaf.isLocallyBijective_iff_isIso
    (Etale.constantSheafToContinuousMapSheafType X A)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance

/-- **The constant sheaf of sets is the sheaf of locally constant functions.** For a discrete
set `A`, the constant sheaf with value `A` on the small étale site of `X` is isomorphic to the
sheaf `U ↦ C(U, A)`, by the map sending the constant section `a` to the constant function `a`. -/
noncomputable def Etale.constantSheafIsoContinuousMapSheafType :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj A ≅
      Etale.continuousMapSheafType X A :=
  asIso (Etale.constantSheafToContinuousMapSheafType X A)

end ContinuousMap
section Sigma

variable (S' : Type u) (X : Scheme.{u}) [TopologicalSpace S'] [DiscreteTopology S']

/-- The index of the summand of `∐_{S'} X` containing a point, as a continuous function. -/
noncomputable def sigmaIdx : C(↑(∐ fun _ : S' ↦ X), S') :=
  ⟨fun z ↦ ((sigmaMk fun _ : S' ↦ X).symm z).1,
    (continuous_sigma_iff.2 fun _ ↦ continuous_const).comp (sigmaMk _).symm.continuous⟩

omit [DiscreteTopology S'] in
/-- The index of a point of the `σ`-th summand of `∐_{S'} X` is `σ`. -/
@[simp]
lemma sigmaIdx_ι (σ : S') (x : X) : sigmaIdx S' X (Sigma.ι (fun _ : S' ↦ X) σ x) = σ := by
  change ((sigmaMk fun _ : S' ↦ X).symm (Sigma.ι (fun _ : S' ↦ X) σ x)).1 = σ
  rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

variable {S' X}

/-- On the open subscheme of `W` where the index of `a : W ⟶ ∐_{S'} X` is `σ`, the morphism `a`
is the composite of `w` with the inclusion of the `σ`-th summand. -/
lemma comp_sigmaIdx_apply {W : Scheme.{u}} (a : W ⟶ ∐ fun _ : S' ↦ X) (w : W ⟶ X)
    (ha : a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w) (σ : S') :
    (W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ).ι ≫ a =
      (W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ).ι ≫ w ≫ Sigma.ι (fun _ : S' ↦ X) σ := by
  let O := W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ
  have hrange : Set.range (O.ι ≫ a) ⊆ Set.range (Sigma.ι (fun _ : S' ↦ X) σ) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨τ, y, hy⟩ := (sigmaOpenCover fun _ : S' ↦ X).exists_eq ((O.ι ≫ a) z)
    have hτ : τ = σ := by
      have h1 : sigmaIdx S' X ((O.ι ≫ a) z) = σ := z.2
      rw [← hy] at h1
      exact (sigmaIdx_ι S' X τ y).symm.trans h1
    subst hτ
    exact ⟨y, hy⟩
  have h := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : S' ↦ X) σ) (O.ι ≫ a) hrange
  have hl := congrArg (· ≫ Sigma.desc (fun _ : S' ↦ 𝟙 X)) h
  simp only [Category.assoc, Sigma.ι_comp_desc, Category.comp_id, ha] at hl
  rw [← h, hl, Category.assoc]

variable {A : Type w} [TopologicalSpace A] [DiscreteTopology A] (e : A ≃ S')

/-- **Morphisms into a trivial cover are locally constant functions.** For `w : W ⟶ X`, the
morphisms `a : W ⟶ ∐_{S'} X` over `X` correspond to the locally constant functions `W → A`,
for `A ≃ S'`: the function attached to `a` sends `z` to the index of the summand containing
`a z`. -/
noncomputable def sigmaHomEquiv {W : Scheme.{u}} (w : W ⟶ X) :
    C(W, A) ≃ {a : W ⟶ ∐ fun _ : S' ↦ X // a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w} where
  toFun f := ⟨W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)), by
    rw [Scheme.glueOfContinuousMap_comp]
    exact Scheme.glueOfContinuousMap_eq fun m ↦ by simp⟩
  invFun a := ⟨fun z ↦ e.symm (sigmaIdx S' X (a.1 z)),
    continuous_of_discreteTopology.comp ((sigmaIdx S' X).comp a.1.base.hom).continuous⟩
  left_inv f := by
    ext z
    have h := Scheme.fiberOpens_ι_glueOfContinuousMap f
      (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) (f z)
    have := congrArg (fun g ↦ g ⟨z, (rfl : f z = f z)⟩) h
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
    change e.symm (sigmaIdx S' X
      (W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) z)) = f z
    rw [this, sigmaIdx_ι, Equiv.symm_apply_apply]
  right_inv a := by
    refine Subtype.ext (Scheme.glueOfContinuousMap_eq fun m ↦ ?_)
    have h := comp_sigmaIdx_apply a.1 w a.2 (e m)
    have hO : W.fiberOpens ⟨fun z ↦ e.symm (sigmaIdx S' X (a.1 z)),
        continuous_of_discreteTopology.comp ((sigmaIdx S' X).comp a.1.base.hom).continuous⟩ m =
        W.fiberOpens ((sigmaIdx S' X).comp a.1.base.hom) (e m) := by
      ext z
      exact e.symm_apply_eq
    rw [hO]
    exact h.symm

/-- The morphism attached to a locally constant function `f` is glued from the inclusions of the
summands on the fibres of `f`. -/
lemma sigmaHomEquiv_apply_coe {W : Scheme.{u}} (w : W ⟶ X) (f : C(W, A)) :
    (sigmaHomEquiv e w f).1 =
      W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) := rfl

/-- The locally constant function attached to `a : W ⟶ ∐_{S'} X` is the index of the summand. -/
lemma sigmaHomEquiv_symm_apply {W : Scheme.{u}} (w : W ⟶ X)
    (a : {a : W ⟶ ∐ fun _ : S' ↦ X // a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w}) (z : W) :
    (sigmaHomEquiv e w).symm a z = e.symm (sigmaIdx S' X (a.1 z)) := rfl


/-- `sigmaHomEquiv` is natural in `W`. -/
lemma sigmaHomEquiv_comp {W W' : Scheme.{u}} (φ : W' ⟶ W) (w : W ⟶ X) (f : C(W, A)) :
    (sigmaHomEquiv e (φ ≫ w) (f.comp φ.base.hom)).1 = φ ≫ (sigmaHomEquiv e w f).1 := by
  rw [sigmaHomEquiv_apply_coe, sigmaHomEquiv_apply_coe, Scheme.comp_glueOfContinuousMap]
  simp only [Category.assoc]

/-- `sigmaHomEquiv` is natural in `W`, in a form with the base morphisms only equal. -/
lemma sigmaHomEquiv_comp' {W W' : Scheme.{u}} (φ : W' ⟶ W) (w : W ⟶ X) {w' : W' ⟶ X}
    (hw : φ ≫ w = w') (f : C(W, A)) :
    (sigmaHomEquiv e w' (f.comp φ.base.hom)).1 = φ ≫ (sigmaHomEquiv e w f).1 := by
  subst hw
  exact sigmaHomEquiv_comp e φ w f

end Sigma
section Restrict

variable {T : Scheme.{u}} (E : T.Etaleᵒᵖ ⥤ Type (u + 1)) (U : T.Etale)

/-- The restriction of a presheaf on the small étale site of `T` to the small étale site of an
étale `T`-scheme `U`: its sections over `W ⟶ U` are the sections over `W ⟶ U ⟶ T`. It is the
presheaf underlying `(Etale.overSheafEquiv U _).functor.obj (E.over U)`. -/
abbrev Etale.restrictPresheaf : U.left.Etaleᵒᵖ ⥤ Type (u + 1) :=
  (Scheme.Etale.etaleToOver U ⋙ CategoryTheory.Over.forget U).op ⋙ E

variable (S' : Type u)

/-- The trivial cover `∐_{S'} U ⟶ U ⟶ T`, as an étale `T`-scheme. -/
noncomputable abbrev Etale.trivialCover : T.Etale :=
  have : AlgebraicGeometry.Etale (Sigma.desc fun _ : S' ↦ 𝟙 U.left) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  Etale.mk (Sigma.desc (fun _ : S' ↦ 𝟙 U.left) ≫ U.hom)

/-- The trivial cover `∐_{S'} U ⟶ U`, as an étale `U`-scheme. -/
noncomputable abbrev Etale.trivialCover' : U.left.Etale :=
  have : AlgebraicGeometry.Etale (Sigma.desc fun _ : S' ↦ 𝟙 U.left) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  Etale.mk (Sigma.desc (fun _ : S' ↦ 𝟙 U.left))

variable [TopologicalSpace S'] [DiscreteTopology S'] {A : Type (u + 1)} [TopologicalSpace A]
  [DiscreteTopology A] (e : A ≃ S')

variable {E U S'}

/-- A universal section on the trivial cover `∐_{S'} U` identifies the restriction of `E` to `U`
with the sheaf of locally constant `A`-valued functions, for `A ≃ S'`. -/
noncomputable def Etale.isoOfIsUniversalSection {ξ : E.obj (op (Etale.trivialCover U S'))}
    (h : IsUniversalSection E U.hom (Etale.trivialCover U S') (Sigma.desc fun _ ↦ 𝟙 U.left) ξ) :
    Etale.restrictPresheaf E U ≅ (Etale.continuousMapSheafType U.left A).obj := by
  let κ (W : U.left.Etale) (f : C(W.left, A)) : E.obj (op (Etale.mk (W.hom ≫ U.hom))) :=
    E.map (MorphismProperty.Over.homMk (sigmaHomEquiv e W.hom f).1 (by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ U.hom) (sigmaHomEquiv e W.hom f).2)) :
        Etale.mk (W.hom ≫ U.hom) ⟶ Etale.trivialCover U S').op ξ
  have hκ (W : U.left.Etale) : Function.Bijective (κ W) := by
    let ψ : {a : W.left ⟶ ∐ fun _ : S' ↦ U.left // a ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = W.hom} →
        {a : Etale.mk (W.hom ≫ U.hom) ⟶ Etale.trivialCover U S' //
          a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = W.hom} := fun a ↦
      ⟨MorphismProperty.Over.homMk a.1 (by
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) a.2)), a.2⟩
    have hψ : Function.Bijective ψ :=
      ⟨fun a b hab ↦ Subtype.ext (congrArg (fun c ↦ c.1.left) hab),
        fun b ↦ ⟨⟨b.1.left, b.2⟩, rfl⟩⟩
    exact ((h (Etale.mk (W.hom ≫ U.hom)) W.hom rfl).comp hψ).comp (sigmaHomEquiv e W.hom).bijective
  refine (NatIso.ofComponents (fun W ↦ (Equiv.ofBijective (κ W.unop) (hκ W.unop)).toIso)
    (fun {W₁ W₂} φ ↦ ?_)).symm
  ext f
  change κ W₂.unop (f.comp φ.unop.left.base.hom) =
    E.map (MorphismProperty.Over.homMk φ.unop.left (by
      change φ.unop.left ≫ W₁.unop.hom ≫ U.hom = W₂.unop.hom ≫ U.hom
      rw [MorphismProperty.Over.w_assoc]) :
        Etale.mk (W₂.unop.hom ≫ U.hom) ⟶ Etale.mk (W₁.unop.hom ≫ U.hom)).op (κ W₁.unop f)
  simp only [κ]
  rw [← Functor.map_comp_apply, ← op_comp]
  refine congrArg (fun g ↦ E.map (Opposite.op g) ξ) (EtaleTorsor.etaleHom_ext ?_)
  change (sigmaHomEquiv e W₂.unop.hom (f.comp φ.unop.left.base.hom)).1 =
    φ.unop.left ≫ (sigmaHomEquiv e W₁.unop.hom f).1
  exact sigmaHomEquiv_comp' e φ.unop.left _ (MorphismProperty.Over.w φ.unop) f
/-- The restriction of `E` to `U` evaluated on a morphism of étale `U`-schemes is `E` evaluated
on the corresponding morphism of étale `T`-schemes. -/
lemma Etale.restrictPresheaf_map_eq {W₁ W₂ : U.left.Etale} (a : W₁ ⟶ W₂)
    (b : Etale.mk (W₁.hom ≫ U.hom) ⟶ Etale.mk (W₂.hom ≫ U.hom)) (hab : b.left = a.left)
    (x : E.obj (op (Etale.mk (W₂.hom ≫ U.hom)))) :
    (Etale.restrictPresheaf E U).map a.op x = E.map b.op x :=
  congrArg (fun g ↦ E.map (Opposite.op g) x) (EtaleTorsor.etaleHom_ext hab.symm)

/-- **An identification with locally constant functions gives a universal section.** If the
restriction of `E` to `U` is identified with the sheaf of locally constant `A`-valued functions,
`A ≃ S'`, then the section corresponding to the index function of `∐_{S'} U` is universal on
the trivial cover `∐_{S'} U ⟶ U`. -/
lemma Etale.isUniversalSection_of_iso
    (α : Etale.restrictPresheaf E U ≅ (Etale.continuousMapSheafType U.left A).obj) :
    IsUniversalSection E U.hom (Etale.trivialCover U S') (Sigma.desc fun _ ↦ 𝟙 U.left)
      (α.inv.app (op (Etale.trivialCover' U S'))
        ((sigmaHomEquiv e (Sigma.desc fun _ : S' ↦ 𝟙 U.left)).symm
          ⟨𝟙 _, Category.id_comp _⟩)) := by
  refine IsUniversalSection.of_mk fun W w _ ↦ ?_
  let W'' : U.left.Etale := Etale.mk w
  let idx := (sigmaHomEquiv e (Sigma.desc fun _ : S' ↦ 𝟙 U.left)).symm ⟨𝟙 _, Category.id_comp _⟩
  let ψ : {a : Etale.mk (w ≫ U.hom) ⟶ Etale.trivialCover U S' //
      a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} →
      {a : W ⟶ ∐ fun _ : S' ↦ U.left // a ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} :=
    fun a ↦ ⟨a.1.left, a.2⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b hab ↦ Subtype.ext (EtaleTorsor.etaleHom_ext (congrArg Subtype.val hab)),
      fun b ↦ ?_⟩
    refine ⟨⟨MorphismProperty.Over.homMk b.1 ?_, b.2⟩, rfl⟩
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) b.2)
  have key : α.hom.app (op W'') ∘ (fun a : {a : Etale.mk (w ≫ U.hom) ⟶ Etale.trivialCover U S' //
      a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} ↦
        E.map a.1.op (α.inv.app (op (Etale.trivialCover' U S')) idx)) =
      (sigmaHomEquiv e w).symm ∘ ψ := by
    ext1 a
    let a'' : W'' ⟶ Etale.trivialCover' U S' := MorphismProperty.Over.homMk a.1.left a.2
    have h1 : E.map a.1.op (α.inv.app (op (Etale.trivialCover' U S')) idx) =
        (Etale.restrictPresheaf E U).map a''.op
          (α.inv.app (op (Etale.trivialCover' U S')) idx) :=
      (Etale.restrictPresheaf_map_eq a'' a.1 rfl _).symm
    have h2 : α.hom.app (op (Etale.trivialCover' U S'))
        (α.inv.app (op (Etale.trivialCover' U S')) idx) = idx := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, α.inv_hom_id]
      rfl
    rw [Function.comp_apply, h1, NatTrans.naturality_apply, h2]
    exact ContinuousMap.ext fun z ↦ rfl
  have hα : Function.Bijective (α.hom.app (op W'')) :=
    (isIso_iff_bijective _).1 inferInstance
  exact (Function.Bijective.of_comp_iff' hα _).1
    (key ▸ (sigmaHomEquiv e w).symm.bijective.comp hψ)

end Restrict
section Finite

variable {T : Scheme.{u}}

/-- If the restriction of a sheaf `E` with finite stalks to a nonempty étale `T`-scheme `U` is
the sheaf of locally constant `A`-valued functions, then `A` is finite: `A` injects into the
stalk of `E` at a geometric point of `U`, a constant function being determined by its value at
a point. -/
lemma Etale.finite_of_iso {E : Sheaf T.smallEtaleTopology (Type (u + 1))} (hfin : IsFiniteSheaf E)
    (U : T.Etale) (x : U.left) {A : Type (u + 1)} [TopologicalSpace A] [DiscreteTopology A]
    (α : Etale.restrictPresheaf E.obj U ≅ (Etale.continuousMapSheafType U.left A).obj) :
    Finite A := by
  let Ω := AlgebraicClosure (U.left.residueField x)
  let t : Spec (.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫
      U.left.fromSpecResidueField x
  let s : Spec (.of Ω) ⟶ T := t ≫ U.hom
  let Φ := pointSmallEtale s
  let V0 : U.left.Etale := Etale.mk (𝟙 U.left)
  let U' : T.Etale := Etale.mk (𝟙 U.left ≫ U.hom)
  let x' : Φ.fiber.obj U' := CategoryTheory.Over.homMk t (by
    change t ≫ 𝟙 U.left ≫ U.hom = s
    rw [Category.id_comp])
  have : Finite (ToType (Φ.sheafFiber.obj E)) :=
    (ConcreteCategory.isFinitelyGenerated_iff_finite _).1 (hfin.isFinitelyGenerated_sheafFiber Ω s)
  have : Finite (ToType (Φ.presheafFiber.obj E.obj)) := this
  let c (σ : A) : E.obj.obj (op U') := α.inv.app (op V0) (ContinuousMap.const _ σ)
  refine Finite.of_injective (fun σ ↦ Φ.toPresheafFiber U' x' E.obj (c σ)) fun σ τ hστ ↦ ?_
  obtain ⟨Y, f, y, -, hf⟩ := (Φ.toPresheafFiber_eq_iff' U' x' _ _).1 hστ
  let Y'' : U.left.Etale := Etale.mk f.left
  let f'' : Y'' ⟶ V0 := MorphismProperty.Over.homMk f.left (Category.comp_id _)
  let eY : Etale.mk (f.left ≫ U.hom) ≅ Y := MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Y.hom = f.left ≫ U.hom
    rw [Category.id_comp, ← MorphismProperty.Over.w f]
    exact congrArg (f.left ≫ ·) (Category.id_comp U.hom))
  have hc (σ : A) : (Etale.restrictPresheaf E.obj U).map f''.op (c σ) =
      E.obj.map eY.hom.op (E.obj.map f.op (c σ)) := by
    rw [← Functor.map_comp_apply, ← op_comp]
    exact Etale.restrictPresheaf_map_eq f'' _ rfl _
  have h' : (Etale.restrictPresheaf E.obj U).map f''.op (c σ) =
      (Etale.restrictPresheaf E.obj U).map f''.op (c τ) := by
    rw [hc, hc, hf]
  have hα (σ : A) : α.hom.app (op Y'') ((Etale.restrictPresheaf E.obj U).map f''.op (c σ)) =
      ContinuousMap.const _ σ := by
    have h2 : α.hom.app (op V0) (c σ) = ContinuousMap.const _ σ := by
      change α.hom.app (op V0) (α.inv.app (op V0) _) = _
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, α.inv_hom_id]
      rfl
    rw [NatTrans.naturality_apply, h2]
    exact ContinuousMap.ext fun _ ↦ rfl
  have := congrArg (α.hom.app (op Y'')) h'
  rw [hα, hα] at this
  exact congrArg (fun g : C(Y.left, A) ↦ g (y.left (IsLocalRing.closedPoint Ω))) this

end Finite

section Main

variable {T : Scheme.{u}} (E : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : T.Etale)

/-- **A constant sheaf with finite stalks is represented by a trivial finite cover.** If the
restriction of a sheaf `E` with finite stalks to a nonempty étale `T`-scheme `U` is constant,
then it is represented by a trivial finite cover `∐_{S'} U ⟶ U`.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem Etale.exists_isUniversalSection_of_isConstant (hfin : IsFiniteSheaf E) (x : U.left)
    [(E.over U).IsConstant (T.smallEtaleTopology.over U)] :
    ∃ (S' : Type u) (_ : Finite S') (ξ : E.obj.obj (op (Etale.trivialCover U S'))),
      IsUniversalSection E.obj U.hom (Etale.trivialCover U S') (Sigma.desc fun _ ↦ 𝟙 U.left)
        ξ := by
  let G := (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (E.over U)
  have : G.IsConstant U.left.smallEtaleTopology :=
    (Sheaf.isConstant_sheafCongr_functor_iff (Etale.overEquiv U)
      CategoryTheory.Over.mkIdTerminal (E.over U)).2 inferInstance
  obtain ⟨S, ⟨iS⟩⟩ := Sheaf.mem_essImage_of_isConstant _ G
  let : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let α : Etale.restrictPresheaf E.obj U ≅ (Etale.continuousMapSheafType U.left S).obj :=
    (sheafToPresheaf _ _).mapIso
      (iS.symm ≪≫ Etale.constantSheafIsoContinuousMapSheafType U.left S)
  have : Finite S := Etale.finite_of_iso hfin U x α
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  let : TopologicalSpace (ULift.{u} (Fin n)) := ⊥
  have : DiscreteTopology (ULift.{u} (Fin n)) := ⟨rfl⟩
  exact ⟨ULift.{u} (Fin n), inferInstance, _,
    Etale.isUniversalSection_of_iso (eS.trans Equiv.ulift.symm) α⟩

/-- **A sheaf represented by a trivial cover is constant.** If the restriction of `E` to an étale
`T`-scheme `U` is represented by a trivial cover `∐_{S'} U ⟶ U`, then the restriction of `E` to
`U` is constant. -/
theorem Etale.isConstant_over_of_isUniversalSection (S' : Type u)
    {ξ : E.obj.obj (op (Etale.trivialCover U S'))}
    (h : IsUniversalSection E.obj U.hom (Etale.trivialCover U S')
      (Sigma.desc fun _ ↦ 𝟙 U.left) ξ) :
    (E.over U).IsConstant (T.smallEtaleTopology.over U) := by
  let : TopologicalSpace S' := ⊥
  have : DiscreteTopology S' := ⟨rfl⟩
  let : TopologicalSpace (ULift.{u + 1} S') := ⊥
  have : DiscreteTopology (ULift.{u + 1} S') := ⟨rfl⟩
  let α := Etale.isoOfIsUniversalSection (A := ULift.{u + 1} S') Equiv.ulift h
  let G := (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (E.over U)
  have : G.IsConstant U.left.smallEtaleTopology :=
    Sheaf.isConstant_of_iso _ ((fullyFaithfulSheafToPresheaf _ _).preimageIso (X := G)
      (Y := Etale.continuousMapSheafType U.left (ULift.{u + 1} S')) α ≪≫
      (Etale.constantSheafIsoContinuousMapSheafType U.left (ULift.{u + 1} S')).symm)
  exact (Sheaf.isConstant_sheafCongr_functor_iff (Etale.overEquiv U)
    CategoryTheory.Over.mkIdTerminal (E.over U)).1 this

end Main

end AlgebraicGeometry.Scheme
