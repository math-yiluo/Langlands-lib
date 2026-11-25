/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Constant
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback

/-!
# Finite étale trivialization of finite locally constant sheaves

Let `Λ` be a finite commutative ring and `L` a finite locally constant sheaf of `Λ`-modules on
the small étale site of a connected scheme `X`. Then there is a connected finite étale cover
`p : P ⟶ X` such that `p^* L` is the constant sheaf of a finite `Λ`-module
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_connectedSpace`, blueprint
`fin2-lem-lisse-trivialized-finite-etale`).

The underlying sheaf of sets of `L` is represented by a finite étale `X`-scheme `E`
(`AlgebraicGeometry.Scheme.FiniteEtale.toFLC`). A Galois object `A` of the Galois category of
finite étale `X`-schemes dominating `E`
(`CategoryTheory.PreGaloisCategory.exists_galois_representative`) splits `E`:
`E ×_X A ≅ ∐_{Hom(A, E)} A`
(`AlgebraicGeometry.Scheme.FiniteEtale.isPullback_sigmaDesc_of_isGalois`). Hence the pullback
of the sheaf of sets of `L` to `A` is the sheaf of sections of a trivial cover, a constant
sheaf (`AlgebraicGeometry.Scheme.uliftYonedaTrivialCoverIso`), and since `A` is connected the
pullback of `L` itself is constant
(`AlgebraicGeometry.Scheme.module_pullback_isConstant_of_set_pullback`). Over a Noetherian base
we apply this on each of the finitely many connected components
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory Opposite
open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

namespace FiniteEtale

variable {X : Scheme.{u}} [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- **A Galois object splits the objects it dominates.** Let `A` be a Galois object of the
category of finite étale `X`-schemes and `E` a finite étale `X`-scheme such that evaluation at
a point `a ∈ A_s` is a bijection `Hom(A, E) → E_s`. Then `E ×_X A ≅ ∐_{Hom(A, E)} A` over `A`,
the summand indexed by `f` mapping to `E` by `f`. On geometric fibres this is the bijection
`(f, a') ↦ (f(a'), a')`, as evaluation at every point `a'` of `A_s` is bijective (`Aut A` acts
transitively on `A_s`); the fibre functor reflects isomorphisms. -/
lemma isPullback_sigmaDesc_of_isGalois (A E : X.FiniteEtale) [IsGalois A] (a : (fiber s).obj A)
    (ha : Function.Bijective fun f : A ⟶ E ↦ (fiber s).map f a) :
    IsPullback (Sigma.desc fun f : (A ⟶ E) ↦ f.hom.left)
      (Sigma.desc fun _ : (A ⟶ E) ↦ 𝟙 A.obj.left) E.obj.hom A.obj.hom := by
  have : IsFinite A.obj.hom := A.property
  have : IsFinite E.obj.hom := E.property
  have hw : (Sigma.desc fun f : (A ⟶ E) ↦ f.hom.left) ≫ E.obj.hom =
      (Sigma.desc fun _ : (A ⟶ E) ↦ 𝟙 A.obj.left) ≫ A.obj.hom :=
    Sigma.hom_ext _ _ fun f ↦ by simp
  let φ := Limits.pullback.lift _ _ hw
  suffices IsIso φ from IsPullback.of_iso_pullback ⟨hw⟩ (asIso φ)
    (by simp [φ]) (by simp [φ])
  -- `∐ A` and `E ×_X A` as finite étale `X`-schemes, and `φ` as a morphism between them
  let a' : (∐ fun _ : (A ⟶ E) ↦ A.obj.left) ⟶ X := Sigma.desc fun _ ↦ A.obj.hom
  let b' : Limits.pullback E.obj.hom A.obj.hom ⟶ X := Limits.pullback.snd _ _ ≫ A.obj.hom
  have : Etale a' := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let C : X.FiniteEtale := ⟨Etale.mk a', inferInstanceAs (IsFinite a')⟩
  let B : X.FiniteEtale := ⟨Etale.mk b', inferInstanceAs (IsFinite b')⟩
  have hφ : φ ≫ b' = a' := Sigma.hom_ext _ _ fun f ↦ by simp [φ, a', b']
  let Φ : C ⟶ B := ObjectProperty.homMk (MorphismProperty.Over.homMk φ hφ)
  -- a geometric point of `A` gives an element of its geometric fibre
  let pt (x : Spec (.of Ω) ⟶ A.obj.left) (hx : x ≫ A.obj.hom = s) : (fiber s).obj A :=
    Over.homMk (V := (Etale.forget X).obj A.obj) x hx
  -- evaluation at any point of `A_s` is bijective
  have hev (x : (fiber s).obj A) : Function.Bijective fun f : A ⟶ E ↦ (fiber s).map f x := by
    obtain ⟨σ, rfl⟩ := evaluation_aut_surjective_of_isGalois (fiber s) A a x
    refine ⟨fun f g hfg ↦ evaluation_injective_of_isConnected (fiber s) A E _ hfg, fun e ↦ ?_⟩
    obtain ⟨g, hg⟩ := ha.2 e
    refine ⟨σ.asIso.inv ≫ g, ?_⟩
    simp only [Functor.map_comp, FintypeCat.comp_apply]
    rw [← FintypeCat.comp_apply ((fiber s).map σ.asIso.hom), ← Functor.map_comp, σ.asIso.hom_inv_id,
      CategoryTheory.Functor.map_id, FintypeCat.id_apply]
    exact hg
  have hΦ : IsIso ((fiber s).map Φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · have hxy' : x.left ≫ φ = y.left ≫ φ := congrArg (fun u ↦ u.left) hxy
      have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
      have : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
      obtain ⟨f, x', hx'⟩ := exists_comp_sigmaι_eq_of_subsingleton (X := Spec (.of Ω)) x.left
      obtain ⟨g, y', hy'⟩ := exists_comp_sigmaι_eq_of_subsingleton (X := Spec (.of Ω)) y.left
      rw [← hx', ← hy', Category.assoc, Category.assoc] at hxy'
      have h₁ := congrArg (· ≫ Limits.pullback.fst _ _) hxy'
      have h₂ := congrArg (· ≫ Limits.pullback.snd _ _) hxy'
      simp only [Category.assoc, φ, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Sigma.ι_comp_desc, Category.comp_id] at h₁ h₂
      subst h₂
      have hxs : x' ≫ A.obj.hom = s := by
        rw [← fiber_left_comp s x, ← hx', Category.assoc]
        exact congrArg (x' ≫ ·) (Sigma.ι_comp_desc (fun _ : (A ⟶ E) ↦ A.obj.hom) f).symm
      have hfg : f = g := by
        refine evaluation_injective_of_isConnected (fiber s) A E (pt x' hxs) ?_
        exact fiber_ext s h₁
      subst hfg
      exact fiber_ext s (hx'.symm.trans hy')
    · have h₂ : (z.left ≫ Limits.pullback.snd _ _) ≫ A.obj.hom = s := by
        rw [Category.assoc]
        exact fiber_left_comp s z
      have h₁ : (z.left ≫ Limits.pullback.fst _ _) ≫ E.obj.hom = s := by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact h₂
      let e : (fiber s).obj E := Over.homMk (V := (Etale.forget X).obj E.obj) _ h₁
      obtain ⟨f, hf⟩ := (hev (pt _ h₂)).2 e
      have hf' : (z.left ≫ Limits.pullback.snd _ _) ≫ f.hom.left =
          z.left ≫ Limits.pullback.fst _ _ :=
        congrArg (fun u ↦ u.left) hf
      have hC : ((z.left ≫ Limits.pullback.snd _ _) ≫
          Sigma.ι (fun _ : (A ⟶ E) ↦ A.obj.left) f) ≫ a' = s := by
        rw [Category.assoc]
        exact (congrArg _ (Sigma.ι_comp_desc _ _)).trans h₂
      refine ⟨Over.homMk (V := (Etale.forget X).obj C.obj) _ hC, fiber_ext s ?_⟩
      change ((z.left ≫ Limits.pullback.snd _ _) ≫
        Sigma.ι (fun _ : (A ⟶ E) ↦ A.obj.left) f) ≫ φ = z.left
      refine Limits.pullback.hom_ext ?_ ?_
      · simpa [φ] using hf'
      · simp [φ]
  have : IsIso Φ := isIso_of_reflects_iso Φ (fiber s)
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _ ⋙ Etale.forget X ⋙ Over.forget X).map Φ))

end FiniteEtale

section TrivialCover

variable {P : Scheme.{u}} (S : Type u)

/-- The trivial cover `∐_S P ⟶ P`, as an étale `P`-scheme. -/
abbrev Etale.trivialCoverSelf : P.Etale :=
  have : AlgebraicGeometry.Etale (Sigma.desc fun _ : S ↦ 𝟙 P) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  Etale.mk (Sigma.desc fun _ : S ↦ 𝟙 P)

/-- Morphisms of étale `P`-schemes into the trivial cover `∐_S P` are the locally constant
functions to `S` (`AlgebraicGeometry.Scheme.sigmaHomEquiv`). -/
def trivialCoverSelfHomEquiv [TopologicalSpace S] [DiscreteTopology S] (W : P.Etale) :
    ULift.{u + 1} (W ⟶ Etale.trivialCoverSelf S) ≃ C(W.left, ULift.{u + 1} S) :=
  Equiv.ulift.trans
    ((show (W ⟶ Etale.trivialCoverSelf S) ≃
        {a : W.left ⟶ ∐ fun _ : S ↦ P // a ≫ Sigma.desc (fun _ ↦ 𝟙 P) = W.hom} from
      { toFun f := ⟨f.left, MorphismProperty.Over.w f⟩
        invFun a := MorphismProperty.Over.homMk a.1 a.2
        left_inv _ := rfl
        right_inv _ := rfl }).trans (sigmaHomEquiv Equiv.ulift W.hom).symm)

lemma trivialCoverSelfHomEquiv_naturality [TopologicalSpace S] [DiscreteTopology S]
    {W₁ W₂ : P.Etale} (g : W₂ ⟶ W₁) (f : W₁ ⟶ Etale.trivialCoverSelf S) :
    trivialCoverSelfHomEquiv S W₂ ⟨g ≫ f⟩ =
      (trivialCoverSelfHomEquiv S W₁ ⟨f⟩).comp g.left.base.hom := by
  apply (sigmaHomEquiv Equiv.ulift W₂.hom).injective
  apply Subtype.ext
  change ((sigmaHomEquiv Equiv.ulift W₂.hom) ((sigmaHomEquiv Equiv.ulift W₂.hom).symm
      ⟨(g ≫ f).left, MorphismProperty.Over.w (g ≫ f)⟩)).1 =
    (sigmaHomEquiv Equiv.ulift W₂.hom (((sigmaHomEquiv Equiv.ulift W₁.hom).symm
      ⟨f.left, MorphismProperty.Over.w f⟩).comp g.left.base.hom)).1
  have h := sigmaHomEquiv_comp' Equiv.ulift g.left W₁.hom (MorphismProperty.Over.w g)
    ((sigmaHomEquiv Equiv.ulift W₁.hom).symm ⟨f.left, MorphismProperty.Over.w f⟩)
  have h₁ := congrArg Subtype.val ((sigmaHomEquiv Equiv.ulift W₁.hom).apply_symm_apply
    ⟨f.left, MorphismProperty.Over.w f⟩)
  have h₂ := congrArg Subtype.val ((sigmaHomEquiv Equiv.ulift W₂.hom).apply_symm_apply
    ⟨(g ≫ f).left, MorphismProperty.Over.w (g ≫ f)⟩)
  refine h₂.trans (Eq.trans ?_ h.symm)
  exact (congrArg (g.left ≫ ·) h₁).symm

/-- **The sheaf of sections of a trivial cover is constant.** The sections over `W` of the
trivial cover `∐_S P ⟶ P` are the locally constant functions `W → S`
(`AlgebraicGeometry.Scheme.sigmaHomEquiv`), i.e. the sections of the constant sheaf. -/
def uliftYonedaTrivialCoverIso :
    P.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.trivialCoverSelf S) ≅
      (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj (ULift.{u + 1} S) :=
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := P.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.trivialCoverSelf S))
      (Y := Etale.continuousMapSheafType P (ULift.{u + 1} S))
      (NatIso.ofComponents (fun W ↦ (trivialCoverSelfHomEquiv S W.unop).toIso)
        fun g ↦ by
          ext f
          exact trivialCoverSelfHomEquiv_naturality S g.unop f.down) ≪≫
    (Etale.constantSheafIsoContinuousMapSheafType P (ULift.{u + 1} S)).symm

end TrivialCover

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The sheaf of sets underlying a finite locally constant sheaf of `Λ`-modules, `Λ` finite, is
finite locally constant. -/
lemma IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes_sheafForget
    {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hF : IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheafOfTypes ((sheafForget Y.smallEtaleTopology).obj F) := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (F.over _)).IsConstant _)
  · have hfg := hF.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s
    have : Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) :=
      ConcreteCategory.FiniteOfIsFinitelyGenerated.finite_of_isFinitelyGenerated
        (C := ModuleCat.{u + 1} Λ) _ hfg
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this e.symm.toEquiv

/-- Blueprint `fin2-lem-lisse-trivialized-finite-etale`: Finite etale trivialization of a lisse
sheaf, connected case.

Let `X` be a connected scheme, `Λ` a finite commutative ring and `L` a finite locally constant
sheaf of `Λ`-modules on `X_ét`. There is a finite étale surjective morphism `p : P ⟶ X` with `P`
connected such that `p^* L` is the constant sheaf of a finite `Λ`-module `M`. -/
theorem exists_isConstant_upperStar_of_connectedSpace {X : Scheme.{u}} [ConnectedSpace X]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf L] :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ AlgebraicGeometry.Etale p ∧ Surjective p ∧
      ConnectedSpace P ∧ ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((p)^*[ModuleCat.{u + 1} Λ].obj L ≅
          (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  -- the underlying sheaf of sets of `L` is represented by a finite étale `E`
  let L₀ := (sheafForget X.smallEtaleTopology).obj L
  have hL₀ := IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes_sheafForget L
  obtain ⟨E, ⟨eE⟩⟩ := Functor.EssSurj.mem_essImage (F := FiniteEtale.toFLC X) ⟨L₀, hL₀⟩
  -- a Galois object dominating `E`
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let s : Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
      (AlgebraicClosure (X.residueField x)))) ≫ X.fromSpecResidueField x
  obtain ⟨A, a, hgal, ha⟩ := exists_galois_representative (FiniteEtale.fiber s) E
  have : IsFinite A.obj.hom := A.property
  have : ConnectedSpace A.obj.left := FiniteEtale.connectedSpace_of_isConnected A
  let p : A.obj.left ⟶ X := A.obj.hom
  have hsurj : Surjective p := by
    have : AlgebraicGeometry.Etale p := A.obj.prop
    have hc : IsClopen (Set.range p) := ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
    obtain ⟨y⟩ := (inferInstance : Nonempty A.obj.left)
    exact ⟨Set.range_eq_univ.1 (hc.eq_univ ⟨_, y, rfl⟩)⟩
  refine ⟨A.obj.left, p, inferInstance, A.obj.prop, hsurj, inferInstance, ?_⟩
  -- the pullback of `L₀` to `A` is the sheaf of sections of a trivial cover
  have hpb := FiniteEtale.isPullback_sigmaDesc_of_isGalois s A E a ha
  let T : A.obj.left.FiniteEtale :=
    ⟨Etale.trivialCoverSelf (A ⟶ E), inferInstanceAs (IsFinite (Sigma.desc fun _ ↦ _))⟩
  let eT : (FiniteEtale.pullback p).obj E ≅ T :=
    FiniteEtale.isoPullbackOfIsPullback p T E _ hpb
  have hc : ((etaleSetPullback p).obj L₀).IsConstant A.obj.left.smallEtaleTopology := by
    refine Sheaf.isConstant_of_iso _ (((etaleSetPullback p).mapIso
      ((ObjectProperty.ι _).mapIso eE.symm)) ≪≫ (FiniteEtale.toFLCPullbackIso p).app E ≪≫
        (FiniteEtale.toFLC _ ⋙ ObjectProperty.ι _).mapIso eT ≪≫
          uliftYonedaTrivialCoverIso (A ⟶ E))
  have := module_pullback_isConstant_of_set_pullback Λ p L hc
  obtain ⟨M, ⟨eM⟩⟩ := Sheaf.mem_essImage_of_isConstant _ ((p)^*[ModuleCat.{u + 1} Λ].obj L)
  refine ⟨M, ?_, ⟨eM.symm⟩⟩
  have : IsFiniteSheaf ((p)^*[ModuleCat.{u + 1} Λ].obj L) := IsFiniteSheaf.upperStar p L
  have : IsFiniteSheaf ((constantSheaf A.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj M) := IsFiniteSheaf.of_iso eM.symm
  have : Nonempty A.obj.left := inferInstance
  have := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := A.obj.left) M
  exact Module.finite_of_finite Λ


/-- Blueprint `fin2-lem-lisse-trivialized-finite-etale`: Finite etale trivialization of a lisse
sheaf.

Let `X` be a Noetherian scheme (for instance of finite type over a field), `Λ` a finite
commutative ring and `L` a finite locally constant sheaf of `Λ`-modules on `X_ét`. There are
finitely many connected schemes `P_a` with finite étale morphisms `p_a : P_a ⟶ X`, jointly
surjective, such that each `p_a^* L` is the constant sheaf of a finite `Λ`-module `M_a`. In
other words `p : P = ∐ P_a ⟶ X` is finite étale surjective and `p^* L` is constant with finite
value on each connected component of `P`. If `X` is connected, a single connected `P` suffices
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_connectedSpace`); in general we apply
that to the finitely many connected components of `X`, which are open and closed. -/
theorem exists_isConstant_upperStar {X : Scheme.{u}} [IsNoetherian X]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf L] :
    ∃ (n : ℕ) (P : Fin n → Scheme.{u}) (p : ∀ a, P a ⟶ X),
      (∀ a, IsFinite (p a) ∧ AlgebraicGeometry.Etale (p a) ∧ ConnectedSpace (P a)) ∧
      (∀ x : X, ∃ a, x ∈ Set.range (p a).base) ∧
      ∀ a, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((p a)^*[ModuleCat.{u + 1} Λ].obj L ≅
          (constantSheaf (P a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  -- the connected components of `X`
  let e := (Finite.equivFin (ConnectedComponents X)).symm
  let U (a : Fin (Nat.card (ConnectedComponents X))) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {e a},
      ((isClopen_discrete {e a}).preimage ConnectedComponents.continuous_coe).isOpen⟩
  have hU (a : Fin (Nat.card (ConnectedComponents X))) : IsClopen (U a : Set X) :=
    (isClopen_discrete {e a}).preimage ConnectedComponents.continuous_coe
  have hUc (a : Fin (Nat.card (ConnectedComponents X))) : ConnectedSpace (U a) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e a)
    have hUx : (U a : Set X) = connectedComponent x := by
      simp [U, ← hx, connectedComponents_preimage_singleton]
    exact isConnected_iff_connectedSpace.1 (hUx ▸ isConnected_connectedComponent)
  have (a : Fin (Nat.card (ConnectedComponents X))) :
      IsFiniteLocallyConstantSheaf (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj L) :=
    IsFiniteLocallyConstantSheaf.upperStar _ L
  choose P q hq hqe hqs hP M hM eM using fun a ↦
    exists_isConstant_upperStar_of_connectedSpace (X := U a) (((U a).ι)^*[_].obj L)
  refine ⟨_, P, fun a ↦ q a ≫ (U a).ι, fun a ↦ ?_, fun x ↦ ?_, fun a ↦ ⟨M a, hM a, ?_⟩⟩
  · have : IsClosedImmersion (U a).ι :=
      IsClosedImmersion.of_isOpenImmersion (U a).ι (by simpa using (hU a).isClosed)
    have := hq a
    have := hqe a
    exact ⟨inferInstance, inferInstance, hP a⟩
  · let a := e.symm (ConnectedComponents.mk x)
    have hx : x ∈ U a := by simp [U, a]
    obtain ⟨y, hy⟩ := (hqs a).surj ⟨x, hx⟩
    exact ⟨a, y, by simp [hy]⟩
  · exact ⟨(Etale.upperStarComp (ModuleCat.{u + 1} Λ) (q a) (U a).ι).app L ≪≫ (eM a).some⟩

end AlgebraicGeometry.Scheme

end
