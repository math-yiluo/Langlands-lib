/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology of an open and closed subscheme

Let `U` be an open subscheme of a scheme `X` which is also closed. Restriction of abelian sheaves
to `U` is left adjoint to the pushforward along the inclusion `U ⟶ X`, and both functors are
exact: restriction always is, and the pushforward is because `U` is also closed. Hence the
`Ext`-adjunction identifies `H^n(X, (U.ι)_* N) ≅ H^n(U, N)` for every `𝒪_U`-module `N`.

If `X` is the disjoint union of finitely many open subschemes `U i`, each of them is open and
closed, and an `𝒪_X`-module `M` is the biproduct of the pushforwards of its restrictions to the
`U i`. Together, these show that the cohomology of `M` is the direct sum of the cohomologies of
its restrictions (`AlgebraicGeometry.Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint`).

## Main definitions

- `AlgebraicGeometry.Scheme.Opens.sheafRestrict`, `AlgebraicGeometry.Scheme.Opens.sheafPushforward`:
  restriction of abelian sheaves to an open subscheme `U`, and pushforward along `U.ι`.
- `AlgebraicGeometry.Scheme.Modules.H.pushforwardιLinearEquiv`: for `U` open and closed,
  `H^n(X, (U.ι)_* N) ≃ H^n(U, N)` as `k`-vector spaces.

## Main statements

- `AlgebraicGeometry.Scheme.Opens.preservesFiniteColimits_sheafPushforward`: the pushforward of
  abelian sheaves along the inclusion of an open and closed subscheme is exact.
- `AlgebraicGeometry.Scheme.Modules.finrankH_pushforward_ι`: `h^n(X, (U.ι)_* N) = h^n(U, N)`.
- `AlgebraicGeometry.Scheme.Modules.isIso_biproduct_lift_restrictAdjunction_unit`: an
  `𝒪_X`-module is the biproduct of the pushforwards of its restrictions to the pieces of a
  finite disjoint open cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Function Abelian

namespace AlgebraicGeometry.Scheme

namespace Opens

variable {X : Scheme.{u}} (U : X.Opens)

/-- The restriction of abelian sheaves on `X` to an open subscheme `U`. -/
noncomputable abbrev sheafRestrict : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u} :=
  U.ι.opensFunctor.sheafPushforwardContinuous _ _ _

/-- The pushforward of abelian sheaves on an open subscheme `U` along the inclusion `U ⟶ X`. -/
noncomputable abbrev sheafPushforward :
    Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (Opens.map U.ι.base).sheafPushforwardContinuous _ _ _

/-- Restriction of abelian sheaves to an open subscheme is left adjoint to the pushforward. -/
noncomputable def sheafRestrictAdjunction : U.sheafRestrict ⊣ U.sheafPushforward :=
  U.ι.opensFunctorAdjunction.sheafPushforwardContinuous _ _

instance : PreservesFiniteColimits U.sheafRestrict :=
  U.sheafRestrictAdjunction.leftAdjoint_preservesColimits.{0, 0}.preservesFiniteColimits

instance : U.sheafRestrict.Additive := Functor.additive_of_preserves_binary_products _

instance : U.sheafPushforward.Additive := Functor.additive_of_preserves_binary_products _

/-- The restriction of a constant sheaf to an open subscheme is constant: both
`constantSheaf ⋙ U.sheafRestrict` and `constantSheaf` are left adjoint to taking sections over
`U`. -/
noncomputable def sheafRestrictConstantSheafIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙ U.sheafRestrict ≅
      constantSheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u} :=
  (((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).comp
    U.sheafRestrictAdjunction).ofNatIsoRight (Iso.refl _)).leftAdjointUniq
    (constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop)

/-- If `U` is also closed, the pushforward of abelian sheaves along `U ⟶ X` preserves
epimorphisms: a section over `W` is locally liftable near the points of `W ∩ U` because the
original epimorphism is locally surjective, and near the points of `W \ U` because the sections
over `W \ U` of a pushforward vanish. -/
theorem preservesEpimorphisms_sheafPushforward (hU : IsClosed (U : Set X)) :
    U.sheafPushforward.PreservesEpimorphisms := by
  constructor
  intro A B f hf
  rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
  replace hf := (TopCat.Presheaf.isLocallySurjective_iff f.hom).1 (by exact hf)
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun W t x hx ↦ ?_
  by_cases hxU : x ∈ U
  · obtain ⟨O, hOW, ⟨s, hs⟩, hxO⟩ := hf ((Opens.map U.ι.base).obj W) t ⟨x, hxU⟩ hx
    have hO : (Opens.map U.ι.base).obj (U.ι ''ᵁ O) ≤ O := (U.ι.preimage_image_eq O).le
    refine ⟨U.ι ''ᵁ O, ?_, ⟨A.obj.map (homOfLE hO).op s, ?_⟩, ⟨⟨x, hxU⟩, hxO, rfl⟩⟩
    · exact (U.ι.image_mono hOW).trans (U.ι.image_preimage_le W)
    · change f.hom.app _ (A.obj.map _ s) = B.obj.map _ t
      rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply, hs]
      change B.obj.map _ (B.obj.map _ t) = _
      erw [← ConcreteCategory.comp_apply, ← B.obj.map_comp]
      rfl
  · refine ⟨W ⊓ ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩, inf_le_left, ⟨0, ?_⟩, ⟨hx, hxU⟩⟩
    have h : (Opens.map U.ι.base).obj (W ⊓ ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩) = ⊥ :=
      eq_bot_iff.2 fun y hy ↦ (hy.2 y.2).elim
    have := AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty B h).isZero
    exact @Subsingleton.elim _ this _ _

/-- If `U` is also closed, the pushforward of abelian sheaves along `U ⟶ X` is exact. -/
theorem preservesFiniteColimits_sheafPushforward (hU : IsClosed (U : Set X)) :
    PreservesFiniteColimits U.sheafPushforward := by
  have := U.preservesEpimorphisms_sheafPushforward hU
  have := Functor.preservesHomology_of_preservesEpis_and_kernels U.sheafPushforward
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- The isomorphism `AlgebraicGeometry.Scheme.Opens.sheafHPushforwardAddEquiv` for `F = (U.ι)_* N`
itself. -/
noncomputable def sheafHPushforwardAddEquivAux (hU : IsClosed (U : Set X))
    (N : Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H (U.sheafPushforward.obj N) n ≃+ Sheaf.H N n :=
  have := U.preservesFiniteColimits_sheafPushforward hU
  (U.sheafRestrictAdjunction.extAddEquiv _ N n).trans
    (Ext.precompAddEquiv (U.sheafRestrictConstantSheafIso.app _).symm N n)

lemma sheafHPushforwardAddEquivAux_map (hU : IsClosed (U : Set X))
    {N N' : Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u}} (g : N ⟶ N')
    (n : ℕ) (x : Sheaf.H (U.sheafPushforward.obj N) n) :
    U.sheafHPushforwardAddEquivAux hU N' n (Sheaf.H.map (U.sheafPushforward.map g) n x) =
      Sheaf.H.map g n (U.sheafHPushforwardAddEquivAux hU N n x) := by
  change (Ext.mk₀ (U.sheafRestrictConstantSheafIso.app _).inv).comp
      (U.sheafRestrictAdjunction.mapExtCounit _ N' n _) (zero_add n) =
    Sheaf.H.map g n ((Ext.mk₀ (U.sheafRestrictConstantSheafIso.app _).inv).comp
      (U.sheafRestrictAdjunction.mapExtCounit _ N n x) (zero_add n))
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Adjunction.mapExtCounit_comp_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

/-- If `U` is also closed, `H^n(X, (U.ι)_* N) ≅ H^n(U, N)` for every abelian sheaf `N` on `U`: this
is the `Ext`-adjunction `CategoryTheory.Adjunction.extAddEquiv` for the exact functors
`U.sheafRestrict ⊣ U.sheafPushforward`, together with the identification of the restriction of
the constant sheaf `ℤ`. For flexibility, the source is any sheaf `F` with an isomorphism
`α : F ≅ (U.ι)_* N`. -/
noncomputable def sheafHPushforwardAddEquiv (hU : IsClosed (U : Set X))
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {N : Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u}}
    (α : F ≅ U.sheafPushforward.obj N) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H N n :=
  ({ toFun := Sheaf.H.map α.hom n
     invFun := Sheaf.H.map α.inv n
     left_inv x := by rw [← Sheaf.H.map_comp_apply, α.hom_inv_id, Sheaf.H.map_id_apply]
     right_inv y := by rw [← Sheaf.H.map_comp_apply, α.inv_hom_id, Sheaf.H.map_id_apply]
     map_add' := map_add _ } : Sheaf.H F n ≃+ Sheaf.H (U.sheafPushforward.obj N) n).trans
    (U.sheafHPushforwardAddEquivAux hU N n)

/-- The isomorphism `AlgebraicGeometry.Scheme.Opens.sheafHPushforwardAddEquiv` is natural. -/
lemma sheafHPushforwardAddEquiv_map (hU : IsClosed (U : Set X))
    {F F' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {N N' : Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u}}
    (α : F ≅ U.sheafPushforward.obj N) (α' : F' ≅ U.sheafPushforward.obj N') (φ : F ⟶ F')
    (g : N ⟶ N') (h : φ ≫ α'.hom = α.hom ≫ U.sheafPushforward.map g) (n : ℕ)
    (x : Sheaf.H F n) :
    U.sheafHPushforwardAddEquiv hU α' n (Sheaf.H.map φ n x) =
      Sheaf.H.map g n (U.sheafHPushforwardAddEquiv hU α n x) := by
  change U.sheafHPushforwardAddEquivAux hU N' n (Sheaf.H.map α'.hom n (Sheaf.H.map φ n x)) =
    Sheaf.H.map g n (U.sheafHPushforwardAddEquivAux hU N n (Sheaf.H.map α.hom n x))
  rw [← Sheaf.H.map_comp_apply, h, Sheaf.H.map_comp_apply, sheafHPushforwardAddEquivAux_map]

end Opens

namespace Modules

variable {X : Scheme.{u}}

section Pushforward

variable (U : X.Opens)

/-- Multiplication by a global function `a` on the pushforward of `N` along the inclusion of an
open subscheme `U` is the pushforward of multiplication by the restriction of `a` to `U`. -/
lemma smulHom_pushforward_ι (N : U.toScheme.Modules) (a : Γ(X, ⊤)) :
    ((pushforward U.ι).obj N).smulHom a = (pushforward U.ι).map (N.smulHom (U.ι.appTop a)) := by
  ext W x
  change (U.ι.app W (X.presheaf.map (homOfLE le_top).op a)) • (show Γ(N, U.ι ⁻¹ᵁ W) from x) =
    U.toScheme.presheaf.map (homOfLE (le_top (a := U.ι ⁻¹ᵁ W))).op (U.ι.appTop a) •
      (show Γ(N, U.ι ⁻¹ᵁ W) from x)
  congr 1
  rw [← CategoryTheory.comp_apply, U.ι.naturality]
  rfl

variable (hU : IsClosed (U : Set X))

/-- If `U` is an open and closed subscheme of `X`, then `H^n(X, (U.ι)_* N) ≅ H^n(U, N)` for every
`𝒪_U`-module `N`, by `AlgebraicGeometry.Scheme.Opens.sheafHPushforwardAddEquiv`. -/
noncomputable def H.pushforwardιAddEquiv (N : U.toScheme.Modules) (n : ℕ) :
    ((pushforward U.ι).obj N).H n ≃+ N.H n :=
  (U.sheafHPushforwardAddEquiv hU (N := (SheafOfModules.toSheaf _).obj N)
    (Iso.refl _ : (SheafOfModules.toSheaf _).obj ((pushforward U.ι).obj N) ≅
      U.sheafPushforward.obj ((SheafOfModules.toSheaf _).obj N)) n :
    Sheaf.H ((SheafOfModules.toSheaf _).obj ((pushforward U.ι).obj N)) n ≃+
      Sheaf.H ((SheafOfModules.toSheaf _).obj N) n)

/-- The isomorphism `AlgebraicGeometry.Scheme.Modules.H.pushforwardιAddEquiv` is compatible with
multiplication by global functions. -/
lemma H.pushforwardιAddEquiv_map_smulHom (N : U.toScheme.Modules) (n : ℕ) (a : Γ(X, ⊤))
    (x : ((pushforward U.ι).obj N).H n) :
    H.pushforwardιAddEquiv U hU N n (H.map (((pushforward U.ι).obj N).smulHom a) n x) =
      H.map (N.smulHom (U.ι.appTop a)) n (H.pushforwardιAddEquiv U hU N n x) := by
  rw [smulHom_pushforward_ι]
  exact U.sheafHPushforwardAddEquiv_map hU _ _ _ _
    ((Category.comp_id _).trans (Category.id_comp _).symm) n x

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **Cohomology of an open and closed subscheme.** If `U` is an open and closed subscheme of a
`k`-scheme `X`, then `H^n(X, (U.ι)_* N) ≅ H^n(U, N)` as `k`-vector spaces, for every
`𝒪_U`-module `N`. Here `U` is a `k`-scheme through `X`. -/
noncomputable def H.pushforwardιLinearEquiv (N : U.toScheme.Modules) (n : ℕ) :
    letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ X ↘ Spec (.of k)⟩
    ((pushforward U.ι).obj N).H n ≃ₗ[k] N.H n :=
  letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ X ↘ Spec (.of k)⟩
  { H.pushforwardιAddEquiv U hU N n with
    map_smul' c x := by
      have hc : globalSectionsRingHom k (X := U.toScheme) c =
          U.ι.appTop (globalSectionsRingHom k c) := by
        change ((ΓSpecIso _).inv ≫ (U.ι ≫ X ↘ Spec (.of k)).appTop).hom c =
          U.ι.appTop (((ΓSpecIso _).inv ≫ (X ↘ Spec (.of k)).appTop).hom c)
        rw [Scheme.Hom.comp_appTop]
        rfl
      change H.pushforwardιAddEquiv U hU N n
          (H.map (((pushforward U.ι).obj N).smulHom (globalSectionsRingHom k c)) n x) =
        H.map (N.smulHom (globalSectionsRingHom k (X := U.toScheme) c)) n
          (H.pushforwardιAddEquiv U hU N n x)
      rw [hc]
      exact H.pushforwardιAddEquiv_map_smulHom U hU N n _ x }

include hU in
/-- If `U` is an open and closed subscheme of a `k`-scheme `X`, then
`h^n(X, (U.ι)_* N) = h^n(U, N)` for every `𝒪_U`-module `N`. -/
theorem finrankH_pushforward_ι (N : U.toScheme.Modules) (n : ℕ) :
    ((pushforward U.ι).obj N).finrankH k n =
      letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ X ↘ Spec (.of k)⟩
      N.finrankH k n :=
  (H.pushforwardιLinearEquiv U hU k N n).finrank_eq

end Pushforward

section Decomposition

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **A module on a finite disjoint union is the direct sum of its restrictions.** If `X` is the
disjoint union of finitely many open subschemes `U i`, then every `𝒪_X`-module `M` is the
biproduct of the pushforwards of its restrictions to the `U i`, via the units of the adjunctions
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. Over an open `W` this is the sheaf
condition for the disjoint cover of `W` by the `W ∩ U i`. -/
theorem isIso_biproduct_lift_restrictAdjunction_unit {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤) (M : X.Modules) :
    IsIso (biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app M) := by
  let G : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafToPresheaf _ AddCommGrpCat.{u}
  suffices ∀ W, IsIso ((G.map (biproduct.lift fun i ↦
      (restrictAdjunction (U i).ι).unit.app M)).app W) by
    have := NatIso.isIso_of_isIso_app (G.map (biproduct.lift fun i ↦
      (restrictAdjunction (U i).ι).unit.app M))
    have : G.ReflectsIsomorphisms := inferInstanceAs
      (SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
    exact isIso_of_reflects_iso _ G
  rintro ⟨W⟩
  let E : X.Modules ⥤ AddCommGrpCat.{u} := G ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op W)
  have : E.Additive := inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf _) ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op W)).Additive
  change IsIso (E.map _)
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let V (i : ι) : X.Opens := (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W)
  have hVU (i : ι) : V i = U i ⊓ W := by
    simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hVW (i : ι) : V i ≤ W := (U i).ι.image_preimage_le W
  have hV : W ≤ iSup V := fun x hx ↦ by
    have hx' : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact Opens.mem_iSup.mpr ⟨i, by rw [hVU]; exact ⟨hi, hx⟩⟩
  let ψ : E.obj M ⟶ AddCommGrpCat.of ((i : ι) → Γ(M, V i)) :=
    AddCommGrpCat.ofHom (AddMonoidHom.pi fun i ↦ (F.1.map (homOfLE (hVW i)).op).hom)
  have hψ : Function.Bijective ψ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
    · refine F.eq_of_locally_eq' V W (fun i ↦ homOfLE (hVW i)) hV x 0 fun i ↦ ?_
      rw [map_zero]
      exact congrFun hx i
    · obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' V W (fun i ↦ homOfLE (hVW i)) hV y
        fun i j ↦ by
          by_cases hij : i = j
          · subst hij
            rfl
          · have h : V i ⊓ V j = ⊥ := by
              rw [hVU, hVU]
              exact eq_bot_iff.2 fun x hx ↦ (Opens.coe_disjoint.mpr (hU hij)).le_bot
                ⟨hx.1.1, hx.2.1⟩
            have := AddCommGrpCat.subsingleton_of_isZero
              (TopCat.Sheaf.isTerminalOfEqEmpty F h).isZero
            exact Subsingleton.elim _ _
      exact ⟨s, funext hs⟩
  have : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).2 hψ
  have hlift : ψ ≫ (AddCommGrpCat.biproductIsoPi fun i ↦ E.obj
      ((pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M))).inv =
      biproduct.lift fun i ↦ E.map ((restrictAdjunction (U i).ι).unit.app M) := by
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    erw [Category.assoc, AddCommGrpCat.biproductIsoPi_inv_comp_π, biproduct.lift_π]
    rfl
  have : IsIso (E.map (biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app M) ≫
      (E.mapBiproduct _).hom) := by
    rw [biproduct.map_lift_mapBiprod, ← hlift]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_inv _)
  exact IsIso.of_isIso_comp_right _ (E.mapBiproduct _).hom

end Decomposition

end Modules

end AlgebraicGeometry.Scheme
