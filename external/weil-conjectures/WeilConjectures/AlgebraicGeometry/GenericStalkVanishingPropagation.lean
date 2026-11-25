/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Propagation of generic vanishing into a local system -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Generic vanishing of a map into a local system propagates to every geometric stalk.
Source: Stacks Project, Tag 09BG (3), and the etale-local constant-section argument
in Tag 09BH (3) (https://stacks.math.columbia.edu/tag/09BG and
https://stacks.math.columbia.edu/tag/09BH).
(blueprint: lem-weil-pbc-generic-all-stalks).

Proof: Fix a geometric point s and an element a of the stalk of F there. Suppose
its image b in the stalk of G is nonzero. Lift s to a member V of an etale cover
trivializing G. Such a lift exists because the cover is surjective and a nonempty
etale fibre over a separably closed field has a rational point. Pullback identifies
the stalks at the lifted point with those at s. Write the target on V as the
constant sheaf associated to a module M. Its stalk is canonically M, so b corresponds
to an element m different from zero.

Represent a on a pointed etale neighbourhood W of the lifted point. Equality of
its image germ with the germ of the constant section m is witnessed on a further
pointed neighbourhood, by the filtered-colimit description of stalks. Replace W by
this refinement; its image section in the constant target is now constantly m.
The composite W to X is etale, so its image is open. W is nonempty because it has
the chosen geometric point. The generic point eta lies in every nonempty open of X,
so there is a point w of W over eta. Compose the geometric point obtained from an
algebraic closure of the residue field at w with W to X. This gives a geometric
point t of X over eta, in the same universe as X.

At this new pointed neighbourhood, the image of the representing section has germ m,
which is nonzero by the constant-sheaf stalk formula and compatibility of stalks
with pullback. But hφ makes the map at t zero, a contradiction. Thus every a maps
to zero at every s, and extensionality of module homomorphisms proves the conclusion.
This is automatic for a zero source, target, or coefficient ring. The hypotheses
exclude the empty scheme. The argument uses neither finite generation nor any
Noetherian hypothesis. -/
theorem all_sheafFiber_map_eq_zero_of_generic
    {X : Scheme.{u}} [IrreducibleSpace X] {Λ : Type (u + 1)} [CommRing Λ]
    (η : X) (hη : IsGenericPoint η Set.univ)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsLocallyConstantSheaf G] (φ : F ⟶ G)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s (IsLocalRing.closedPoint Ω) = η →
        (pointSmallEtale s).sheafFiber.map φ = 0) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      (pointSmallEtale s).sheafFiber.map φ = 0 := open Limits Opposite in by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hconst_zero {N : ModuleCat.{u + 1} Λ} {W : X.Etale} [Nonempty W.left]
      (n : N)
      (h : (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W) n = 0) : n = 0 := by
    have := (X.smallEtaleTopology.W_toSheafify
      ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallyInjective
    have hmem := Presheaf.equalizerSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) n 0
      (h.trans (map_zero _).symm)
    by_contra hn
    have hbot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
      refine X.smallEtaleTopology.superset_covering ?_ hmem
      intro V g hg
      exact hn hg
    obtain ⟨V, g, hg, -⟩ := (mem_smallEtaleTopology_iff _).1 hbot
      (Classical.arbitrary W.left)
    exact hg
  have hzero_near {W : X.Etale} (a : F.obj.obj (op W)) (w : W.left)
      (hw : W.hom w = η) :
      ∃ (W' : X.Etale) (g : W' ⟶ W), Nonempty W'.left ∧
        G.obj.map g.op (φ.hom.app (op W) a) = 0 := by
    let s' := W.left.algClosurePoint w
    let t := s' ≫ W.hom
    let Φ := pointSmallEtale t
    let x : Φ.fiber.obj W := Over.homMk s' rfl
    have ht : t (IsLocalRing.closedPoint _) = η := by
      change W.hom (s' (IsLocalRing.closedPoint _)) = η
      rw [W.left.algClosurePoint_base]
      exact hw
    have h0 : Φ.toPresheafFiber W x G.obj (φ.hom.app (op W) a) =
        Φ.toPresheafFiber W x G.obj 0 := by
      rw [map_zero]
      have hnat := ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality φ.hom W x) a
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
      rw [← hnat]
      exact ConcreteCategory.congr_hom (hφ _ t ht) (Φ.toPresheafFiber W x F.obj a)
    obtain ⟨W', g, y, -, hy⟩ := (Φ.toPresheafFiber_eq_iff' W x _ _).1 h0
    exact ⟨W', g, ⟨y.left (IsLocalRing.closedPoint _)⟩, by simpa using hy⟩
  have hzero : φ = 0 := by
    obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
      (LinearMap.ext fun a ↦ ?_)))
    induction V using Opposite.rec with | op V => ?_
    change φ.hom.app (op V) a = 0
    set b := φ.hom.app (op V) a
    -- the sieve of étale `V`-schemes on which `b` vanishes covers `V`
    let S : Sieve V :=
      { arrows W g := G.obj.map g.op b = 0
        downward_closed {W W'} g hg g' := by
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg, map_zero] }
    refine Sheaf.isSeparated G V S ?_ b 0 fun W g hg ↦ by rw [map_zero]; exact hg
    rw [mem_smallEtaleTopology_iff]
    intro v
    -- a member `Uᵢ` of the trivialising cover through the image of `v`
    obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (V.hom v)
    set Ui := 𝒰.etalePrecoverageToEtale i
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    have : Etale V.hom := V.prop
    let W₁ : X.Etale := Scheme.Etale.mk (pullback.fst V.hom (𝒰.f i) ≫ V.hom)
    let g₁ : W₁ ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom (𝒰.f i))
    let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd V.hom (𝒰.f i))
      pullback.condition.symm
    obtain ⟨w₁, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback v u hu.symm
    -- `G` is constant over `Uᵢ`
    have := hc i
    obtain ⟨N, ⟨e₀⟩⟩ := (G.over Ui).mem_essImage_of_isConstant (J := X.smallEtaleTopology.over Ui)
    let e : G.over Ui ≅ ((constantSheaf X.smallEtaleTopology _).obj N).over Ui :=
      e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology _ Ui N
    set NX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
    have hnat {W W'' : Over Ui} (k : W'' ⟶ W) (y : ToType (G.obj.obj (op W.left))) :
        e.hom.hom.app (op W'') (G.obj.map k.left.op y) =
          NX.obj.map k.left.op (e.hom.hom.app (op W) y) :=
      ConcreteCategory.congr_hom (e.hom.hom.naturality k.op) y
    let W₁' : Over Ui := Over.mk h₁
    let c : ToType (NX.obj.obj (op W₁)) := e.hom.hom.app (op W₁') (G.obj.map g₁.op b)
    -- `c` is locally constant
    have hsurj := (X.smallEtaleTopology.W_toSheafify
      ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallySurjective
    obtain ⟨W₂, g₂, ⟨n, hn⟩, w₂, hw₂⟩ := (mem_smallEtaleTopology_iff _).1
      (Presheaf.imageSieve_mem X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) c) w₁
    have : Nonempty W₂.left := ⟨w₂⟩
    -- the constant `n` vanishes, by looking near a point over `η`
    have hn0 : n = 0 := by
      have hopen : IsOpen (Set.range W₂.hom) := W₂.hom.isOpenMap.isOpen_range
      obtain ⟨w, hw⟩ := (hη.mem_open_set_iff hopen).2
        ⟨W₂.hom w₂, Set.mem_univ _, Set.mem_range_self _⟩
      obtain ⟨W₃, g₃, hW₃, h₃⟩ := hzero_near
        (F.obj.map (g₂ ≫ g₁).op a) w hw
      have : Nonempty W₃.left := hW₃
      refine hconst_zero (N := N) (W := W₃) n ?_
      have hφa : φ.hom.app (op W₂) (F.obj.map (g₂ ≫ g₁).op a) = G.obj.map (g₂ ≫ g₁).op b := by
        rw [← ConcreteCategory.comp_apply, φ.hom.naturality]
        rfl
      have hb : G.obj.map (g₃ ≫ g₂).op (G.obj.map g₁.op b) = 0 := by
        have e₁ : G.obj.map (g₃ ≫ g₂).op (G.obj.map g₁.op b) =
            G.obj.map g₃.op (G.obj.map (g₂ ≫ g₁).op b) := by
          simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc]
        rw [e₁, ← hφa, h₃]
      have := hnat (W := W₁') (W'' := Over.mk ((g₃ ≫ g₂) ≫ h₁)) (Over.homMk (g₃ ≫ g₂))
        (G.obj.map g₁.op b)
      have h₄ : (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W₃) n =
          NX.obj.map (g₃ ≫ g₂).op c := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        erw [← hn]
        exact ConcreteCategory.congr_hom
          ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality g₃.op) n
      rw [h₄]
      refine this.symm.trans ?_
      change e.hom.hom.app (op (Over.mk ((g₃ ≫ g₂) ≫ h₁))) (G.obj.map (g₃ ≫ g₂).op _) = 0
      rw [hb]
      exact LinearMap.map_zero _
    -- hence `b` vanishes on `W₂`
    let W₂' : Over Ui := Over.mk (g₂ ≫ h₁)
    have h₅ : e.hom.hom.app (op W₂') (G.obj.map g₂.op (G.obj.map g₁.op b)) = 0 := by
      refine (hnat (W := W₁') (W'' := W₂') (Over.homMk g₂) (G.obj.map g₁.op b)).trans ?_
      change NX.obj.map g₂.op c = 0
      erw [← hn, hn0]
      exact map_zero _
    have hinj := (((sheafToPresheaf _ _).mapIso e).app (op W₂')).toLinearEquiv.injective
    refine ⟨W₂, g₂ ≫ g₁, ?_, w₂, ?_⟩
    · change G.obj.map (g₂ ≫ g₁).op b = 0
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact hinj (h₅.trans (LinearMap.map_zero _).symm)
    · change (g₂.left ≫ g₁.left) w₂ = v
      rw [Scheme.Hom.comp_apply, hw₂]
      exact hw₁
  intro Ω _ _ s
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    (pointSmallEtale s).sheafFiber_additive
  rw [hzero, Functor.map_zero]

end AlgebraicGeometry.Scheme
