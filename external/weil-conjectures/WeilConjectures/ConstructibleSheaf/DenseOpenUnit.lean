/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Locally constant sheaves on a regular scheme extend uniquely over a dense open

Let `X` be a locally noetherian regular scheme, `j : U ⟶ X` an open immersion with dense image
and `G` a locally constant sheaf of `Λ`-modules on the small étale site of `X`. Then the unit
`G ⟶ j_* j^* G` of the adjunction `j^* ⊣ j_*` is an isomorphism.

It is a monomorphism since morphisms into a locally constant sheaf are determined on a dense
open (`AlgebraicGeometry.Etale.upperStar_map_injective_of_isLocallyConstantSheaf`). It is locally
surjective: a section of `j_* j^* G` over an étale `V ⟶ X` is a section of `G` over
`V ×_X U`; near a point of `V`, refine `V` to an étale `W` over which `G` is constant and whose
underlying scheme is irreducible. Such `W` exist because étale `X`-schemes are again locally
noetherian with integral local rings, so their points have irreducible open neighbourhoods. Then
`W ×_X U` is a nonempty open of `W`, hence irreducible, and the sections of a constant sheaf
over an irreducible étale scheme are the constants
(`AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`); so the section over
`W ×_X U` is a constant, which is the restriction of the same constant over `W`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`: the sections of the
  constant sheaf of modules `N` over an étale `X`-scheme with irreducible underlying space are
  `N`.
- `AlgebraicGeometry.exists_isOpen_irreducibleSpace_of_isDomain_stalk`: a point of a locally
  noetherian scheme with integral local rings has an irreducible open neighbourhood.
- `AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction_of_isRegular`: the unit
  `G ⟶ j_* j^* G` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- **Irreducible neighbourhoods.** A point of a locally noetherian scheme whose local rings are
integral domains has an irreducible open neighbourhood: its connected component is open, the
scheme being locally connected, and a connected locally noetherian scheme with integral local
rings is irreducible (`AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`). -/
theorem exists_isOpen_irreducibleSpace_of_isDomain_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ IrreducibleSpace O := by
  let O : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  refine ⟨O, mem_connectedComponent, ?_⟩
  have : ConnectedSpace O :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : IsLocallyNoetherian O := inferInstance
  exact irreducibleSpace_of_isDomain_stalk O fun y ↦
    have := h y.1
    MulEquiv.isDomain _ (O.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv

/-- The preimage of an open subscheme `U` of `X` in a scheme `W` over `X` with irreducible
underlying space is preconnected: it is an open subset of an irreducible space. -/
lemma preconnectedSpace_pullback_of_irreducibleSpace {W X U : Scheme.{u}} [IrreducibleSpace W]
    (f : W ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] :
    PreconnectedSpace (pullback f j : Scheme.{u}) := by
  have h := (pullback.fst f j).isOpenEmbedding
  refine ⟨h.isInducing.isPreconnected_image.1 ?_⟩
  rw [Set.image_univ]
  exact (IsPreirreducible.open_subset (IrreducibleSpace.isIrreducible_univ W).isPreirreducible
    h.isOpen_range (Set.subset_univ _)).isPreconnected

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}

section VanishingLocus

variable (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The points of an étale `X`-scheme `W` near which a section `σ` of `M` over `W` vanishes:
those in the image of an étale `W' ⟶ W` on which `σ` restricts to zero. This is the analogue for
sheaves of `Λ`-modules of `AlgebraicGeometry.Etale.vanishingLocus` for abelian sheaves. -/
def moduleVanishingLocus {W : X.Etale} (σ : ToType (M.obj.obj (op W))) : Set W.left :=
  {w | ∃ (W' : X.Etale) (g : W' ⟶ W) (w' : W'.left), g.left w' = w ∧ M.obj.map g.op σ = 0}

variable {M}

/-- The vanishing locus of a section is open, étale morphisms being open. -/
lemma isOpen_moduleVanishingLocus {W : X.Etale} (σ : ToType (M.obj.obj (op W))) :
    IsOpen (moduleVanishingLocus M σ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨W', g, w', rfl, hg⟩
  exact ⟨Set.range g.left, fun _ ⟨w'', hw''⟩ ↦ ⟨W', g, w'', hw'', hg⟩,
    g.left.isOpenMap.isOpen_range, w', rfl⟩

/-- A section whose vanishing locus is everything is zero, by the sheaf condition. -/
lemma eq_zero_of_moduleVanishingLocus_eq_univ {W : X.Etale} {σ : ToType (M.obj.obj (op W))}
    (h : moduleVanishingLocus M σ = Set.univ) : σ = 0 := by
  let S : Sieve W :=
    { arrows W' g := M.obj.map g.op σ = 0
      downward_closed {W W'} g hg g' := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg, map_zero] }
  refine Sheaf.isSeparated M W S ?_ σ 0 fun W' g hg ↦ by rw [map_zero]; exact hg
  rw [mem_smallEtaleTopology_iff]
  intro w
  obtain ⟨W', g, w', hw', hg⟩ : w ∈ moduleVanishingLocus M σ := h ▸ Set.mem_univ w
  exact ⟨W', g, hg, w', hw'⟩

/-- **A locally constant sheaf is locally a constant sheaf.** Near a point `w` of an étale
`X`-scheme `W`, a section `σ` of a locally constant sheaf `M` is a constant `n` of a constant
sheaf: there is an étale neighbourhood `g : W₂ ⟶ W` of `w` such that for every nonempty étale
`P ⟶ W₂`, the restriction of `σ` to `P` vanishes if and only if `n` does. -/
lemma exists_isZero_iff_of_isLocallyConstantSheaf [IsLocallyConstantSheaf M] {W : X.Etale}
    (σ : ToType (M.obj.obj (op W))) (w : W.left) :
    ∃ (W₂ : X.Etale) (g : W₂ ⟶ W) (w₂ : W₂.left) (N : ModuleCat.{u + 1} Λ) (n : N),
      g.left w₂ = w ∧ ∀ (P : X.Etale) (h : P ⟶ W₂), Nonempty P.left →
        (M.obj.map (h ≫ g).op σ = 0 ↔ n = 0) := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := M)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (W.hom w)
  set Ui := 𝒰.etalePrecoverageToEtale i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  let W₁ : X.Etale := Scheme.Etale.mk (pullback.fst W.hom (𝒰.f i) ≫ W.hom)
  let g₁ : W₁ ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom (𝒰.f i))
  let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd W.hom (𝒰.f i))
    pullback.condition.symm
  obtain ⟨w₁, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hu.symm
  have := hc i
  obtain ⟨N, ⟨e₀⟩⟩ := (M.over Ui).mem_essImage_of_isConstant (J := X.smallEtaleTopology.over Ui)
  let e : M.over Ui ≅ ((constantSheaf X.smallEtaleTopology _).obj N).over Ui :=
    e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology _ Ui N
  set NX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  have hnat {V V' : Over Ui} (k : V' ⟶ V) (y : ToType (M.obj.obj (op V.left))) :
      e.hom.hom.app (op V') (M.obj.map k.left.op y) =
        NX.obj.map k.left.op (e.hom.hom.app (op V) y) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality k.op) y
  let W₁' : Over Ui := Over.mk h₁
  let c : ToType (NX.obj.obj (op W₁)) := e.hom.hom.app (op W₁') (M.obj.map g₁.op σ)
  have hsurj := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallySurjective
  obtain ⟨W₂, g₂, ⟨n, hn⟩, w₂, hw₂⟩ := (mem_smallEtaleTopology_iff _).1
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) c) w₁
  change ToType N at n
  refine ⟨W₂, g₂ ≫ g₁, w₂, N, n, ?_, fun P h hP ↦ ?_⟩
  · change (g₂.left ≫ g₁.left) w₂ = w
    rw [Scheme.Hom.comp_apply, hw₂]
    exact hw₁
  · let P' : Over Ui := Over.mk ((h ≫ g₂) ≫ h₁)
    have hinj := (((sheafToPresheaf _ _).mapIso e).app (op P')).toLinearEquiv.injective
    have h₄ : e.hom.hom.app (op P') (M.obj.map (h ≫ g₂ ≫ g₁).op σ) =
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op P) n := by
      have := hnat (V := W₁') (V' := P') (Over.homMk (h ≫ g₂)) (M.obj.map g₁.op σ)
      rw [← Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      refine this.trans ?_
      change NX.obj.map (h ≫ g₂).op c = _
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [← hn]
      exact (ConcreteCategory.congr_hom
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality h.op)
          n).symm
    constructor
    · intro h0
      refine eq_zero_of_toSheafify_app_eq_zero (W := P) n ?_
      rw [← h₄, h0]
      exact LinearMap.map_zero _
    · rintro rfl
      refine hinj ((h₄.trans ?_).trans (LinearMap.map_zero _).symm)
      exact map_zero _

/-- **The vanishing locus of a section of a locally constant sheaf is open and closed.** Near a
point outside it the section is a nonzero constant, and a nonzero constant vanishes on no
nonempty étale scheme. -/
theorem isClopen_moduleVanishingLocus [IsLocallyConstantSheaf M] {W : X.Etale}
    (σ : ToType (M.obj.obj (op W))) : IsClopen (moduleVanishingLocus M σ) := by
  refine ⟨?_, isOpen_moduleVanishingLocus σ⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro w hw
  obtain ⟨W₂, g, w₂, N, n, hw₂, hn⟩ := exists_isZero_iff_of_isLocallyConstantSheaf σ w
  have hn0 : n ≠ 0 := by
    intro h0
    exact hw ⟨W₂, g, w₂, hw₂, by simpa using (hn W₂ (𝟙 _) ⟨w₂⟩).2 h0⟩
  refine ⟨Set.range g.left, ?_, g.left.isOpenMap.isOpen_range, w₂, hw₂⟩
  rintro _ ⟨y, rfl⟩ ⟨W', g', w', hw', hg'⟩
  obtain ⟨Z, p₁, p₂, z, hp, -, -⟩ := exists_eq_of_apply_eq g g' y w' hw'.symm
  refine hn0 ((hn Z p₁ ⟨z⟩).1 ?_)
  rw [hp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg', map_zero]

/-- **Sections of a locally constant sheaf over a connected étale scheme are determined near a
point.** If a section of a locally constant sheaf `M` over an étale `X`-scheme with connected
underlying space vanishes near one point, it is zero. -/
theorem eq_zero_of_mem_moduleVanishingLocus [IsLocallyConstantSheaf M] {W : X.Etale}
    [PreconnectedSpace W.left] {σ : ToType (M.obj.obj (op W))} {w : W.left}
    (hw : w ∈ moduleVanishingLocus M σ) : σ = 0 :=
  eq_zero_of_moduleVanishingLocus_eq_univ
    ((isClopen_moduleVanishingLocus σ).eq_univ ⟨w, hw⟩)

end VanishingLocus

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}

section ConstantSheaf

variable (N : ModuleCat.{u + 1} Λ)

/-- A constant sheaf of modules on the small étale site is locally constant, trivialised by the
identity cover. -/
instance isLocallyConstantSheaf_constantSheaf :
    IsLocallyConstantSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) := by
  have : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N).IsConstant
      X.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  exact ⟨⟨⟨Cover.mkOfCovers PUnit (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun x ↦ ⟨⟨⟩, x, rfl⟩)
    (fun _ ↦ inferInstance), fun _ ↦
    (isConstant_over_iff_upperStar _ _ _).2 (Sheaf.IsConstant.upperStar (X := X) _ _ _)⟩⟩⟩

/-- **Sections of a constant sheaf over a connected étale scheme.** The sections over an étale
`X`-scheme with nonempty connected underlying space of the constant étale sheaf of modules `N`
are the constants: a section is a constant near one point, and then everywhere since the
locus where two sections of a locally constant sheaf agree is open and closed. -/
theorem bijective_toSheafify_app_of_preconnectedSpace {W : X.Etale} [PreconnectedSpace W.left]
    [Nonempty W.left] :
    Function.Bijective
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W)) := by
  refine ⟨fun n n' h ↦ sub_eq_zero.1 (eq_zero_of_toSheafify_app_eq_zero (N := N) (W := W)
    (n - n') (by rw [map_sub]; exact sub_eq_zero.2 h)),
    fun σ ↦ ?_⟩
  have hsurj := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallySurjective
  obtain ⟨w⟩ := ‹Nonempty W.left›
  obtain ⟨W₂, g₂, ⟨n, hn⟩, w₂, hw₂⟩ := (mem_smallEtaleTopology_iff _).1
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) σ) w
  change ToType N at n
  refine ⟨n, (sub_eq_zero.1 (eq_zero_of_mem_moduleVanishingLocus
    (M := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)
    (w := w) ⟨W₂, g₂, w₂, hw₂, ?_⟩))⟩
  rw [map_sub, sub_eq_zero]
  exact (ConcreteCategory.congr_hom
    ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality g₂.op)
      n).symm.trans hn

end ConstantSheaf

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unit of `j^* ⊣ j_*` for the restriction along an open immersion is restriction of
sections along the projection `V ×_X U ⟶ V`. -/
lemma openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale) :
    ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G).hom.app
        (op V) =
      G.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
        trivial).counit.app V).op :=
  rfl

variable {j} in
/-- **Local surjectivity of the unit `G ⟶ j_* j^* G`.** Near a point `v` of an étale `X`-scheme
`V`, a section `σ` of `j_* j^* G` over `V` comes from a section of `G`: on an étale
neighbourhood `W` of `v` with irreducible underlying space over which `G` is constant, the
section `σ` restricted to the nonempty open `W ×_X U` of `W`, which is again irreducible, is a
constant, which extends over `W`. -/
lemma exists_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_eq
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] (hj : Dense (Set.range j.base))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf G]
    {V : X.Etale}
    (σ : ToType (((j)_*[ModuleCat.{u + 1} Λ].obj
      ((openImmersionRestriction (ModuleCat.{u + 1} Λ) j).obj G)).obj.obj (op V)))
    (v : V.left) :
    ∃ (W : X.Etale) (g : W ⟶ V) (t : ToType (G.obj.obj (op W))),
      ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        G).hom.app (op W) t =
        ((j)_*[ModuleCat.{u + 1} Λ].obj
          ((openImmersionRestriction (ModuleCat.{u + 1} Λ) j).obj G)).obj.map g.op σ ∧
      v ∈ Set.range g.left := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (V.hom v)
  set Ui := 𝒰.etalePrecoverageToEtale i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  let W₁ : X.Etale := Scheme.Etale.mk (pullback.fst V.hom (𝒰.f i) ≫ V.hom)
  let g₁ : W₁ ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom (𝒰.f i))
  let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd V.hom (𝒰.f i))
    pullback.condition.symm
  obtain ⟨w₁, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback v u hu.symm
  have := hc i
  obtain ⟨N, ⟨e₀⟩⟩ := (G.over Ui).mem_essImage_of_isConstant (J := X.smallEtaleTopology.over Ui)
  let e : G.over Ui ≅ ((constantSheaf X.smallEtaleTopology _).obj N).over Ui :=
    e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology _ Ui N
  set NX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  -- an irreducible neighbourhood `W` of `w₁`
  have : IsLocallyNoetherian W₁.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X) W₁.hom
  obtain ⟨O, hO, hOirr⟩ := exists_isOpen_irreducibleSpace_of_isDomain_stalk (hX W₁) w₁
  let W : X.Etale := Scheme.Etale.mk (O.ι ≫ W₁.hom)
  let g₂ : W ⟶ W₁ := MorphismProperty.Over.homMk O.ι
  have : IrreducibleSpace W.left := hOirr
  -- its open `W ×_X U`
  let ε := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app W
  let WU := (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W)
  have : Nonempty WU.left := by
    have : Nonempty W.left := ⟨⟨w₁, hO⟩⟩
    obtain ⟨w, x, hx⟩ := exists_apply_mem_range_of_dense j hj W
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w x hx.symm
    exact ⟨z⟩
  have : PreconnectedSpace WU.left :=
    preconnectedSpace_pullback_of_irreducibleSpace (W := W.left) (X := X) W.hom j
  -- the section over `W ×_X U` is a constant
  set σ' := ((j)_*[ModuleCat.{u + 1} Λ].obj
    ((openImmersionRestriction (ModuleCat.{u + 1} Λ) j).obj G)).obj.map (g₂ ≫ g₁).op σ
  let P' : Over Ui := Over.mk (ε ≫ g₂ ≫ h₁)
  let P : Over Ui := Over.mk (g₂ ≫ h₁)
  obtain ⟨n, hn⟩ := (bijective_toSheafify_app_of_preconnectedSpace N (W := WU)).2
    (e.hom.hom.app (op P') σ')
  refine ⟨W, g₂ ≫ g₁, e.inv.hom.app (op P)
    ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W) n), ?_,
    ⟨w₁, hO⟩, hw₁⟩
  rw [openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app]
  have h₁ := ConcreteCategory.congr_hom (e.inv.hom.naturality (Over.homMk ε : P' ⟶ P).op)
    ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W) n)
  have h₂ := ConcreteCategory.congr_hom
    ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality ε.op) n
  refine h₁.symm.trans ?_
  change e.inv.hom.app (op P') (NX.obj.map ε.op _) = σ'
  erw [← h₂, hn]
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op P')) e.hom_inv_id) σ'

/-- **Locally constant sheaves extend uniquely over a dense open** (blueprint
`theorem-purity-real-sheaves-curves`, part (3)). Let `X` be a locally noetherian scheme such that
the local rings of all étale `X`-schemes are integral domains (for instance a regular scheme),
`j : U ⟶ X` an open immersion with dense image and `G` a locally constant sheaf of modules on
the small étale site of `X`. Then the unit `G ⟶ j_* j^* G` is an isomorphism. -/
theorem isIso_unit_upperStarLowerStarAdjunction_of_isDomain_stalk
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] (hj : Dense (Set.range j.base))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf G] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) := by
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let adj' := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have hmono : Mono (adj.unit.app G) := by
    refine ⟨fun a b hab ↦ upperStar_map_injective_of_isLocallyConstantSheaf (M := G) j hj ?_⟩
    have h := congrArg (fun f ↦ (j)^*[ModuleCat.{u + 1} Λ].map f) hab
    simp only [Functor.map_comp] at h
    exact (cancel_mono _).1 h
  have hepi' : Epi (adj'.unit.app G) := by
    have : Sheaf.IsLocallySurjective (adj'.unit.app G) := ⟨fun {V} σ ↦ by
      rw [mem_smallEtaleTopology_iff]
      intro v
      obtain ⟨W, g, t, ht, hv⟩ :=
        exists_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_eq (G := G) hX hj σ v
      exact ⟨W, g, ⟨t, ht⟩, hv⟩⟩
    infer_instance
  have hepi : Epi (adj.unit.app G) := by
    have h : adj.unit.app G = adj'.unit.app G ≫
        (j)_*[ModuleCat.{u + 1} Λ].map ((adj.leftAdjointUniq adj').inv.app G) := by
      rw [← adj.unit_leftAdjointUniq_hom_app adj' G, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    rw [h]
    infer_instance
  exact isIso_of_mono_of_epi _

/-- The local rings of an étale scheme over a regular scheme are integral domains, being regular
local rings (`AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`). -/
lemma isDomain_stalk_left_of_isRegular [IsRegular X] (W : X.Etale)
    (w : W.left) : IsDomain (W.left.presheaf.stalk w) :=
  @IsRegularLocalRing.isDomain _ _ (isRegularLocalRing_stalk_of_etale (X := W.left) (Y := X)
    W.hom (fun _ ↦ IsRegular.isRegularLocalRing_stalk _) w)

/-- **Locally constant sheaves on a regular scheme extend uniquely over a dense open.** For a
locally noetherian regular scheme `X`, an open immersion `j : U ⟶ X` with dense image and a
locally constant sheaf `G` of modules on the small étale site of `X`, the unit
`G ⟶ j_* j^* G` is an isomorphism: étale `X`-schemes are again regular, so their local rings
are integral domains. -/
theorem isIso_unit_upperStarLowerStarAdjunction_of_isRegular [IsLocallyNoetherian X]
    [IsRegular X] (hj : Dense (Set.range j.base))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf G] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) :=
  isIso_unit_upperStarLowerStarAdjunction_of_isDomain_stalk j isDomain_stalk_left_of_isRegular
    hj G

end Etale

end AlgebraicGeometry
