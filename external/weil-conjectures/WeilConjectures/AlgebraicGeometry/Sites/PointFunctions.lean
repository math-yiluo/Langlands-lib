/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The étale sheaf of functions on points

For a scheme `X` and an abelian group `M`, the presheaf on the small étale site of `X` sending
an étale `X`-scheme `V` to the group `V → M` of *all* functions on the underlying set of `V`
is a sheaf: an étale covering family is jointly surjective, and the points of a fibre product
surject onto the pairs of points with a common image.

## Main definitions

- `AlgebraicGeometry.Scheme.pointFunctionPresheaf`: the presheaf `V ↦ (V → M)`.
- `AlgebraicGeometry.Scheme.pointFunctionSheaf`: the same, as a sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.isSheaf_pointFunctionPresheaf`: the presheaf `V ↦ (V → M)` is a
  sheaf for the small étale topology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (M : AddCommGrpCat.{u + 1})

/-- The presheaf on the small étale site of `X` sending an étale `X`-scheme `V` to the group
of all functions from the underlying set of `V` to `M`, with restriction given by
precomposition. -/
noncomputable def pointFunctionPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := AddCommGrpCat.of (V.unop.left → M)
  map {V W} φ := AddCommGrpCat.ofHom
    { toFun D y := D (φ.unop.left y)
      map_zero' := rfl
      map_add' _ _ := rfl }

set_option backward.isDefEq.respectTransparency false in
variable {X} in
/-- In a covering sieve of the small étale site every point is in the image of an arrow of
the sieve. -/
lemma exists_of_mem_smallEtaleTopology {V : X.Etale} {S : Sieve V}
    (hS : S ∈ X.smallEtaleTopology V) (v : V.left) :
    ∃ (W : X.Etale) (g : W ⟶ V) (w : W.left), S g ∧ g.left w = v := by
  obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hS
  obtain ⟨i, u, hu⟩ := U.exists_eq v
  exact ⟨_, (U.f i).asOverProp X, u, hU _ _ (by use i), hu⟩

variable {X} in
/-- Two points of étale `X`-schemes with a common image in `V` come from one point of an étale
`X`-scheme mapping to both. -/
lemma exists_eq_of_apply_eq {V W₁ W₂ : X.Etale} (g₁ : W₁ ⟶ V) (g₂ : W₂ ⟶ V) (w₁ : W₁.left)
    (w₂ : W₂.left) (h : g₁.left w₁ = g₂.left w₂) :
    ∃ (Z : X.Etale) (p₁ : Z ⟶ W₁) (p₂ : Z ⟶ W₂) (z : Z.left), p₁ ≫ g₁ = p₂ ≫ g₂ ∧
      p₁.left z = w₁ ∧ p₂.left z = w₂ := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w₁ w₂ h
  let e := PreservesPullback.iso (Etale.forget X ⋙ Over.forget X) g₁ g₂
  refine ⟨pullback g₁ g₂, pullback.fst _ _, pullback.snd _ _, e.inv z, pullback.condition,
    ?_, ?_⟩
  · have h₁ : e.inv ≫ (pullback.fst g₁ g₂).left = pullback.fst g₁.left g₂.left :=
      PreservesPullback.iso_inv_fst _ _ _
    rw [← hz₁, ← h₁]
    rfl
  · have h₂ : e.inv ≫ (pullback.snd g₁ g₂).left = pullback.snd g₁.left g₂.left :=
      PreservesPullback.iso_inv_snd _ _ _
    rw [← hz₂, ← h₂]
    rfl

/-- **Functions on points form an étale sheaf.** The presheaf `V ↦ (V → M)` of all functions
on the underlying set satisfies the sheaf condition for the small étale topology: a compatible
family on a covering sieve glues, since every point of `V` is in the image of an arrow of the
sieve, and two such preimages are images of one point of a fibre product. -/
theorem isSheaf_pointFunctionPresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (X.pointFunctionPresheaf M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  choose W g w hg hgw using exists_of_mem_smallEtaleTopology hS
  have key : ∀ {W' : X.Etale} (g' : W' ⟶ V) (hg' : S g') (w' : W'.left) (v : V.left),
      g'.left w' = v → (x g' hg' : W'.left → M) w' = (x (g v) (hg v) : _ → M) (w v) := by
    intro W' g' hg' w' v hv
    obtain ⟨Z, p₁, p₂, z, hp, hz₁, hz₂⟩ :=
      exists_eq_of_apply_eq g' (g v) w' (w v) (by rw [hv, hgw])
    have h : (x g' hg' : W'.left → M) (p₁.left z) = (x (g v) (hg v) : _ → M) (p₂.left z) :=
      congrFun (hx p₁ p₂ hg' (hg v) hp) z
    rw [← hz₁, ← hz₂]
    exact h
  refine ⟨fun v ↦ (x (g v) (hg v) : _ → M) (w v), fun W' g' hg' ↦ ?_, fun t ht ↦ ?_⟩
  · funext w'
    exact (key g' hg' w' _ rfl).symm
  · funext v
    have h : t ((g v).left (w v)) = (x (g v) (hg v) : _ → M) (w v) :=
      congrFun (ht (g v) (hg v)) (w v)
    rw [← h, hgw]

/-- The étale sheaf `V ↦ (V → M)` of all functions on the underlying set of an étale
`X`-scheme. -/
noncomputable def pointFunctionSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨X.pointFunctionPresheaf M, X.isSheaf_pointFunctionPresheaf M⟩

/-- The map of presheaves from the constant presheaf `M` to `V ↦ (V → M)`, sending `m` to the
constant function `m`. -/
noncomputable def constToPointFunctionPresheaf :
    (Functor.const X.Etaleᵒᵖ).obj M ⟶ X.pointFunctionPresheaf M where
  app V := AddCommGrpCat.ofHom
    { toFun m _ := m
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- The map from the constant sheaf `M` to the sheaf `V ↦ (V → M)` of functions on points,
sending a section to the corresponding locally constant function. It is an isomorphism when
every étale `X`-scheme is discrete, for instance over a field
(`AlgebraicGeometry.Scheme.isIso_constantSheafToPointFunctionSheaf`). -/
noncomputable def constantSheafToPointFunctionSheaf :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶ X.pointFunctionSheaf M :=
  ⟨sheafifyLift _ (X.constToPointFunctionPresheaf M) (X.isSheaf_pointFunctionPresheaf M)⟩

section Pushforward

variable {X} {Z : Scheme.{u}} (g : Z ⟶ X)

lemma overPullback_map_left_fst {V W : X.Etale} (φ : W ⟶ V) (z : ↥(pullback W.hom g)) :
    pullback.fst V.hom g (((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).left z) =
      φ.left (pullback.fst W.hom g z) := by
  have h : ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).left ≫ pullback.fst V.hom g =
      pullback.fst W.hom g ≫ φ.left := by simp
  exact congrArg (fun f ↦ f z) h

/-- Restriction of functions on points along `g : Z ⟶ X`: the map of sheaves
`(V → M) ⟶ (V ×_X Z → M)` given by precomposition with the first projection. -/
noncomputable def pointFunctionSheafToLowerStar :
    X.pointFunctionSheaf M ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (Z.pointFunctionSheaf M) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun D z := D (pullback.fst V.unop.hom g z)
          map_zero' := rfl
          map_add' _ _ := rfl }
     naturality {V W} φ := by
      ext D
      funext z
      exact congrArg D (overPullback_map_left_fst g φ.unop z).symm }⟩

lemma pointFunctionSheafToLowerStar_app_apply (V : X.Etale) (D : V.left → M)
    (z : ↥(pullback V.hom g)) :
    ((pointFunctionSheafToLowerStar M g).hom.app (op V) D : _ → M) z =
      D (pullback.fst V.hom g z) :=
  rfl


open Classical in
/-- Extension by zero of a function on `V ×_X Z` along the first projection to `V`: the value
at `y` is that at a preimage of `y`, if there is one, and `0` otherwise. -/
noncomputable def extendByZero {V : X.Etale} (c : ↥(pullback V.hom g) → M) (y : V.left) : M :=
  if h : ∃ z, pullback.fst V.hom g z = y then c h.choose else 0

variable {M g}

lemma extendByZero_of_notMem {V : X.Etale} (c : ↥(pullback V.hom g) → M) {y : V.left}
    (hy : V.hom y ∉ Set.range g) : extendByZero M g c y = 0 := by
  have h : ¬ ∃ z, pullback.fst V.hom g z = y := by
    rintro ⟨z, rfl⟩
    exact hy ⟨pullback.snd V.hom g z,
      (congrArg (fun f ↦ f z) (pullback.condition (f := V.hom) (g := g))).symm⟩
  rw [extendByZero, dite_eq_right h]

lemma extendByZero_zero {V : X.Etale} : extendByZero M g (V := V) 0 = 0 := by
  funext y
  rw [extendByZero]
  split_ifs <;> rfl

lemma extendByZero_add {V : X.Etale} (c c' : ↥(pullback V.hom g) → M) :
    extendByZero M g (c + c') = extendByZero M g c + extendByZero M g c' := by
  funext y
  simp only [extendByZero, Pi.add_apply]
  split_ifs <;> simp

variable [IsPreimmersion g]

lemma extendByZero_fst {V : X.Etale} (c : ↥(pullback V.hom g) → M) (z : ↥(pullback V.hom g)) :
    extendByZero M g c (pullback.fst V.hom g z) = c z := by
  have h : ∃ z', pullback.fst V.hom g z' = pullback.fst V.hom g z := ⟨z, rfl⟩
  rw [extendByZero, dite_eq_left h]
  congr 1
  exact (pullback.fst V.hom g).isEmbedding.injective h.choose_spec

lemma extendByZero_comp {V W : X.Etale} (φ : W ⟶ V) (c : ↥(pullback V.hom g) → M)
    (y : W.left) :
    extendByZero M g (fun z ↦ c (((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).left z)) y =
      extendByZero M g c (φ.left y) := by
  by_cases h : ∃ z, pullback.fst W.hom g z = y
  · obtain ⟨z, rfl⟩ := h
    rw [extendByZero_fst, ← overPullback_map_left_fst, extendByZero_fst]
  · have hy : W.hom y ∉ Set.range g := fun hy ↦
      h ((Set.ext_iff.1 (Scheme.Pullback.range_fst W.hom g) y).2 hy)
    have hy' : V.hom (φ.left y) ∉ Set.range g := by
      have e : V.hom (φ.left y) = W.hom y :=
        congrArg (fun f : W.left ⟶ X ↦ f y) (CategoryTheory.Over.w ((Etale.forget X).map φ))
      exact e ▸ hy
    rw [extendByZero_of_notMem _ hy, extendByZero_of_notMem _ hy']

variable (M g)

/-- Extension by zero of functions on points along a preimmersion `g : Z ⟶ X`: a function `c`
on `V ×_X Z` is sent to the function on `V` which is `c` on the image of the first projection,
an injection, and `0` elsewhere. -/
noncomputable def lowerStarPointFunctionSheafToPointFunctionSheaf :
    (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (Z.pointFunctionSheaf M) ⟶
      X.pointFunctionSheaf M :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun c := extendByZero M g (V := V.unop) c
          map_zero' := extendByZero_zero
          map_add' := extendByZero_add }
     naturality {V W} φ := by
      ext c
      funext y
      exact extendByZero_comp φ.unop c y }⟩

lemma lowerStarPointFunctionSheafToPointFunctionSheaf_app_apply (V : X.Etale)
    (c : ↥(pullback V.hom g) → M) :
    ((lowerStarPointFunctionSheafToPointFunctionSheaf M g).hom.app (op V) c : _ → M) =
      extendByZero M g c :=
  rfl


/-- Extension by zero followed by restriction is the identity. -/
@[reassoc (attr := simp)]
lemma lowerStarPointFunctionSheafToPointFunctionSheaf_comp :
    lowerStarPointFunctionSheafToPointFunctionSheaf M g ≫ pointFunctionSheafToLowerStar M g =
      𝟙 _ := by
  ext V c
  funext z
  exact extendByZero_fst c z

/-- Extension by zero along `g` followed by restriction along a morphism `g'` with image
disjoint from that of `g` is zero. -/
lemma lowerStarPointFunctionSheafToPointFunctionSheaf_comp_eq_zero {Z' : Scheme.{u}}
    (g' : Z' ⟶ X) (h : Disjoint (Set.range g) (Set.range g')) :
    lowerStarPointFunctionSheafToPointFunctionSheaf M g ≫ pointFunctionSheafToLowerStar M g' =
      0 := by
  ext V c
  funext z
  refine extendByZero_of_notMem c ?_
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact fun hm ↦ h.ne_of_mem hm (Set.mem_range_self _) rfl

end Pushforward

section Indicator

variable {X}

open Classical in
/-- Multiplication by the indicator function of the preimage of a set `S` of points of `X`: the
endomorphism of `V ↦ (V → M)` keeping the values at the points of `V` over `S` and replacing the
others by `0`. -/
noncomputable def pointFunctionSheafIndicator (S : Set X) :
    X.pointFunctionSheaf M ⟶ X.pointFunctionSheaf M :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun D y := if V.unop.hom y ∈ S then D y else 0
          map_zero' := by
            funext y
            change (if _ then (0 : M) else 0) = 0
            split_ifs <;> rfl
          map_add' D D' := by
            funext y
            change (if _ then D y + D' y else 0) = (if _ then D y else 0) + (if _ then D' y else 0)
            split_ifs <;> simp }
     naturality {V W} φ := by
      ext D
      funext y
      have e : W.unop.hom y = V.unop.hom (φ.unop.left y) :=
        (congrArg (fun f : W.unop.left ⟶ X ↦ f y)
          (CategoryTheory.Over.w ((Etale.forget X).map φ.unop))).symm
      change (if W.unop.hom y ∈ S then D (φ.unop.left y) else 0) =
        if V.unop.hom (φ.unop.left y) ∈ S then D (φ.unop.left y) else 0
      rw [e] }⟩

open Classical in
lemma pointFunctionSheafIndicator_app_apply (S : Set X) (V : X.Etale) (D : V.left → M)
    (y : V.left) :
    ((pointFunctionSheafIndicator M S).hom.app (op V) D : V.left → M) y =
      if V.hom y ∈ S then D y else 0 :=
  rfl


end Indicator

section Neighbourhoods

variable {X} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- The open subscheme `U` of an étale `X`-scheme `V`, as an étale `X`-scheme. -/
noncomputable abbrev Etale.ofOpens (V : X.Etale) (U : V.left.Opens) : X.Etale :=
  Etale.mk (U.ι ≫ V.hom)

/-- The inclusion of an open subscheme of an étale `X`-scheme, in the small étale site. -/
noncomputable abbrev Etale.ofOpensι (V : X.Etale) (U : V.left.Opens) :
    Etale.ofOpens V U ⟶ V :=
  MorphismProperty.Over.homMk U.ι rfl

/-- **Zariski neighbourhoods are étale neighbourhoods.** If an open subscheme `U` of an étale
`X`-scheme `V` contains the image of a geometric point `v` of `V` over `s`, then `v` lifts to
`U`. -/
lemma exists_pointSmallEtale_fiber_ofOpens {V : X.Etale} (v : (pointSmallEtale s).fiber.obj V)
    (U : V.left.Opens) (hU : Set.range v.left ⊆ (U : Set V.left)) :
    ∃ v' : (pointSmallEtale s).fiber.obj (Etale.ofOpens V U),
      (pointSmallEtale s).fiber.map (Etale.ofOpensι V U) v' = v := by
  have hr : Set.range v.left ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have hv₀ := IsOpenImmersion.lift_fac U.ι v.left hr
  refine ⟨CategoryTheory.Over.homMk (IsOpenImmersion.lift U.ι v.left hr) ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι v.left hr ≫ U.ι ≫ V.hom = s
    rw [← Category.assoc, hv₀]
    exact CategoryTheory.Over.w v
  · exact CategoryTheory.Over.OverMorphism.ext hv₀

/-- `AlgebraicGeometry.Scheme.exists_pointSmallEtale_fiber_ofOpens` for the universe-lifted
geometric points. -/
lemma exists_ulift_pointSmallEtale_fiber_ofOpens {V : X.Etale}
    (v : (pointSmallEtale s).ulift.{u + 1}.fiber.obj V) (U : V.left.Opens)
    (hU : Set.range v.down.left ⊆ (U : Set V.left)) :
    ∃ v' : (pointSmallEtale s).ulift.{u + 1}.fiber.obj (Etale.ofOpens V U),
      (pointSmallEtale s).ulift.{u + 1}.fiber.map (Etale.ofOpensι V U) v' = v := by
  obtain ⟨v', hv'⟩ := exists_pointSmallEtale_fiber_ofOpens s v.down U hU
  exact ⟨ULift.up v', ULift.ext hv'⟩

end Neighbourhoods

section Discrete

variable {X}

/-- The fibre of `V ↦ (V → M)` at a geometric point: every germ of a function on points is
the germ of a constant function, if every étale `X`-scheme is discrete. -/
lemma toPresheafFiber_pointFunctionPresheaf_eq_const (h : ∀ V : X.Etale, DiscreteTopology V.left)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {V : X.Etale}
    (v : (pointSmallEtale s).ulift.{u + 1}.fiber.obj V) (D : V.left → M) :
    ∃ m : M, ∃ (W : X.Etale) (g : W ⟶ V) (w : (pointSmallEtale s).ulift.{u + 1}.fiber.obj W),
      (pointSmallEtale s).ulift.{u + 1}.fiber.map g w = v ∧
        (X.pointFunctionPresheaf M).map g.op D = fun _ ↦ m := by
  let y₀ : V.left := v.down.left (IsLocalRing.closedPoint Ω)
  let U : V.left.Opens := ⟨{y₀}, isOpen_discrete _⟩
  have hU : Set.range v.down.left ⊆ (U : Set V.left) := by
    rintro _ ⟨z, rfl⟩
    have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    change _ = y₀
    rw [show z = IsLocalRing.closedPoint Ω from @Subsingleton.elim (Spec (.of Ω)) this z _]
  obtain ⟨v', hv'⟩ := exists_ulift_pointSmallEtale_fiber_ofOpens s v U hU
  refine ⟨D y₀, _, Etale.ofOpensι V U, v', hv', funext fun z ↦ ?_⟩
  change D (U.ι z) = D y₀
  have : U.ι z ∈ (U : Set V.left) := by
    rw [← Scheme.Opens.range_ι]
    exact Set.mem_range_self z
  rw [Set.mem_singleton_iff.1 this]

/-- An étale scheme over a one-point scheme, for instance the spectrum of a field, is
discrete. -/
lemma discreteTopology_of_etale_of_unique {S : Scheme.{u}} [Unique S] (V : S.Etale) :
    DiscreteTopology V.left := by
  have h := V.hom.isDiscrete_preimage_singleton (default : S)
  rw [show V.hom ⁻¹' {(default : S)} = Set.univ from
    Set.eq_univ_of_forall fun _ ↦ @Unique.eq_default S _ _] at h
  exact isDiscrete_univ_iff.1 h

/-- Over a scheme all of whose étale schemes are discrete, for instance the spectrum of a
field, the constant sheaf `M` is the sheaf of all functions on points: the map
`AlgebraicGeometry.Scheme.constantSheafToPointFunctionSheaf` is an isomorphism. It is checked
on the fibres at geometric points, both of which are `M`. -/
theorem isIso_constantSheafToPointFunctionSheaf
    (h : ∀ V : X.Etale, DiscreteTopology V.left) :
    IsIso (X.constantSheafToPointFunctionSheaf M) := by
  refine isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
  let Φ := X.uliftPointSmallEtale x
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let t₀ : Φ.fiber.obj T := (Φ.uniqueFiberObj T hT).default
  -- the fibre map, precomposed with `M ≅ (M_X)_x`, sends `m` to the germ of `m` at `t₀`
  have hcomp : (Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M) =
      (X.constToPointFunctionPresheaf M).app (op T) ≫
        Φ.toPresheafFiber T t₀ (X.pointFunctionPresheaf M) := by
    have h₁ : (Φ.presheafFiberConstIso M).inv =
        Φ.toPresheafFiber T t₀ ((Functor.const X.Etaleᵒᵖ).obj M) := by
      have h := Φ.toPresheafFiber_presheafFiberConstIso_hom M T t₀
      calc (Φ.presheafFiberConstIso M).inv = 𝟙 _ ≫ (Φ.presheafFiberConstIso M).inv :=
            (Category.id_comp _).symm
        _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ((Φ.presheafFiberConstIso M).inv ≫ Φ.presheafFiber.map
      (CategoryTheory.toSheafify _ _)) ≫ Φ.presheafFiber.map (sheafifyLift _ _ _) = _
    rw [Category.assoc, ← Functor.map_comp, toSheafify_sheafifyLift, h₁,
      Φ.toPresheafFiber_naturality]
    rfl
  have hbij : Function.Bijective ((X.constToPointFunctionPresheaf M).app (op T) ≫
      Φ.toPresheafFiber T t₀ (X.pointFunctionPresheaf M)) := by
    refine ⟨fun m m' hm ↦ ?_, fun p ↦ ?_⟩
    · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hm
      obtain ⟨W, g, w, -, hg⟩ := (Φ.toPresheafFiber_eq_iff' _ _ _ _).1 hm
      exact congrFun hg (w.down.left (IsLocalRing.closedPoint _))
    · obtain ⟨V, v, D, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
      obtain ⟨m, W, g, w, hw, hg⟩ :=
        toPresheafFiber_pointFunctionPresheaf_eq_const M h _ v D
      refine ⟨m, ?_⟩
      have e₁ := Φ.toPresheafFiber_w_apply g w (X.pointFunctionPresheaf M) D
      rw [hg, show Φ.fiber.map g w = v from hw] at e₁
      have e₂ := Φ.toPresheafFiber_w_apply (hT.from W) w (X.pointFunctionPresheaf M)
        (fun _ ↦ m)
      rw [show Φ.fiber.map (hT.from W) w = t₀ from (Φ.uniqueFiberObj T hT).uniq _] at e₂
      rw [ConcreteCategory.comp_apply, ← e₁]
      exact e₂.symm
  have hiso : IsIso ((Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M)) := by
    rw [hcomp]
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have : Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M) =
      (Φ.sheafFiberConstantSheafIso M).hom ≫ ((Φ.sheafFiberConstantSheafIso M).inv ≫
        Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M)) := by
    simp
  rw [this]
  infer_instance

end Discrete

end AlgebraicGeometry.Scheme
