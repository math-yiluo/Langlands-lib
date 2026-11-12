import Langlands.Geometry.Analytic.InducedAnalyticSpace

/-! # Berkovich's spaces `X_Σ` for `G`-sets `Σ` -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

open PresentedAffinoidAlgebra.InducedAction (correction correction_spec)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G]
  (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G)
  (S : Type z)

/-! ## The copies of `X` indexed by `S` -/

/-- The disjoint union of copies of `X`, one for each element of `S`. -/
abbrev copies : Cofan fun _ : S => X.V :=
  localizedSigmaCofan fun _ : S => X.V

/-- The disjoint union of the copies is a coproduct. -/
def isColimitCopies : IsColimit (copies X S) :=
  isColimitLocalizedSigmaCofan _

/-- The inclusion of the copy indexed by `s`. -/
abbrev copy (s : S) : X.V ⟶ (copies X S).pt :=
  (copies X S).inj s

variable {X S} in
theorem copies_hom_ext {Y : LocalizedCategory.{u, max z v, max z v} (K := K)}
    {f f' : (copies X S).pt ⟶ Y} (h : ∀ s, copy X S s ≫ f = copy X S s ≫ f') : f = f' :=
  Cofan.IsColimit.hom_ext (isColimitCopies X S) _ _ h

/-- The underlying morphism of the projection `X_S → X`: the identity on every copy. -/
def projectionHom : (copies X S).pt ⟶ X.V :=
  Cofan.IsColimit.desc (isColimitCopies X S) fun _ => 𝟙 X.V

@[reassoc (attr := simp)]
theorem copy_projectionHom (s : S) : copy X S s ≫ projectionHom X S = 𝟙 X.V :=
  Cofan.IsColimit.fac _ _ s

/-! ## The action of `G` -/

variable [MulAction G S]

/-- The action of `g ∈ G`: it sends the copy indexed by `s` to the copy indexed by `g • s`, by
the action of `g` on `X`. -/
def actionMap (g : G) : (copies X S).pt ⟶ (copies X S).pt :=
  Cofan.IsColimit.desc (isColimitCopies X S) fun s => X.ρ g ≫ copy X S (g • s)

@[reassoc (attr := simp)]
theorem copy_actionMap (g : G) (s : S) :
    copy X S s ≫ actionMap X S g = X.ρ g ≫ copy X S (g • s) :=
  Cofan.IsColimit.fac _ _ s

theorem actionMap_one : actionMap X S 1 = 𝟙 _ :=
  copies_hom_ext fun s => by
    rw [copy_actionMap, Action.ρ_one, one_smul, Category.id_comp, Category.comp_id]

theorem actionMap_mul (g k : G) :
    actionMap X S (g * k) = actionMap X S k ≫ actionMap X S g :=
  copies_hom_ext fun s => by
    rw [copy_actionMap, copy_actionMap_assoc, copy_actionMap, ← Category.assoc,
      InducedSpace.ρ_comp, mul_smul]

/-- Berkovich's space `X_Σ` for `Σ = S`, with its action of `G`. -/
abbrev setInduced : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G where
  V := (copies X S).pt
  ρ :=
    { toFun := actionMap X S
      map_one' := actionMap_one X S
      map_mul' := actionMap_mul X S }

@[simp]
theorem setInduced_ρ (g : G) : (setInduced X S).ρ g = actionMap X S g := rfl

/-! ## Functoriality in the `G`-set -/

variable {S} {T U : Type z} [MulAction G T] [MulAction G U]

/-- The morphism `X_S → X_T` of a `G`-map `f : S → T`: the copy indexed by `s` goes identically
to the copy indexed by `f s`. -/
def mapHom (f : S →[G] T) : (copies X S).pt ⟶ (copies X T).pt :=
  Cofan.IsColimit.desc (isColimitCopies X S) fun s => copy X T (f s)

@[reassoc (attr := simp)]
theorem copy_mapHom (f : S →[G] T) (s : S) : copy X S s ≫ mapHom X f = copy X T (f s) :=
  Cofan.IsColimit.fac _ _ s

theorem actionMap_mapHom (f : S →[G] T) (g : G) :
    actionMap X S g ≫ mapHom X f = mapHom X f ≫ actionMap X T g :=
  copies_hom_ext fun s => by
    rw [copy_actionMap_assoc, copy_mapHom, copy_mapHom_assoc, copy_actionMap, map_smul]

/-- The `G`-morphism `X_S → X_T` of a `G`-map `S → T`. -/
def map (f : S →[G] T) : setInduced X S ⟶ setInduced X T where
  hom := mapHom X f
  comm g := actionMap_mapHom X f g

@[simp]
theorem map_hom (f : S →[G] T) : (map X f).hom = mapHom X f := rfl

theorem map_id : map X (MulActionHom.id G : S →[G] S) = 𝟙 (setInduced X S) :=
  Action.hom_ext _ _ (copies_hom_ext fun s => by
    rw [map_hom, copy_mapHom, Action.id_hom, Category.comp_id]
    rfl)

theorem map_comp (f : S →[G] T) (f' : T →[G] U) :
    map X (f'.comp f) = map X f ≫ map X f' :=
  Action.hom_ext _ _ (copies_hom_ext fun s => by
    rw [map_hom, copy_mapHom, Action.comp_hom, map_hom, map_hom, copy_mapHom_assoc,
      copy_mapHom]
    rfl)

/-! ## The projection `X_S → X` -/

variable (S)

theorem actionMap_projectionHom (g : G) :
    actionMap X S g ≫ projectionHom X S = projectionHom X S ≫ X.ρ g :=
  copies_hom_ext fun s => by
    rw [copy_actionMap_assoc, copy_projectionHom, copy_projectionHom_assoc, Category.comp_id]

/-- The projection `X_S → X`, a `G`-morphism. -/
def projection : setInduced X S ⟶ X where
  hom := projectionHom X S
  comm g := actionMap_projectionHom X S g

@[simp]
theorem projection_hom : (projection X S).hom = projectionHom X S := rfl

variable {S}

@[reassoc (attr := simp)]
theorem map_projection (f : S →[G] T) : map X f ≫ projection X T = projection X S :=
  Action.hom_ext _ _ (copies_hom_ext fun s => by
    rw [Action.comp_hom, map_hom, projection_hom, projection_hom, copy_mapHom_assoc,
      copy_projectionHom, copy_projectionHom])

/-! ## Comparison with the induced space of 1.1.2 -/

variable (N : Subgroup G)

/-- The underlying morphism of the comparison from the induced space of 1.1.2 of the restriction
of `X` to `N` to the space of the `G`-set `G ⧸ N` (both have the same underlying disjoint union
of copies): on the copy indexed by `c` it is the action of the representative `c.out`. -/
def inducedIsoHom : (copies X (G ⧸ N)).pt ⟶ (copies X (G ⧸ N)).pt :=
  Cofan.IsColimit.desc (isColimitCopies X (G ⧸ N)) fun c => X.ρ c.out ≫ copy X (G ⧸ N) c

/-- The inverse of `inducedIsoHom`. -/
def inducedIsoInv : (copies X (G ⧸ N)).pt ⟶ (copies X (G ⧸ N)).pt :=
  Cofan.IsColimit.desc (isColimitCopies X (G ⧸ N)) fun c => X.ρ c.out⁻¹ ≫ copy X (G ⧸ N) c

@[reassoc (attr := simp)]
theorem copy_inducedIsoHom (c : G ⧸ N) :
    copy X (G ⧸ N) c ≫ inducedIsoHom X N = X.ρ c.out ≫ copy X (G ⧸ N) c :=
  Cofan.IsColimit.fac _ _ c

@[reassoc (attr := simp)]
theorem copy_inducedIsoInv (c : G ⧸ N) :
    copy X (G ⧸ N) c ≫ inducedIsoInv X N = X.ρ c.out⁻¹ ≫ copy X (G ⧸ N) c :=
  Cofan.IsColimit.fac _ _ c

theorem inducedIsoHom_inv : inducedIsoHom X N ≫ inducedIsoInv X N = 𝟙 _ :=
  copies_hom_ext fun c => by
    rw [copy_inducedIsoHom_assoc, copy_inducedIsoInv, InducedSpace.ρ_comp_assoc, inv_mul_cancel,
      Action.ρ_one, Category.id_comp, Category.comp_id]

theorem inducedIsoInv_hom : inducedIsoInv X N ≫ inducedIsoHom X N = 𝟙 _ :=
  copies_hom_ext fun c => by
    rw [copy_inducedIsoInv_assoc, copy_inducedIsoHom, InducedSpace.ρ_comp_assoc, mul_inv_cancel,
      Action.ρ_one, Category.id_comp, Category.comp_id]

theorem inducedActionMap_inducedIsoHom (g : G) :
    InducedSpace.actionMap N ((Action.res _ N.subtype).obj X) g ≫ inducedIsoHom X N =
      inducedIsoHom X N ≫ actionMap X (G ⧸ N) g :=
  copies_hom_ext (X := X) (S := G ⧸ N) fun c => by
    have e := InducedSpace.copy_actionMap_assoc N ((Action.res _ N.subtype).obj X) g c
      (inducedIsoHom X N)
    refine e.trans ?_
    change X.ρ (correction N g c : G) ≫ copy X (G ⧸ N) (g • c) ≫ inducedIsoHom X N = _
    rw [copy_inducedIsoHom, copy_inducedIsoHom_assoc, copy_actionMap, InducedSpace.ρ_comp_assoc,
      InducedSpace.ρ_comp_assoc, ← correction_spec]

/-- Berkovich 1996, p.4: for a subgroup `N`, the space `X_{G/N}` of the `G`-set `G ⧸ N` is the
induced space of 1.1.2 of the restriction of `X` to `N`. -/
def inducedIso :
    InducedSpace.inducedAction N ((Action.res _ N.subtype).obj X) ≅ setInduced X (G ⧸ N) :=
  Action.mkIso
    { hom := inducedIsoHom X N
      inv := inducedIsoInv X N
      hom_inv_id := inducedIsoHom_inv X N
      inv_hom_id := inducedIsoInv_hom X N }
    (inducedActionMap_inducedIsoHom X N)

@[simp]
theorem inducedIso_hom_hom : (inducedIso X N).hom.hom = inducedIsoHom X N := rfl

/-- Under the comparison, the projection `X_{G/N} → X` is the extension of the identity of the
restriction of `X` (the morphism `ϕ'` of 1.1.2 for `ϕ = 1`). -/
theorem inducedIso_hom_projection :
    (inducedIso X N).hom ≫ projection X (G ⧸ N) =
      InducedSpace.lift N (𝟙 ((Action.res _ N.subtype).obj X)) :=
  Action.hom_ext _ _ (copies_hom_ext (X := X) (S := G ⧸ N) fun c => by
    change copy X (G ⧸ N) c ≫ inducedIsoHom X N ≫ projectionHom X (G ⧸ N) =
      copy X (G ⧸ N) c ≫
        InducedSpace.liftHom (X := (Action.res _ N.subtype).obj X) (Y := X) N (𝟙 X.V)
    rw [copy_inducedIsoHom_assoc, copy_projectionHom, Category.comp_id]
    exact ((InducedSpace.copy_liftHom (X := (Action.res _ N.subtype).obj X) (Y := X) N (𝟙 _)
      c).trans (Category.id_comp _)).symm)

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
