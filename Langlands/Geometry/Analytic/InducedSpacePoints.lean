import Langlands.Geometry.Analytic.InducedSpaceAdjunction
import Langlands.Geometry.Analytic.NearIdentityDomainRestriction

/-! # Points of disjoint unions and of induced analytic spaces

The underlying maps of the summand inclusions of the chosen disjoint union
`localizedSigmaCofan`, and of the structure maps of Berkovich's induced space `X_{G/H}`, on
points of the underlying topological spaces. -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Sigma

variable {J : Type z}

/-- The underlying map of the inclusion of a summand of the chosen disjoint union is the
sigma injection `x ↦ ⟨j, x⟩`. -/
theorem localizedSigmaCofan_inj_space_apply
    (Y : J → LocalizedCategory.{u, max z v, max z v} (K := K)) (j : J)
    (x : localizedSpaceFunctor.obj (Y j)) :
    localizedSpaceFunctor.map ((localizedSigmaCofan Y).inj j) x =
      (⟨j, x⟩ : (i : J) × localizedSpaceFunctor.obj (Y i)) :=
  numerator_point_eq_of_fraction_equation (nonemptyReplacementHom (presentationOf (Y j)))
    ((sigmaCofan fun j => presentationOf (Y j)).inj j) ((localizedSigmaCofan Y).inj j)
    (Localization.isoOfHom_hom_inv_id_assoc (L := localizationFunctor)
      (W := quasiIsomorphisms (K := K)) _ (isQuasiIso_nonemptyReplacementHom _) _) x

end Sigma

namespace InducedSpace

open PresentedAffinoidAlgebra.InducedAction (correction)

variable {G : Type z} [Group G] (H : Subgroup G)

section Copies

variable (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)

/-- The underlying map of the inclusion of the copy indexed by `c` is `x ↦ ⟨c, x⟩`. -/
theorem copy_space_apply (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (copy H X c) x =
      (⟨c, x⟩ : (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) :=
  localizedSigmaCofan_inj_space_apply (fun _ : G ⧸ H => X.V) c x

/-- The underlying map of the inclusion of the copy indexed by `c` is `Sigma.mk c`. -/
theorem copy_space_eq (c : G ⧸ H) :
    ⇑(localizedSpaceFunctor.map (copy H X c)) =
      Sigma.mk (β := fun _ : G ⧸ H => localizedSpaceFunctor.obj X.V) c :=
  funext (copy_space_apply H X c)

/-- The underlying map of the inclusion of a copy is injective. -/
theorem copy_space_injective (c : G ⧸ H) :
    Function.Injective (localizedSpaceFunctor.map (copy H X c)) := by
  rw [copy_space_eq]
  exact sigma_mk_injective

/-- The image of the copy indexed by `c` is the image of `Sigma.mk c`. -/
theorem range_copy_space (c : G ⧸ H) :
    Set.range (localizedSpaceFunctor.map (copy H X c)) =
      Set.range (Sigma.mk (β := fun _ : G ⧸ H => localizedSpaceFunctor.obj X.V) c) := by
  rw [copy_space_eq]
  rfl

/-- The action of `g` sends the point `⟨c, x⟩` to `⟨g • c, κ(g, c) • x⟩`. -/
theorem actionMap_space_apply (g : G) (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (actionMap H X g)
        (⟨c, x⟩ : (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) =
      (⟨g • c, localizedSpaceFunctor.map (X.ρ (correction H g c)).asHom x⟩ :
        (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) := by
  rw [← copy_space_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, copy_actionMap,
    Functor.map_comp, ConcreteCategory.comp_apply, copy_space_apply]

/-- The coset `c` indexing the copy of `X` that contains a point of `X_{G/H}`. -/
def pointCoset (p : localizedSpaceFunctor.obj (copies H X).pt) : G ⧸ H :=
  Sigma.fst (β := fun _ : G ⧸ H => localizedSpaceFunctor.obj X.V) p

@[simp]
theorem pointCoset_mk (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    pointCoset H X (⟨c, x⟩ : (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) = c :=
  rfl

@[simp]
theorem pointCoset_copy (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    pointCoset H X (localizedSpaceFunctor.map (copy H X c) x) = c := by
  rw [copy_space_apply, pointCoset_mk]

/-- A point lies in the copy indexed by `c` exactly when its coset is `c`. -/
theorem mem_range_copy_space_iff (c : G ⧸ H) (p : localizedSpaceFunctor.obj (copies H X).pt) :
    p ∈ Set.range (localizedSpaceFunctor.map (copy H X c)) ↔ pointCoset H X p = c := by
  constructor
  · rintro ⟨x, rfl⟩
    exact pointCoset_copy H X c x
  · intro h
    obtain ⟨d, x⟩ := p
    obtain rfl : d = c := h
    exact ⟨x, copy_space_apply H X d x⟩

/-- The image of each copy is open. -/
theorem isOpen_range_copy_space (c : G ⧸ H) :
    IsOpen (Set.range (localizedSpaceFunctor.map (copy H X c))) := by
  rw [range_copy_space]
  exact isOpen_range_sigmaMk

/-- The action of `g` sends the copy indexed by `c` into the copy indexed by `g • c`. -/
theorem pointCoset_actionMap (g : G) (p : localizedSpaceFunctor.obj (copies H X).pt) :
    pointCoset H X (localizedSpaceFunctor.map (actionMap H X g) p) = g • pointCoset H X p := by
  obtain ⟨c, x⟩ := p
  exact congrArg (pointCoset H X) (actionMap_space_apply H X g c x)

/-- The unit sends `x` to the point `⟨H, r⁻¹ • x⟩` of the copy indexed by the coset `H`, where
`r` is the chosen representative of that coset. -/
theorem unitHom_space_apply (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (unitHom H X) x =
      (⟨baseCoset H, localizedSpaceFunctor.map (X.ρ (baseRep H)⁻¹).asHom x⟩ :
        (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) := by
  rw [unitHom, Functor.map_comp, ConcreteCategory.comp_apply, copy_space_apply]

@[simp]
theorem pointCoset_unitHom (x : localizedSpaceFunctor.obj X.V) :
    pointCoset H X (localizedSpaceFunctor.map (unitHom H X) x) = baseCoset H := by
  rw [unitHom_space_apply, pointCoset_mk]

end Copies

/-- The induced morphism `f_{G/H}` sends the point `⟨c, x⟩` to `⟨c, f x⟩`. -/
theorem inductionFunctor_map_space_apply
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X')
    (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map ((inductionFunctor H).map f).hom
        (⟨c, x⟩ : (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) =
      (⟨c, localizedSpaceFunctor.map f.hom x⟩ :
        (_ : G ⧸ H) × localizedSpaceFunctor.obj X'.V) := by
  rw [← copy_space_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    copy_inductionFunctor_map, Functor.map_comp, ConcreteCategory.comp_apply, copy_space_apply]

/-- The induced morphism `f_{G/H}` maps each copy into the copy with the same index. -/
@[simp]
theorem pointCoset_inductionFunctor_map
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X')
    (p : localizedSpaceFunctor.obj (copies H X).pt) :
    pointCoset H X' (localizedSpaceFunctor.map ((inductionFunctor H).map f).hom p) =
      pointCoset H X p := by
  obtain ⟨c, x⟩ := p
  exact congrArg (pointCoset H X') (inductionFunctor_map_space_apply H f c x)

/-- The extension `X_{G/H} → Y` of `f : X → Y` sends the point `⟨c, x⟩` to `c.out • f x`. -/
theorem liftHom_space_apply {X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
    {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G} (f : X.V ⟶ Y.V)
    (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (liftHom H f)
        (⟨c, x⟩ : (_ : G ⧸ H) × localizedSpaceFunctor.obj X.V) =
      localizedSpaceFunctor.map (Y.ρ c.out).asHom (localizedSpaceFunctor.map f x) := by
  rw [← copy_space_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, copy_liftHom,
    Functor.map_comp, ConcreteCategory.comp_apply]

end InducedSpace

end Langlands.Analytic.SaturatedAtlasPresentation
