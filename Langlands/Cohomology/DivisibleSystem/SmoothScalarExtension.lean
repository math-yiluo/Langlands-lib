import Langlands.Cohomology.DivisibleSystem.ScalarExtension

/-!
# Extension and restriction of scalars of smooth representations

For an algebra `R → S` of commutative rings and a group `G` with a topology, extension of scalars
`V ↦ S ⊗[R] V` and restriction of scalars along `algebraMap R S` preserve smoothness. Hence the
functors `repExtendScalars` and `repRestrictScalars` of `ScalarExtension.lean` and their
adjunction restrict to the published categories `SmoothRep` of smooth representations, with the
same underlying representations, maps, unit and counit. See `SmoothScalarExtension.md`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory TensorProduct

universe w uR uS uG

attribute [local instance] restrictScalarsModule

section Smoothness

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {G : Type uG} [Group G]

/-- A subgroup fixing `v` fixes every pure tensor `s ⊗ v`. -/
theorem tmul_mem_fixedVectors_baseChangeRepresentation {V : Type w} [AddCommGroup V]
    [Module R V] (ρ : Representation R G V) (K : Subgroup G) (s : S) {v : V}
    (hv : v ∈ fixedVectors ρ K) :
    s ⊗ₜ[R] v ∈ fixedVectors (baseChangeRepresentation S ρ) K := by
  intro k
  change s ⊗ₜ[R] ρ (k : G) v = s ⊗ₜ[R] v
  exact congrArg (s ⊗ₜ[R] ·) (hv k)

variable (R)

/-- An element of the restriction of scalars is fixed by a subgroup exactly when the
corresponding element of the original representation is. -/
theorem restrictScalarsRepresentation_fixed_iff {W : Type w} [AddCommGroup W] [Module S W]
    (σ : Representation S G W) (K : Subgroup G) (x : RestrictScalars R S W) :
    (∀ k : K, restrictScalarsRepresentation R S σ (k : G) x = x) ↔
      ∀ k : K,
        σ (k : G) (RestrictScalars.addEquiv R S W x) = RestrictScalars.addEquiv R S W x := by
  change (∀ k : K, (RestrictScalars.addEquiv R S W).symm
      (σ (k : G) (RestrictScalars.addEquiv R S W x)) = x) ↔ _
  simp only [AddEquiv.symm_apply_eq]

variable [TopologicalSpace G]

variable {R} in
/-- Extension of scalars preserves smoothness. Every element of `S ⊗[R] V` is a finite sum of
pure tensors; `s ⊗ v` is fixed by an open subgroup fixing `v`, and a sum of smooth vectors is
fixed by the intersection of open subgroups fixing its summands. -/
theorem isSmooth_baseChangeRepresentation {V : Type w} [AddCommGroup V] [Module R V]
    {ρ : Representation R G V} (hρ : IsSmooth ρ) : IsSmooth (baseChangeRepresentation S ρ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul s v =>
    obtain ⟨K, hK⟩ := hρ v
    exact ⟨K, tmul_mem_fixedVectors_baseChangeRepresentation S ρ K.toSubgroup s hK⟩
  | add x y hx hy => exact isSmoothVector_add hx hy

/-- Restriction of scalars preserves and reflects smoothness: the group acts on the same
additive group by the same maps. -/
theorem isSmooth_restrictScalarsRepresentation_iff {W : Type w} [AddCommGroup W] [Module S W]
    (σ : Representation S G W) : IsSmooth (restrictScalarsRepresentation R S σ) ↔ IsSmooth σ := by
  constructor
  · intro h w
    obtain ⟨K, hK⟩ := h ((RestrictScalars.addEquiv R S W).symm w)
    refine ⟨K, fun k => ?_⟩
    have hw := (restrictScalarsRepresentation_fixed_iff R S σ K.toSubgroup
      ((RestrictScalars.addEquiv R S W).symm w)).1 hK k
    rwa [AddEquiv.apply_symm_apply] at hw
  · intro h x
    obtain ⟨K, hK⟩ := h (RestrictScalars.addEquiv R S W x)
    exact ⟨K, (restrictScalarsRepresentation_fixed_iff R S σ K.toSubgroup x).2 hK⟩

end Smoothness

section Functors

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (G : Type uG) [Group G] [TopologicalSpace G]

/-- Extension of scalars of smooth representations, `V ↦ S ⊗[R] V` with `g` acting by
`1 ⊗ g`: the functor `repExtendScalars` on the full subcategory of smooth representations. -/
def smoothRepExtendScalars : SmoothRep.{uR, uG, w} R G ⥤ SmoothRep.{uS, uG, max uS w} S G :=
  (smoothRepProperty.{uS, uG, max uS w} S G).lift (SmoothRep.toRep ⋙ repExtendScalars.{w} R S G)
    (fun V => isSmooth_baseChangeRepresentation S V.isSmooth)

/-- Restriction of scalars of smooth representations along `algebraMap R S`: the functor
`repRestrictScalars` on the full subcategory of smooth representations. -/
def smoothRepRestrictScalars : SmoothRep.{uS, uG, w} S G ⥤ SmoothRep.{uR, uG, w} R G :=
  (smoothRepProperty.{uR, uG, w} R G).lift (SmoothRep.toRep ⋙ repRestrictScalars.{w} R S G)
    (fun W => (isSmooth_restrictScalarsRepresentation_iff R S W.representation).2 W.isSmooth)

/-- The underlying algebraic representation of `smoothRepExtendScalars` is `repExtendScalars`. -/
theorem smoothRepExtendScalars_comp_toRep :
    smoothRepExtendScalars.{w} R S G ⋙ SmoothRep.toRep =
      SmoothRep.toRep ⋙ repExtendScalars.{w} R S G := rfl

/-- The underlying algebraic representation of `smoothRepRestrictScalars` is
`repRestrictScalars`. -/
theorem smoothRepRestrictScalars_comp_toRep :
    smoothRepRestrictScalars.{w} R S G ⋙ SmoothRep.toRep =
      SmoothRep.toRep ⋙ repRestrictScalars.{w} R S G := rfl

/-- `smoothRepExtendScalars_comp_toRep` as an isomorphism with identity components. -/
def smoothRepExtendScalarsToRepIso :
    smoothRepExtendScalars.{w} R S G ⋙ SmoothRep.toRep ≅
      SmoothRep.toRep ⋙ repExtendScalars.{w} R S G :=
  Iso.refl _

/-- `smoothRepRestrictScalars_comp_toRep` as an isomorphism with identity components. -/
def smoothRepRestrictScalarsToRepIso :
    smoothRepRestrictScalars.{w} R S G ⋙ SmoothRep.toRep ≅
      SmoothRep.toRep ⋙ repRestrictScalars.{w} R S G :=
  Iso.refl _

@[simp]
theorem smoothRepExtendScalars_obj_representation_tmul (V : SmoothRep.{uR, uG, w} R G) (g : G)
    (s : S) (v : V) :
    ((smoothRepExtendScalars.{w} R S G).obj V).representation g (s ⊗ₜ[R] v) =
      s ⊗ₜ[R] V.representation g v := rfl

@[simp]
theorem smoothRepExtendScalars_map_tmul {V W : SmoothRep.{uR, uG, w} R G} (f : V ⟶ W) (s : S)
    (v : V) :
    SmoothRep.hom ((smoothRepExtendScalars.{w} R S G).map f) (s ⊗ₜ[R] v) =
      s ⊗ₜ[R] SmoothRep.hom f v := rfl

theorem smoothRepRestrictScalars_obj_representation_apply (W : SmoothRep.{uS, uG, w} S G)
    (g : G) (x : RestrictScalars R S W) :
    ((smoothRepRestrictScalars.{w} R S G).obj W).representation g x =
      (RestrictScalars.addEquiv R S W).symm
        (W.representation g (RestrictScalars.addEquiv R S W x)) := rfl

theorem smoothRepRestrictScalars_map_apply {W W' : SmoothRep.{uS, uG, w} S G} (f : W ⟶ W')
    (x : RestrictScalars R S W) :
    SmoothRep.hom ((smoothRepRestrictScalars.{w} R S G).map f) x =
      (RestrictScalars.addEquiv R S W').symm
        (SmoothRep.hom f (RestrictScalars.addEquiv R S W x)) := rfl

instance smoothRepExtendScalars_additive : (smoothRepExtendScalars.{w} R S G).Additive where
  map_add {_ _ f g} :=
    ObjectProperty.hom_ext _ ((repExtendScalars.{w} R S G).map_add (f := f.hom) (g := g.hom))

instance smoothRepRestrictScalars_additive : (smoothRepRestrictScalars.{w} R S G).Additive where
  map_add := rfl

/-- The unit of extension and restriction of scalars of smooth representations, `v ↦ 1 ⊗ v`:
the components of `repExtendScalarsUnit`. -/
def smoothRepExtendScalarsUnit :
    𝟭 (SmoothRep.{uR, uG, max uS w} R G) ⟶
      smoothRepExtendScalars.{max uS w} R S G ⋙ smoothRepRestrictScalars R S G where
  app V := ObjectProperty.homMk ((repExtendScalarsUnit.{w} R S G).app V.obj)
  naturality _ _ f :=
    ObjectProperty.hom_ext _ ((repExtendScalarsUnit.{w} R S G).naturality f.hom)

/-- The counit of extension and restriction of scalars of smooth representations,
`s ⊗ w ↦ s • w`: the components of `repExtendScalarsCounit`. -/
def smoothRepExtendScalarsCounit :
    smoothRepRestrictScalars R S G ⋙ smoothRepExtendScalars.{max uS w} R S G ⟶
      𝟭 (SmoothRep.{uS, uG, max uS w} S G) where
  app W := ObjectProperty.homMk ((repExtendScalarsCounit.{w} R S G).app W.obj)
  naturality _ _ f :=
    ObjectProperty.hom_ext _ ((repExtendScalarsCounit.{w} R S G).naturality f.hom)

theorem toRep_map_smoothRepExtendScalarsUnit_app (V : SmoothRep.{uR, uG, max uS w} R G) :
    SmoothRep.toRep.map ((smoothRepExtendScalarsUnit.{w} R S G).app V) =
      (repExtendScalarsUnit.{w} R S G).app V.obj := rfl

theorem toRep_map_smoothRepExtendScalarsCounit_app (W : SmoothRep.{uS, uG, max uS w} S G) :
    SmoothRep.toRep.map ((smoothRepExtendScalarsCounit.{w} R S G).app W) =
      (repExtendScalarsCounit.{w} R S G).app W.obj := rfl

@[simp]
theorem smoothRepExtendScalarsUnit_app_apply (V : SmoothRep.{uR, uG, max uS w} R G) (v : V) :
    SmoothRep.hom ((smoothRepExtendScalarsUnit.{w} R S G).app V) v =
      (RestrictScalars.addEquiv R S (S ⊗[R] V)).symm (1 ⊗ₜ v) := rfl

@[simp]
theorem smoothRepExtendScalarsCounit_app_tmul (W : SmoothRep.{uS, uG, max uS w} S G) (s : S)
    (x : RestrictScalars R S W) :
    SmoothRep.hom ((smoothRepExtendScalarsCounit.{w} R S G).app W) (s ⊗ₜ x) =
      s • RestrictScalars.addEquiv R S W x := rfl

/-- Extension of scalars of smooth representations is left adjoint to restriction of scalars,
with unit `smoothRepExtendScalarsUnit` and counit `smoothRepExtendScalarsCounit`; the triangle
identities are those of `repExtendScalarsAdjunction`. -/
def smoothRepExtendScalarsAdjunction :
    smoothRepExtendScalars.{max uS w} R S G ⊣ smoothRepRestrictScalars R S G :=
  Adjunction.mkOfUnitCounit
    { unit := smoothRepExtendScalarsUnit R S G
      counit := smoothRepExtendScalarsCounit R S G
      left_triangle := by
        refine NatTrans.ext (funext fun V => ObjectProperty.hom_ext _ ?_)
        change (repExtendScalars.{max uS w} R S G).map ((repExtendScalarsUnit.{w} R S G).app V.obj)
            ≫ 𝟙 _ ≫ (repExtendScalarsCounit.{w} R S G).app
              ((repExtendScalars.{max uS w} R S G).obj V.obj) = 𝟙 _
        rw [Category.id_comp]
        exact (repExtendScalarsAdjunction.{w} R S G).left_triangle_components V.obj
      right_triangle := by
        refine NatTrans.ext (funext fun W => ObjectProperty.hom_ext _ ?_)
        change (repExtendScalarsUnit.{w} R S G).app ((repRestrictScalars R S G).obj W.obj)
            ≫ 𝟙 _ ≫ (repRestrictScalars R S G).map
              ((repExtendScalarsCounit.{w} R S G).app W.obj) = 𝟙 _
        rw [Category.id_comp]
        exact (repExtendScalarsAdjunction.{w} R S G).right_triangle_components W.obj }

@[simp]
theorem smoothRepExtendScalarsAdjunction_unit :
    (smoothRepExtendScalarsAdjunction.{w} R S G).unit = smoothRepExtendScalarsUnit R S G := rfl

@[simp]
theorem smoothRepExtendScalarsAdjunction_counit :
    (smoothRepExtendScalarsAdjunction.{w} R S G).counit = smoothRepExtendScalarsCounit R S G :=
  rfl

/-- The adjunction bijection of smooth representations is the bijection of
`repExtendScalarsAdjunction` on underlying morphisms. -/
theorem smoothRepExtendScalarsAdjunction_homEquiv_hom (V : SmoothRep.{uR, uG, max uS w} R G)
    (W : SmoothRep.{uS, uG, max uS w} S G) (f : (smoothRepExtendScalars R S G).obj V ⟶ W) :
    ((smoothRepExtendScalarsAdjunction.{w} R S G).homEquiv V W f).hom =
      (repExtendScalarsAdjunction.{w} R S G).homEquiv V.obj W.obj f.hom := rfl

/-- The inverse adjunction bijection of smooth representations is the inverse bijection of
`repExtendScalarsAdjunction` on underlying morphisms. -/
theorem smoothRepExtendScalarsAdjunction_homEquiv_symm_hom (V : SmoothRep.{uR, uG, max uS w} R G)
    (W : SmoothRep.{uS, uG, max uS w} S G) (f : V ⟶ (smoothRepRestrictScalars R S G).obj W) :
    (((smoothRepExtendScalarsAdjunction.{w} R S G).homEquiv V W).symm f).hom =
      ((repExtendScalarsAdjunction.{w} R S G).homEquiv V.obj W.obj).symm f.hom := rfl

variable {ι : Type*} (c : ComplexShape ι)

/-- Extension of scalars applied degreewise to complexes of smooth representations. -/
abbrev smoothRepExtendScalarsComplex :
    HomologicalComplex (SmoothRep.{uR, uG, w} R G) c ⥤
      HomologicalComplex (SmoothRep.{uS, uG, max uS w} S G) c :=
  (smoothRepExtendScalars R S G).mapHomologicalComplex c

/-- Restriction of scalars applied degreewise to complexes of smooth representations. -/
abbrev smoothRepRestrictScalarsComplex :
    HomologicalComplex (SmoothRep.{uS, uG, w} S G) c ⥤
      HomologicalComplex (SmoothRep.{uR, uG, w} R G) c :=
  (smoothRepRestrictScalars R S G).mapHomologicalComplex c

/-- The degreewise unit `v ↦ 1 ⊗ v`, a natural chain map from a complex of smooth
representations to the restriction of scalars of its extension of scalars. -/
def smoothRepExtendScalarsComplexUnit :
    𝟭 (HomologicalComplex (SmoothRep.{uR, uG, max uS w} R G) c) ⟶
      smoothRepExtendScalarsComplex R S G c ⋙ smoothRepRestrictScalarsComplex R S G c where
  app K :=
    { f i := (smoothRepExtendScalarsUnit R S G).app (K.X i)
      comm' i j _ := ((smoothRepExtendScalarsUnit R S G).naturality (K.d i j)).symm }
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun i => (smoothRepExtendScalarsUnit R S G).naturality (φ.f i)

end Functors

end Langlands.Cohomology
