import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Langlands.Topology.GroupAction.DiscreteOperatorGroup
import Langlands.Topology.Category.TopologicalGroup
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-! # Berkovich's category `𝒜n^op` of analytic spaces with operators: the fixed-`K`, `K`-linear
part -/

noncomputable section

universe u v w z

open CategoryTheory

namespace Langlands

namespace Topology.TopologicalGroup

/-- The trivial topological group `{1}`. -/
abbrev trivial : TopologicalGroup.{z} :=
  of PUnit.{z + 1}

/-- `G_d`: the group of `G` with the discrete topology (the Library's
`Topology.DiscreteOperatorGroup`). -/
abbrev discrete (G : TopologicalGroup.{z}) : TopologicalGroup.{z} :=
  of (DiscreteOperatorGroup G.carrier)

/-- The identity map `G_d → G`, a continuous homomorphism. -/
abbrev fromDiscrete (G : TopologicalGroup.{z}) : discrete G ⟶ G :=
  DiscreteOperatorGroup.toOriginal G.carrier

/-- Conjugation `g' ↦ g g' g⁻¹`, a continuous homomorphism. -/
def conj {G : TopologicalGroup.{z}} (g : G.carrier) : G ⟶ G where
  toMonoidHom := (MulAut.conj g).toMonoidHom
  continuous_toFun := by
    change Continuous fun x : G.carrier => g * x * g⁻¹
    fun_prop

@[simp]
theorem conj_apply {G : TopologicalGroup.{z}} (g x : G.carrier) : conj g x = g * x * g⁻¹ :=
  rfl

end Topology.TopologicalGroup

namespace Analytic.SaturatedAtlasPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Berkovich's analytic spaces with operators `X(G)` over the fixed field `K`: a topological
group `G` and a `G`-space `X` in the Library's sense, a Hausdorff `K`-analytic space with a
continuous action of `G` by `K`-linear automorphisms. -/
structure SpaceWithOperators where
  /-- The topological group `G` of operators. -/
  group : Topology.TopologicalGroup.{z}
  /-- The `G`-space `X`. -/
  space : GSpace.{u, v, w} K group.carrier

namespace SpaceWithOperators

variable {K}

/-- Berkovich's morphisms `Y(H) → X(G)` over the fixed field `K`: a continuous homomorphism
`ν : H → G` and a `K`-linear morphism of analytic spaces `φ : Y → X` compatible with `ν`, that is
`φ ∘ h = ν(h) ∘ φ`. -/
@[ext]
structure Hom (Y X : SpaceWithOperators.{u, v, w, z} K) where
  /-- The continuous homomorphism `ν : H → G`. -/
  groupHom : Y.group ⟶ X.group
  /-- The `K`-linear morphism of analytic spaces `φ : Y → X`. -/
  hom : Y.space.obj.V ⟶ X.space.obj.V
  comm : ∀ h : Y.group.carrier, Y.space.obj.ρ h ≫ hom = hom ≫ X.space.obj.ρ (groupHom h)

/-- The identity morphism of `X(G)`. -/
def Hom.id (X : SpaceWithOperators.{u, v, w, z} K) : Hom X X where
  groupHom := 𝟙 X.group
  hom := 𝟙 _
  comm _ := by
    rw [Category.comp_id, Category.id_comp]
    rfl

/-- The composition of morphisms of spaces with operators. -/
def Hom.comp {Z Y X : SpaceWithOperators.{u, v, w, z} K} (f : Hom Z Y) (g : Hom Y X) :
    Hom Z X where
  groupHom := f.groupHom ≫ g.groupHom
  hom := f.hom ≫ g.hom
  comm h := by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc]
    rfl

/-- The fixed-`K`, `K`-linear part of Berkovich's category `𝒜n^op` of analytic spaces with
operators. -/
instance : Category (SpaceWithOperators.{u, v, w, z} K) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.groupHom) (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.groupHom) (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.groupHom g.groupHom h.groupHom)
    (Category.assoc f.hom g.hom h.hom)

@[ext]
theorem hom_ext {Y X : SpaceWithOperators.{u, v, w, z} K} {f g : Y ⟶ X}
    (hgroup : f.groupHom = g.groupHom) (hhom : f.hom = g.hom) : f = g :=
  Hom.ext hgroup hhom

@[simp]
theorem id_groupHom (X : SpaceWithOperators.{u, v, w, z} K) :
    Hom.groupHom (𝟙 X) = 𝟙 X.group :=
  rfl

@[simp]
theorem id_hom (X : SpaceWithOperators.{u, v, w, z} K) : Hom.hom (𝟙 X) = 𝟙 X.space.obj.V :=
  rfl

@[simp]
theorem comp_groupHom {Z Y X : SpaceWithOperators.{u, v, w, z} K} (f : Z ⟶ Y) (g : Y ⟶ X) :
    Hom.groupHom (f ≫ g) = f.groupHom ≫ g.groupHom :=
  rfl

@[simp]
theorem comp_hom {Z Y X : SpaceWithOperators.{u, v, w, z} K} (f : Z ⟶ Y) (g : Y ⟶ X) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

variable (K) in
/-- The group of operators: `X(G) ↦ G`, `(ν, φ) ↦ ν`. -/
@[simps]
def toTopologicalGroup :
    SpaceWithOperators.{u, v, w, z} K ⥤ Topology.TopologicalGroup.{z} where
  obj X := X.group
  map f := f.groupHom

variable (K) in
/-- The underlying analytic space: `X(G) ↦ X`, `(ν, φ) ↦ φ`. -/
@[simps]
def forget : SpaceWithOperators.{u, v, w, z} K ⥤ LocalizedCategory.{u, v, w} (K := K) where
  obj X := X.space.obj.V
  map f := f.hom

/-! ## The fibre over `G` -/

/-- A `G`-space `X` as the space with operators `X(G)`, and a `G`-morphism as a morphism whose
group homomorphism is the identity of `G`. -/
@[simps]
def ofGSpace (G : Topology.TopologicalGroup.{z}) :
    GSpace.{u, v, w} K G.carrier ⥤ SpaceWithOperators.{u, v, w, z} K where
  obj X := ⟨G, X⟩
  map f :=
    { groupHom := 𝟙 G
      hom := f.hom.hom
      comm := f.hom.comm }

instance (G : Topology.TopologicalGroup.{z}) : (ofGSpace (K := K) G).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (Action.hom_ext _ _ (congrArg Hom.hom h))

/-- The morphisms between `G`-spaces whose group homomorphism is the identity of `G` are the
`G`-morphisms: the fibre over `G` is the category of continuous `K`-linear `G`-actions on
Hausdorff `K`-analytic spaces, the fixed-`K` part of Berkovich's `G-𝒜n`. -/
theorem exists_ofGSpace_map_eq {G : Topology.TopologicalGroup.{z}}
    {X Y : GSpace.{u, v, w} K G.carrier}
    (f : (ofGSpace G).obj X ⟶ (ofGSpace G).obj Y) (hf : f.groupHom = 𝟙 G) :
    ∃ f' : X ⟶ Y, (ofGSpace G).map f' = f :=
  ⟨ObjectProperty.homMk
    { hom := f.hom
      comm := fun g => (f.comm g).trans (by rw [hf]; rfl) },
    hom_ext hf.symm rfl⟩

/-- `ofGSpace G` lands in the fibre over `G`. -/
theorem ofGSpace_comp_toTopologicalGroup (G : Topology.TopologicalGroup.{z}) :
    ofGSpace (K := K) G ⋙ toTopologicalGroup K = (Functor.const _).obj G :=
  rfl

/-! ## Cartesian morphisms: `𝒜n^op` is fibred over topological groups -/

/-- The restriction `X(H)` of `X(G)` along a continuous homomorphism `ν : H → G`. -/
abbrev resObj (X : SpaceWithOperators.{u, v, w, z} K) {H : Topology.TopologicalGroup.{z}}
    (ν : H ⟶ X.group) : SpaceWithOperators.{u, v, w, z} K :=
  ⟨H, (GSpace.res ν).obj X.space⟩

/-- The morphism `X(H) → X(G)` given by `ν : H → G` and the identity of `X`. -/
def resLift (X : SpaceWithOperators.{u, v, w, z} K) {H : Topology.TopologicalGroup.{z}}
    (ν : H ⟶ X.group) : resObj X ν ⟶ X where
  groupHom := ν
  hom := 𝟙 X.space.obj.V
  comm _ := (Category.comp_id _).trans (Category.id_comp _).symm

@[simp]
theorem resLift_groupHom (X : SpaceWithOperators.{u, v, w, z} K) {H : Topology.TopologicalGroup.{z}}
    (ν : H ⟶ X.group) : (resLift X ν).groupHom = ν :=
  rfl

@[simp]
theorem resLift_hom (X : SpaceWithOperators.{u, v, w, z} K) {H : Topology.TopologicalGroup.{z}}
    (ν : H ⟶ X.group) : (resLift X ν).hom = 𝟙 X.space.obj.V :=
  rfl

theorem isHomLift_iff {Y X : SpaceWithOperators.{u, v, w, z} K} (ν : Y.group ⟶ X.group)
    (f : Y ⟶ X) : (toTopologicalGroup K).IsHomLift ν f ↔ f.groupHom = ν :=
  ⟨fun h => (@IsHomLift.eq_of_isHomLift _ _ _ _ (toTopologicalGroup K) Y X ν f h).symm,
    fun h => by
    subst h
    exact IsHomLift.map (toTopologicalGroup K) f⟩

/-- `resLift X ν` is strongly cartesian over `ν`. -/
instance isStronglyCartesian_resLift (X : SpaceWithOperators.{u, v, w, z} K)
    {H : Topology.TopologicalGroup.{z}} (ν : H ⟶ X.group) :
    (toTopologicalGroup K).IsStronglyCartesian ν (resLift X ν) where
  toIsHomLift := (isHomLift_iff ν (resLift X ν)).2 rfl
  universal_property' {Y} g f hf := by
    have hfg : f.groupHom = g ≫ ν := (isHomLift_iff (g ≫ ν) f).1 hf
    let χ : Y ⟶ resObj X ν :=
      { groupHom := g
        hom := f.hom
        comm := fun h => (f.comm h).trans (by rw [hfg]; rfl) }
    refine ⟨χ, ⟨(isHomLift_iff g χ).2 rfl, hom_ext hfg.symm (Category.comp_id _)⟩, ?_⟩
    rintro χ' ⟨hχ', hχ'f⟩
    exact hom_ext ((isHomLift_iff g χ').1 hχ')
      ((Category.comp_id _).symm.trans (congrArg Hom.hom hχ'f))

/-- Berkovich: "The category `𝒜n^op` is a fibred category over the category of topological
groups", for its fixed-`K`, `K`-linear part. -/
instance : (toTopologicalGroup.{u, v, w, z} K).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun X _ ν =>
    ⟨resObj X ν, resLift X ν, isStronglyCartesian_resLift X ν⟩

/-! ## The action of `G` on `X(G)` and Berkovich's Example 1.1.3 -/

/-- The automorphism of `X(G)` given by `g ∈ G`: conjugation `g' ↦ g g' g⁻¹` on `G` and the
action of `g` on `X`. -/
def conjugation (X : SpaceWithOperators.{u, v, w, z} K) (g : X.group.carrier) : X ⟶ X where
  groupHom := Topology.TopologicalGroup.conj g
  hom := X.space.obj.ρ g
  comm h := by
    rw [← End.mul_def, ← End.mul_def, ← map_mul, ← map_mul, Topology.TopologicalGroup.conj_apply,
      inv_mul_cancel_right]

@[simp]
theorem conjugation_groupHom (X : SpaceWithOperators.{u, v, w, z} K) (g : X.group.carrier) :
    (conjugation X g).groupHom = Topology.TopologicalGroup.conj g :=
  rfl

@[simp]
theorem conjugation_hom (X : SpaceWithOperators.{u, v, w, z} K) (g : X.group.carrier) :
    (conjugation X g).hom = X.space.obj.ρ g :=
  rfl

theorem conjugation_one (X : SpaceWithOperators.{u, v, w, z} K) : conjugation X 1 = 𝟙 X :=
  hom_ext (Topology.TopologicalGroup.hom_ext fun x => by simp) (Action.ρ_one _)

theorem conjugation_mul (X : SpaceWithOperators.{u, v, w, z} K) (g g' : X.group.carrier) :
    conjugation X (g * g') = conjugation X g' ≫ conjugation X g :=
  hom_ext (Topology.TopologicalGroup.hom_ext fun x => by simp [mul_assoc])
    (map_mul X.space.obj.ρ g g')

/-- Berkovich: "the action of `G` on `X` extends to a natural action of `G` on `X(G)` for which
`ν_g(g') = g g' g⁻¹`." -/
def conjugationAction (X : SpaceWithOperators.{u, v, w, z} K) : X.group.carrier →* End X where
  toFun := conjugation X
  map_one' := conjugation_one X
  map_mul' := conjugation_mul X

/-- Berkovich's morphism `a : X(G_d) → X(G)` (Example 1.1.3), where `G_d` is `G` with the
discrete topology. -/
abbrev discreteLift (X : SpaceWithOperators.{u, v, w, z} K) :
    resObj X (Topology.TopologicalGroup.fromDiscrete X.group) ⟶ X :=
  resLift X (Topology.TopologicalGroup.fromDiscrete X.group)

/-- The underlying space `X = X({1})` of a space with operators, with the trivial group. -/
abbrev underlying (X : SpaceWithOperators.{u, v, w, z} K) : SpaceWithOperators.{u, v, w, z} K :=
  resObj X (1 : Topology.TopologicalGroup.trivial.carrier →ₜ* X.group.carrier)

/-- Berkovich's morphism `b : X → X(G)` (Example 1.1.3). -/
abbrev underlyingLift (X : SpaceWithOperators.{u, v, w, z} K) : underlying X ⟶ X :=
  resLift X (1 : Topology.TopologicalGroup.trivial.carrier →ₜ* X.group.carrier)

end SpaceWithOperators

end Analytic.SaturatedAtlasPresentation

end Langlands
