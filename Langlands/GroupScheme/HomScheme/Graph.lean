import Langlands.GroupScheme.Products
import Langlands.GroupScheme.RepresentedSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Actual graphs of group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G K : GroupScheme S}

/-- The actual graph homomorphism into the product group scheme. -/
def graphHom (f : H ⟶ G) : H ⟶ H ⊗ G :=
  lift (𝟙 H) f

@[reassoc (attr := simp)]
theorem graphHom_fst (f : H ⟶ G) : graphHom f ≫ fst H G = 𝟙 H := by
  simp [graphHom]

@[reassoc (attr := simp)]
theorem graphHom_snd (f : H ⟶ G) : graphHom f ≫ snd H G = f := by
  simp [graphHom]

@[reassoc (attr := simp)]
theorem graphHom_hom_fst (f : H ⟶ G) :
    (graphHom f).hom.hom ≫ fst H.X G.X = 𝟙 H.X := by
  change (graphHom f ≫ fst H G).hom.hom = (𝟙 H : H ⟶ H).hom.hom
  rw [graphHom_fst]

@[reassoc (attr := simp)]
theorem graphHom_hom_snd (f : H ⟶ G) :
    (graphHom f).hom.hom ≫ snd H.X G.X = f.hom.hom := by
  change (graphHom f ≫ snd H G).hom.hom = f.hom.hom
  rw [graphHom_snd]

instance (f : H ⟶ G) : Mono (graphHom f).hom.hom where
  right_cancellation a b h := by
    have hp := congrArg (fun t => t ≫ fst H.X G.X) h
    simpa only [Category.assoc, graphHom_hom_fst, Category.comp_id] using hp

/-- A graph is closed when the target group scheme is separated over the base. -/
theorem isClosedImmersion_graphHom (f : H ⟶ G) [IsSeparated G.X.hom] :
    IsClosedImmersion (graphHom f).hom.hom.left := by
  have hp : IsSeparated (fst H.X G.X).left := by
    change IsSeparated (pullback.fst H.X.hom G.X.hom)
    infer_instance
  have he : (graphHom f).hom.hom.left ≫ (fst H.X G.X).left = 𝟙 _ := by
    change ((graphHom f).hom.hom ≫ fst H.X G.X).left =
      (𝟙 H.X : H.X ⟶ H.X).left
    rw [graphHom_hom_fst]
  have : IsClosedImmersion ((graphHom f).hom.hom.left ≫ (fst H.X G.X).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ (fst H.X G.X).left

/-- The graph as an actual subgroup functor on all test schemes. -/
def graph (f : H ⟶ G) : SubgroupFunctor (H ⊗ G) :=
  SubgroupFunctor.range (graphHom f)

/-- The actual graph homomorphism represents its graph subgroup functor. -/
theorem graph_isRepresentedBy (f : H ⟶ G) :
    (graph f).IsRepresentedBy (graphHom f) :=
  ⟨inferInstance, rfl⟩

/-- Membership in a graph is the actual equality between its two projections. -/
theorem mem_graph_iff (f : H ⟶ G) {T : Over S} (x : T ⟶ (H ⊗ G).X) :
    x ∈ (graph f).carrier T ↔
      x ≫ snd H.X G.X = x ≫ fst H.X G.X ≫ f.hom.hom := by
  change (∃ y : T ⟶ H.X, y ≫ (graphHom f).hom.hom = x) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro h
    refine ⟨x ≫ fst H.X G.X, ?_⟩
    apply hom_ext
    · simp
    · simpa using h.symm

/-- A homomorphism is determined by its graph on all test schemes. -/
theorem graph_injective : Function.Injective (graph (H := H) (G := G)) := by
  intro f g h
  have hm : (graphHom f).hom.hom ∈ (graph g).carrier H.X := by
    rw [← h]
    change ∃ y : H.X ⟶ H.X, y ≫ (graphHom f).hom.hom = (graphHom f).hom.hom
    exact ⟨𝟙 _, by simp⟩
  have he := (mem_graph_iff g _).mp hm
  apply Grp.hom_ext
  simpa only [← Category.assoc, graphHom_hom_snd, graphHom_hom_fst,
    Category.id_comp] using he

/-- A subgroup functor is a graph if it has an actual representative whose
first projection to `H` is an isomorphism of group schemes. -/
def IsGraph (F : SubgroupFunctor (H ⊗ G)) : Prop :=
  ∃ (K : GroupScheme S) (j : K ⟶ H ⊗ G),
    F.IsRepresentedBy j ∧ IsIso (j ≫ fst H G)

/-- Every actual homomorphism supplies such a graph subgroup. -/
theorem isGraph_graph (f : H ⟶ G) : IsGraph (graph f) := by
  refine ⟨H, graphHom f, graph_isRepresentedBy f, ?_⟩
  rw [graphHom_fst]
  infer_instance

/-- Recover the homomorphism from an actual representative with invertible
first projection. -/
def homOfGraphRepresentative (j : K ⟶ H ⊗ G) [IsIso (j ≫ fst H G)] : H ⟶ G :=
  inv (j ≫ fst H G) ≫ j ≫ snd H G

/-- The recovered graph is the original inclusion reparametrized by its first
projection. -/
theorem graphHom_homOfGraphRepresentative (j : K ⟶ H ⊗ G)
    [IsIso (j ≫ fst H G)] :
    graphHom (homOfGraphRepresentative j) = inv (j ≫ fst H G) ≫ j := by
  apply hom_ext
  · simp [Category.assoc]
  · simp [homOfGraphRepresentative, Category.assoc]

/-- Recovery gives exactly the original subgroup functor, rather than only an
abstractly isomorphic group scheme. -/
theorem graph_homOfGraphRepresentative (j : K ⟶ H ⊗ G)
    [IsIso (j ≫ fst H G)] :
    graph (homOfGraphRepresentative j) = SubgroupFunctor.range j := by
  rw [graph, graphHom_homOfGraphRepresentative]
  exact SubgroupFunctor.range_iso_comp (asIso (j ≫ fst H G)).symm j

/-- A graph subgroup determines a unique actual homomorphism. -/
theorem IsGraph.existsUnique {F : SubgroupFunctor (H ⊗ G)} (hF : IsGraph F) :
    ∃! f : H ⟶ G, graph f = F := by
  obtain ⟨K, j, hj, hp⟩ := hF
  have := hp
  refine ⟨homOfGraphRepresentative j, (graph_homOfGraphRepresentative j).trans hj.2, ?_⟩
  intro f hf
  exact graph_injective (hf.trans ((graph_homOfGraphRepresentative j).trans hj.2).symm)

/-- Actual homomorphisms are exactly the represented subgroup functors whose
first projection is invertible. -/
def graphEquiv : (H ⟶ G) ≃ {F : SubgroupFunctor (H ⊗ G) // IsGraph F} :=
  Equiv.ofBijective (fun f => ⟨graph f, isGraph_graph f⟩)
    ⟨fun f g h => graph_injective (congrArg Subtype.val h), fun F => by
      obtain ⟨f, hf, _⟩ := F.property.existsUnique
      exact ⟨f, Subtype.ext hf⟩⟩

end Langlands.GroupScheme.HomScheme
