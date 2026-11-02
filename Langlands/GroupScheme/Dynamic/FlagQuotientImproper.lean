import Langlands.GroupScheme.Dynamic.FlagQuotientStatement
import Langlands.GroupScheme.Dynamic.ImproperParabolic

/-! # Proper scheme quotients for improper dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable (k : Type u) [Field k]

/-- The base scheme as a relative scheme, the quotient model when the parabolic is full. -/
def improperFlagQuotient : Over (Spec (CommRingCat.of k)) :=
  Over.mk (𝟙 _)

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The structure morphism to the quotient of a group by itself. -/
def improperFlagQuotientMap : G.X ⟶ improperFlagQuotient k :=
  Over.homMk G.X.hom (Category.comp_id _)

/-- The improper quotient model has proper structure morphism. -/
theorem improperFlagQuotient_isProper : IsProper (improperFlagQuotient k).hom := by
  dsimp [improperFlagQuotient]
  infer_instance

/-- All morphisms to the improper quotient are the structure morphism. -/
theorem improperFlagQuotient_hom_ext {T : Over (Spec (CommRingCat.of k))}
    (f g : T ⟶ improperFlagQuotient k) : f = g := by
  apply Over.OverMorphism.ext
  have hf : f.left = T.hom := by
    have h := Over.w f
    change f.left ≫ 𝟙 _ = T.hom at h
    simpa only [Category.comp_id] using h
  have hg : g.left = T.hom := by
    have h := Over.w g
    change g.left ≫ 𝟙 _ = T.hom at h
    simpa only [Category.comp_id] using h
  exact hf.trans hg.symm

/-- The structure morphism realizes the exact all-test coset fibers of a full parabolic. -/
theorem improperFlagQuotientMap_fibers
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hP : parabolic χ = ⊤)
    (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) :
    g ≫ improperFlagQuotientMap k G = h ≫ improperFlagQuotientMap k G ↔
      g⁻¹ * h ∈ (parabolic χ).carrier T := by
  rw [hP]
  simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
  exact improperFlagQuotient_hom_ext k _ _

/-- The identity section over the whole base is a section of the improper quotient map. -/
theorem improperFlagQuotientMap_section :
    (1 : openOver k (improperFlagQuotient k) ⊤ ⟶ G.X) ≫ improperFlagQuotientMap k G =
      openOverι k (improperFlagQuotient k) ⊤ :=
  improperFlagQuotient_hom_ext k _ _

/-- The exact algebraic flag-quotient conclusion in the improper case. -/
theorem exists_properFlagQuotient_of_parabolic_eq_top
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hP : parabolic χ = ⊤) :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (π : G.X ⟶ Q),
      IsProper Q.hom ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ π = h ≫ π ↔ g⁻¹ * h ∈ (parabolic χ).carrier T) ∧
      ∀ p : RingPoint k Q k,
        ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
          Set.range p.left ⊆ U ∧ s ≫ π = openOverι k Q U := by
  refine ⟨improperFlagQuotient k, improperFlagQuotientMap k G,
    improperFlagQuotient_isProper k, improperFlagQuotientMap_fibers k G χ hP, ?_⟩
  intro p
  exact ⟨⊤, 1, Set.subset_univ _, improperFlagQuotientMap_section k G⟩

/-- Every group scheme has the required proper quotient for its trivial cocharacter. -/
theorem exists_properFlagQuotient_trivialCocharacter :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (π : G.X ⟶ Q),
      IsProper Q.hom ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ π = h ≫ π ↔
          g⁻¹ * h ∈ (parabolic (trivialCocharacter G)).carrier T) ∧
      ∀ p : RingPoint k Q k,
        ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
          Set.range p.left ⊆ U ∧ s ≫ π = openOverι k Q U :=
  exists_properFlagQuotient_of_parabolic_eq_top k G _ (parabolic_trivialCocharacter (G := G))

end Langlands.GroupScheme.Dynamic
