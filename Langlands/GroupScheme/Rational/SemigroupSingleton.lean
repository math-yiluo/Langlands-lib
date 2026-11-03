import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.OrderedProductMaps
import Langlands.GroupScheme.Derived.Basic

/-! # The singleton semigroup ordered product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section SingletonProduct

variable {B : Scheme.{u}}

private theorem singleton_orderedMultiplication_isIso (G : GroupScheme B) :
    IsIso (orderedMultiplication (fun _ : Fin 1 => 𝟙 G)) := by
  apply (isIso_orderedMultiplication_iff _).2
  intro T
  constructor
  · intro x y h
    have h0 : x 0 = y 0 := by
      rw [orderedPoints_one, orderedPoints_one] at h
      change x 0 ≫ 𝟙 G.X = y 0 ≫ 𝟙 G.X at h
      simpa only [Category.comp_id] using h
    funext r
    simpa only [Fin.eq_zero r] using h0
  · intro g
    refine ⟨fun _ => g, ?_⟩
    rw [orderedPoints_one]
    change g ≫ 𝟙 G.X = g
    exact Category.comp_id g

/-- The actual singleton ordered multiplication, with its inverse supplied by
the all-test coordinate equivalence. -/
def singletonOrderedProductIso (G : GroupScheme B) :
    (∏ᶜ fun _ : Fin 1 => G).X ≅ G.X :=
  letI := singleton_orderedMultiplication_isIso G
  asIso (orderedMultiplication (fun _ : Fin 1 => 𝟙 G))

@[simp]
theorem singletonOrderedProductIso_hom (G : GroupScheme B) :
    (singletonOrderedProductIso G).hom =
      orderedMultiplication (fun _ : Fin 1 => 𝟙 G) := rfl

end SingletonProduct

section CoveringSemigroup

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- If a semigroup contains every ambient action weight, the smooth connected
ambient group itself is a generator and the generated functor is total. -/
theorem semigroupSubgroup_eq_top_of_support (b : AutomorphicAction S.toGrp G)
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (A : AddSubsemigroup (characterLattice S))
    (hA : actionWeightSupport b ⊤ ⊆ A) :
    semigroupSubgroup b A = ⊤ := by
  apply semigroupSubgroup_eq_of_maximal_generator b A ⊤
  · refine ⟨⟨G, 𝟙 G, ?_, IsClosedSubgroup.of_iso (Iso.refl G), hG, hconn⟩,
      ?_, hA⟩
    · refine ⟨?_, SubgroupFunctor.range_id G⟩
      change Mono (𝟙 G.X)
      infer_instance
    · exact fun _ _ _ _ => Subgroup.mem_top _
  · exact fun _ _ _ _ _ => Subgroup.mem_top _

/-- Coverage by one block puts every ambient weight in the positively
generated semigroup of that block. -/
theorem semigroupSubgroup_singleton_eq_top (b : AutomorphicAction S.toGrp G)
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (Ψ : Fin 1 → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤) (r : Fin 1) :
    semigroupSubgroup b (AddSubsemigroup.closure (Ψ r)) = ⊤ := by
  apply semigroupSubgroup_eq_top_of_support b hG hconn
  intro χ hχ
  have hmem : χ ∈ ⋃ q, Ψ q := hcover.symm ▸ hχ
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hmem
  apply AddSubsemigroup.subset_closure
  simpa only [Fin.eq_zero q, Fin.eq_zero r] using hq

/-- The exact ordered-product conclusion for a single covering block, with
the ambient group as its smooth connected closed representative. -/
theorem semigroupOrderedProduct_singleton (b : AutomorphicAction S.toGrp G)
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (Ψ : Fin 1 → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤) :
    ∃ (H : Fin 1 → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G),
      (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
      IsIso (orderedMultiplication j) := by
  refine ⟨fun _ => G, fun _ => 𝟙 G, ?_, ?_⟩
  · intro r
    rw [semigroupSubgroup_singleton_eq_top b hG hconn Ψ hcover r]
    refine ⟨⟨?_, SubgroupFunctor.range_id G⟩,
      IsClosedSubgroup.of_iso (Iso.refl G), hG, hconn⟩
    change Mono (𝟙 G.X)
    infer_instance
  · exact (singletonOrderedProductIso G).isIso_hom

end CoveringSemigroup

end Langlands.GroupScheme.RelativeRoot
