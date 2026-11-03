import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.SchemeAction

/-! # All-Borel containment from fixed rational cosets in one Borel quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Construct a factor through any Borel from all-test fixedness of every
rational point of one Borel quotient, using the exact Borel conjugacy input. -/
def factorThroughBorelOfFixedQuotient
    (hconj : BorelConjugacyStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B₀ : GroupScheme (Spec (CommRingCat.of k))) (b₀ : B₀ ⟶ G)
    (hb₀ : IsBorelSubgroup b₀)
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (hi : IsClosedSubgroup i)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
    (hfib : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b₀).carrier Z)
    (a : SchemeAction G Q)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (hfixed : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
      (a.restrict i).IsFixed x)
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (hb : IsBorelSubgroup b) :
    {f : U ⟶ B // f ≫ b = i} := by
  classical
  apply Classical.choice
  obtain ⟨g, φ, hg⟩ := (hconj k G).2 B₀ B b₀ b hb₀ hb
  have hcoset : ∀ (Z : Over (Spec (CommRingCat.of k))) (h : Z ⟶ U.X),
      ((h ≫ i.hom.hom) * G.constantPoint g Z) ≫ q =
        G.constantPoint g Z ≫ q := by
    intro Z h
    have e := hfixed (g ≫ q) Z (Over.homMk Z.hom (by simp)) h
    rw [SchemeAction.restrict_act, ← Category.assoc] at e
    change a.act (h ≫ i.hom.hom) (G.constantPoint g Z ≫ q) =
      G.constantPoint g Z ≫ q at e
    rwa [hact] at e
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion b₀.hom.hom.left := hb₀.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono b₀.hom.hom := Over.mono_of_mono_left _
  let f := factorOfFixedCoset i b₀ q hfib g hcoset
  have hf : f ≫ b₀ = i ≫ (G.innerIso g⁻¹).hom :=
    factorOfFixedCoset_comp i b₀ q hfib g hcoset
  refine ⟨⟨f ≫ φ.hom, ?_⟩⟩
  calc
    (f ≫ φ.hom) ≫ b = f ≫ (b₀ ≫ (G.innerIso g).hom) := by
      rw [Category.assoc, ← hg]
    _ = (i ≫ (G.innerIso g⁻¹).hom) ≫ (G.innerIso g).hom := by
      rw [← Category.assoc, hf]
    _ = i := by rw [G.innerIso_inv_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- The constructed factor gives containment on every scheme test. -/
theorem range_le_all_borels_of_fixed_quotient
    (hconj : BorelConjugacyStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B₀ : GroupScheme (Spec (CommRingCat.of k))) (b₀ : B₀ ⟶ G)
    (hb₀ : IsBorelSubgroup b₀)
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (hi : IsClosedSubgroup i)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
    (hfib : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b₀).carrier Z)
    (a : SchemeAction G Q)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (hfixed : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
      (a.restrict i).IsFixed x)
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (hb : IsBorelSubgroup b) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range b := by
  let f := factorThroughBorelOfFixedQuotient hconj k G B₀ b₀ hb₀ U i hi Q q hfib
    a hact hfixed B b hb
  exact SubgroupFunctor.range_le_of_factor f.val f.property

end Langlands.GroupScheme
