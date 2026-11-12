import Langlands.GroupScheme.Products
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationReduction
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementProof

/-! # Actual finite almost-simple products for simply connected groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Products

variable {S : Scheme.{u}} {I J : Type u} [Finite I] [Finite J]
    (A : I → GroupScheme S) (B : J → GroupScheme S)

/-- The family on the disjoint union of two index types. -/
abbrev sumGroupFamily : I ⊕ J → GroupScheme S
  | .inl i => A i
  | .inr j => B j

/-- Combining two finite products gives the product on their disjoint union. -/
def finiteProductSumIso :
    pi A ⊗ pi B ≅ pi ((sumGroupFamily A B)) where
  hom := Pi.lift (f := (sumGroupFamily A B)) (Sum.rec
    (fun i => fst (pi A) (pi B) ≫ Pi.π A i)
    (fun j => snd (pi A) (pi B) ≫ Pi.π B j))
  inv := lift (Pi.lift (f := A) (fun i => Pi.π ((sumGroupFamily A B)) (Sum.inl i)))
    (Pi.lift (f := B) (fun j => Pi.π ((sumGroupFamily A B)) (Sum.inr j)))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Pi.hom_ext
      intro i
      simp only [Category.assoc, lift_fst, Category.id_comp]
      rw [Pi.lift_comp_π]
      exact Pi.lift_comp_π _ _
    · apply Pi.hom_ext
      intro j
      simp only [Category.assoc, lift_snd, Category.id_comp]
      rw [Pi.lift_comp_π]
      exact Pi.lift_comp_π _ _
  inv_hom_id := by
    apply Pi.hom_ext
    intro ij
    cases ij with
    | inl i =>
      simp only [Category.assoc, Pi.lift_comp_π, Category.id_comp]
      rw [← Category.assoc, lift_fst, Pi.lift_comp_π]
    | inr j =>
      simp only [Category.assoc, Pi.lift_comp_π, Category.id_comp]
      rw [← Category.assoc, lift_snd, Pi.lift_comp_π]

end Products

variable {k : Type u} [Field k]

/-- Actual finite simply connected almost-simple factors and a group-scheme
isomorphism from their product to the supplied group, oriented toward the
categorical product for subsequent projection constructions. -/
structure SimplyConnectedAlmostSimpleProduct
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  Index : Type u
  [finite : Finite Index]
  factor : Index → GroupScheme (Spec (CommRingCat.of k))
  isSimplyConnected : ∀ i, IsSimplyConnected (factor i)
  isAlmostSimple : ∀ i, IsAlmostSimple (factor i)
  iso : G ≅ pi factor

attribute [instance] SimplyConnectedAlmostSimpleProduct.finite

namespace SimplyConnectedAlmostSimpleProduct

variable {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- An almost-simple simply connected group is a one-factor product. -/
def single (hG : IsSimplyConnected G) (hA : IsAlmostSimple G) :
    SimplyConnectedAlmostSimpleProduct G where
  Index := PUnit.{u + 1}
  factor := fun _ => G
  isSimplyConnected := fun _ => hG
  isAlmostSimple := fun _ => hA
  iso := (productUniqueIso (fun _ : PUnit.{u + 1} => G)).symm

/-- A group with the trivial full point functor is an empty product. -/
def empty (htriv : SubgroupFunctor.range (𝟙 G) = ⊥) :
    SimplyConnectedAlmostSimpleProduct G where
  Index := PEmpty.{u + 1}
  factor := PEmpty.elim
  isSimplyConnected := fun i => i.elim
  isAlmostSimple := fun i => i.elim
  iso := {
    hom := Pi.lift (fun i => i.elim)
    inv := Grp.homMk (toUnit _ ≫ η[G.X])
    hom_inv_id := by
      apply hom_ext_points
      intro T x
      have hall (y : T ⟶ G.X) : y = 1 := by
        have hy : y ∈ (SubgroupFunctor.range (𝟙 G)).carrier T :=
          ⟨y, Category.comp_id y⟩
        simpa only [htriv, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hy
      exact (hall _).trans (hall _).symm
    inv_hom_id := by
      apply Pi.hom_ext
      intro i
      exact i.elim }

/-- Two finite product presentations combine across a supplied binary
product isomorphism. -/
def append (e : G ≅ H ⊗ K)
    (D : SimplyConnectedAlmostSimpleProduct H)
    (E : SimplyConnectedAlmostSimpleProduct K) :
    SimplyConnectedAlmostSimpleProduct G where
  Index := D.Index ⊕ E.Index
  factor := sumGroupFamily D.factor E.factor
  isSimplyConnected := Sum.rec D.isSimplyConnected E.isSimplyConnected
  isAlmostSimple := Sum.rec D.isAlmostSimple E.isAlmostSimple
  iso := e ≪≫ (D.iso ⊗ᵢ E.iso) ≪≫ finiteProductSumIso D.factor E.factor

end SimplyConnectedAlmostSimpleProduct

/-- Every simply connected semisimple field group admits actual finite
simply connected almost-simple factors. The empty product is allowed. -/
theorem IsSimplyConnected.nonempty_almostSimpleProduct
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G) :
    Nonempty (SimplyConnectedAlmostSimpleProduct G) := by
  classical
  let P : GroupScheme (Spec (CommRingCat.of k)) → Prop := fun G =>
    IsSimplyConnected G → Nonempty (SimplyConnectedAlmostSimpleProduct G)
  have : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have : ConnectedSpace G.X.left := hG.isSemisimple.isConnectedReductive.connectedSpace
  suffices h : P G from h hG
  apply smoothConnectedAffineGroup_lieDimension_induction P ?_ G
  intro G _ _ _ ih hG
  by_cases htriv : SubgroupFunctor.range (𝟙 G) = ⊥
  · exact ⟨SimplyConnectedAlmostSimpleProduct.empty htriv⟩
  by_cases hAS : IsAlmostSimple G
  · exact ⟨SimplyConnectedAlmostSimpleProduct.single hG hAS⟩
  have hbad : ¬ ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range j).IsNormal →
      SubgroupFunctor.range j = ⊥ ∨ SubgroupFunctor.range j = ⊤ := by
    intro h
    exact hAS ⟨hG.isSemisimple, hG.isSemisimple.noncommutative_of_nontrivial htriv, h⟩
  push Not at hbad
  obtain ⟨H, j, hj, hsH, hcH, hnH, hntH, hfullH⟩ := hbad
  obtain ⟨hH, K, i, hK, hi, _, hprod, hc, hm⟩ :=
    semisimpleNormalIsogenyComplement k G H hG.isSemisimple j hj hsH hcH hnH
  let m := commutingSubgroupMultiplicationHom j i hc
  have : IsIso m := hG.central_isogeny_isIso (H ⊗ K) m hprod hm
  have hscProd : IsSimplyConnected (H ⊗ K) := hG.of_iso (asIso m)
  have hscH : IsSimplyConnected H := hscProd.of_tensor_left hH hK
  have hscK : IsSimplyConnected K := hscProd.of_tensor_right hH hK
  have : Smooth H.X.hom := hsH
  have : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  have : ConnectedSpace H.X.left := hcH
  have : Smooth K.X.hom := hK.isConnectedReductive.smooth
  have : IsAffineHom K.X.hom := hK.isConnectedReductive.isAffineHom
  have : ConnectedSpace K.X.left := hK.isConnectedReductive.connectedSpace
  have hjproper : ¬ IsIso j := by
    intro hjiso
    let := hjiso
    have hrep : SubgroupFunctor.range j = ⊤ := by
      apply SubgroupFunctor.ext
      intro T
      apply top_unique
      intro x _
      have : IsIso j.hom.hom := (Grp.forget _).map_isIso j
      refine ⟨x ≫ inv j.hom.hom, ?_⟩
      change (x ≫ inv j.hom.hom) ≫ j.hom.hom = x
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hfullH hrep
  have hiproper : ¬ IsIso i := by
    intro hiiso
    let := hiiso
    exact hntH (range_left_eq_bot_of_isIso_right_commutingMultiplication j i hc)
  obtain ⟨D⟩ := ih H (Lie.dimension_lt_of_proper_closedSubgroup j hj hjproper) hscH
  obtain ⟨E⟩ := ih K (Lie.dimension_lt_of_proper_closedSubgroup i hi hiproper) hscK
  exact ⟨SimplyConnectedAlmostSimpleProduct.append (asIso m).symm D E⟩

/-- Choose the actual finite product decomposition constructed by dimension
induction and the published arbitrary-field normal complement theorem. -/
def IsSimplyConnected.almostSimpleProduct
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G) :
    SimplyConnectedAlmostSimpleProduct G :=
  Classical.choice hG.nonempty_almostSimpleProduct

end Langlands.GroupScheme
