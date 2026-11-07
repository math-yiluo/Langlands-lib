import Langlands.GroupScheme.HomScheme.TorusSubgroupChartAffineTestsProof
import Langlands.GroupScheme.HomScheme.FiniteSourceHom
import Langlands.GroupScheme.Descent.ClosedSubgroups

/-! # Overlap conditions for descent of subgroup families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.TorusChartDescent

open Descent TorusSubgroupModuli

variable {S₀ : Scheme.{u}} {G : GroupScheme S₀}

@[reassoc] theorem baseChange_map_left_fst {T S : Scheme.{u}} (f : T ⟶ S) {H H' : GroupScheme S}
    (a : H ⟶ H') :
    ((GroupScheme.baseChange f).map a).hom.hom.left ≫ pullback.fst H'.X.hom f =
      pullback.fst H.X.hom f ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Homomorphisms into an iterated base change are determined by their projection to the
original group scheme. -/
theorem hom_ext_triple {B S T : Scheme.{u}} (qB : B ⟶ S₀) (p : S ⟶ B) (r : T ⟶ S)
    {H : GroupScheme T}
    {a b : H ⟶ (GroupScheme.baseChange r).obj
      ((GroupScheme.baseChange p).obj ((GroupScheme.baseChange qB).obj G))}
    (h : a.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange p).obj ((GroupScheme.baseChange qB).obj G)).X.hom r ≫
        pullback.fst ((GroupScheme.baseChange qB).obj G).X.hom p ≫ pullback.fst G.X.hom qB =
      b.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange p).obj ((GroupScheme.baseChange qB).obj G)).X.hom r ≫
        pullback.fst ((GroupScheme.baseChange qB).obj G).X.hom p ≫ pullback.fst G.X.hom qB) :
    a = b := by
  have hw : a.hom.hom.left ≫ pullback.snd _ r = b.hom.hom.left ≫ pullback.snd _ r :=
    (Over.w a.hom.hom).trans (Over.w b.hom.hom).symm
  have hS : ∀ {Z : Scheme.{u}} (z : Z ⟶ pullback ((GroupScheme.baseChange p).obj
      ((GroupScheme.baseChange qB).obj G)).X.hom r),
      z ≫ pullback.fst ((GroupScheme.baseChange p).obj
          ((GroupScheme.baseChange qB).obj G)).X.hom r ≫
        pullback.snd ((GroupScheme.baseChange qB).obj G).X.hom p =
      z ≫ pullback.snd _ r ≫ r := by
    intro Z z
    exact congrArg (z ≫ ·) (pullback.condition (f := ((GroupScheme.baseChange p).obj
      ((GroupScheme.baseChange qB).obj G)).X.hom) (g := r))
  have hB : ∀ {Z : Scheme.{u}} (z : Z ⟶ pullback ((GroupScheme.baseChange p).obj
      ((GroupScheme.baseChange qB).obj G)).X.hom r),
      z ≫ pullback.fst ((GroupScheme.baseChange p).obj
          ((GroupScheme.baseChange qB).obj G)).X.hom r ≫
        pullback.fst ((GroupScheme.baseChange qB).obj G).X.hom p ≫ pullback.snd G.X.hom qB =
      z ≫ pullback.snd _ r ≫ r ≫ p := by
    intro Z z
    have h1 : pullback.fst ((GroupScheme.baseChange qB).obj G).X.hom p ≫
        pullback.snd G.X.hom qB = pullback.snd ((GroupScheme.baseChange qB).obj G).X.hom p ≫ p :=
      pullback.condition (f := ((GroupScheme.baseChange qB).obj G).X.hom) (g := p)
    rw [h1, ← reassoc_of% (hS z)]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa only [Category.assoc] using h
      · simp only [Category.assoc]
        rw [hB, hB, reassoc_of% hw]
    · simp only [Category.assoc]
      rw [hS, hS, reassoc_of% hw]
  · exact hw

/-- The descent overlap condition for a subgroup family along `p`, when its evaluations at
two test points agree as soon as the points agree after `p`. -/
theorem overlap_range_eq_of_evaluate_eq {M : Over S₀} {B : Scheme.{u}}
    (p : M.left ⟶ B) (qB : B ⟶ S₀) (hp : p ≫ qB = M.hom) {K : GroupScheme M.left}
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj G)
    (H : ∀ (T : Over S₀) (a b : T ⟶ M), a.left ≫ p = b.left ≫ p →
      TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b) :
    SubgroupFunctor.range ((GroupScheme.baseChange (fst p)).map
        (j ≫ (pullbackComparison qB p M.hom hp G).inv) ≫
        (canonicalOverlap p ((GroupScheme.baseChange qB).obj G)).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map
        (j ≫ (pullbackComparison qB p M.hom hp G).inv)) := by
  let T₀ : Over S₀ := Over.mk (fst p ≫ M.hom)
  have hsnd : snd p ≫ M.hom = T₀.hom := by
    change snd p ≫ M.hom = fst p ≫ M.hom
    rw [← hp, ← Category.assoc, ← Category.assoc, pullback.condition]
  let a : T₀ ⟶ M := Over.homMk (fst p) rfl
  let b : T₀ ⟶ M := Over.homMk (snd p) hsnd
  have hab : TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b :=
    H T₀ a b pullback.condition
  let c := pullbackComparison qB p M.hom hp G
  let Ψ : (GroupScheme.baseChange T₀.hom).obj G ≅ (GroupScheme.baseChange (snd p)).obj
      ((GroupScheme.baseChange p).obj ((GroupScheme.baseChange qB).obj G)) :=
    (pullbackComparison M.hom (fst p) T₀.hom rfl G).symm ≪≫
      (GroupScheme.baseChange (fst p)).mapIso c.symm ≪≫ canonicalOverlap p _
  have h1 : (GroupScheme.baseChange (fst p)).map (j ≫ c.inv) ≫
      (canonicalOverlap p ((GroupScheme.baseChange qB).obj G)).hom = familyHom j a ≫ Ψ.hom := by
    change _ = ((GroupScheme.baseChange (fst p)).map j ≫
      (pullbackComparison M.hom (fst p) T₀.hom rfl G).hom) ≫ Ψ.hom
    simp only [Ψ, Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have h2' : (GroupScheme.baseChange (snd p)).map c.inv =
      (pullbackComparison M.hom (snd p) T₀.hom hsnd G).hom ≫ Ψ.hom := by
    apply hom_ext_triple qB p (snd p)
    rw [baseChange_map_left_fst_assoc, pullbackComparison_inv_fst]
    simp only [Ψ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
      Over.comp_left, Category.assoc]
    rw [canonicalOverlap_fst_assoc, baseChange_map_left_fst_assoc, pullbackComparison_inv_fst,
      pullbackComparison_inv_fst, pullbackComparison_hom_fst]
  have h2 : (GroupScheme.baseChange (snd p)).map (j ≫ c.inv) = familyHom j b ≫ Ψ.hom := by
    change _ = ((GroupScheme.baseChange (snd p)).map j ≫
      (pullbackComparison M.hom (snd p) T₀.hom hsnd G).hom) ≫ Ψ.hom
    rw [Functor.map_comp, h2', Category.assoc]
  rw [h1, h2]
  exact (SubgroupFunctor.range_comp_iso_eq_iff _ _ Ψ).mpr hab

/-- Equality of evaluations of a closed family, for a test condition stable under
restriction, can be checked on spectra of algebras. -/
theorem evaluate_eq_of_specOver {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} {M : Over (Spec (CommRingCat.of R))}
    {K : GroupScheme M.left} (j : K ⟶ (GroupScheme.baseChange M.hom).obj G)
    (hj : IsClosedSubgroup j)
    (Φ : ∀ {T : Over (Spec (CommRingCat.of R))}, (T ⟶ M) → (T ⟶ M) → Prop)
    (hΦ : ∀ {T T' : Over (Spec (CommRingCat.of R))} (c : T' ⟶ T) (a b : T ⟶ M), Φ a b →
      Φ (c ≫ a) (c ≫ b))
    (H : ∀ (C : Type u) [CommRing C] [Algebra R C] (a b : FiniteSource.specOver R C ⟶ M),
      Φ a b → TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b)
    (T : Over (Spec (CommRingCat.of R))) (a b : T ⟶ M) (h : Φ a b) :
    TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b := by
  refine (evaluate_eq_iff_openCover j j hj hj a b T.left.affineCover).mpr fun k => ?_
  let T' := SubgroupFunctor.coverObj T.left.affineCover k
  have hT' : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X k))
  let ψ : CommRingCat.of R ⟶ Γ(T'.left, ⊤) :=
    Spec.preimage (T'.left.isoSpec.inv ≫ T'.hom : Spec Γ(T'.left, ⊤) ⟶ Spec (CommRingCat.of R))
  let : Algebra R Γ(T'.left, ⊤) := ψ.hom.toAlgebra
  let e : T' ≅ FiniteSource.specOver R Γ(T'.left, ⊤) := Over.isoMk T'.left.isoSpec (by
    show T'.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.hom) = T'.hom
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, Iso.hom_inv_id_assoc])
  have hc := hΦ (SubgroupFunctor.coverMap T.left.affineCover k) a b h
  have he := evaluate_eq_comp j j _ _
    (H Γ(T'.left, ⊤) (e.inv ≫ SubgroupFunctor.coverMap T.left.affineCover k ≫ a)
      (e.inv ≫ SubgroupFunctor.coverMap T.left.affineCover k ≫ b)
      (hΦ e.inv _ _ hc)) e.hom
  simpa only [Iso.hom_inv_id_assoc] using he

end Langlands.GroupScheme.HomScheme.TorusChartDescent
