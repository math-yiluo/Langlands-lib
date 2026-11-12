import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups

/-! # Descent of fixed almost-simple factors through compatible comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Changing the structure of a test scheme preserves its projection to the
original group. -/
theorem descentPoint_left_fst {B S : Scheme.{u}} (b : S ⟶ B)
    (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (T : Over S) (x : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (descentPoint b a ha G T x).left ≫ pullback.fst G.X.hom b =
      x.left ≫ pullback.fst G.X.hom b := by
  have h := congrArg (fun f => f.left)
    (baseChangePointsEquiv_descentPoint b a ha G T x)
  change (descentPoint b a ha G T x).left ≫ pullback.fst G.X.hom b =
    (𝟙 T.left) ≫ (x.left ≫ pullback.fst G.X.hom b) at h
  simpa only [Category.id_comp] using h

/-- A homomorphism preserving the original projection intertwines changes
of the test scheme's structure. -/
theorem descentPoint_comp_of_fst {B C S : Scheme.{u}}
    (b : S ⟶ B) (c : S ⟶ C) (a : S ⟶ S)
    (hb : a ≫ b = b) (hc : a ≫ c = c)
    (G : GroupScheme B) (H : GroupScheme C)
    (f : (GroupScheme.baseChange c).obj H ⟶ (GroupScheme.baseChange b).obj G)
    (p : H.X.left ⟶ G.X.left)
    (hf : f.hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom c ≫ p)
    (T : Over S) (x : T ⟶ ((GroupScheme.baseChange c).obj H).X) :
    descentPoint c a hc H T x ≫ f.hom.hom =
      descentPoint b a hb G T (x ≫ f.hom.hom) := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, Over.comp_left]
  rw [descentPoint_left_fst b a hb G T (x ≫ f.hom.hom)]
  simp only [Over.comp_left, Category.assoc, hf]
  have h := congrArg (fun t => t ≫ p) (descentPoint_left_fst c a hc H T x)
  change (descentPoint c a hc H T x).left ≫ pullback.fst H.X.hom c ≫ p =
    x.left ≫ pullback.fst H.X.hom c ≫ p
  simpa only [Category.assoc] using h

namespace SubgroupFunctor

/-- A homomorphism preserving projection to the original group commutes with
canonical subgroup transport on every test scheme. -/
theorem descentTransport_comap_of_fst {B C S : Scheme.{u}}
    (b : S ⟶ B) (c : S ⟶ C) (a : S ⟶ S)
    (hb : a ≫ b = b) (hc : a ≫ c = c)
    (G : GroupScheme B) (H : GroupScheme C)
    (f : (GroupScheme.baseChange c).obj H ⟶ (GroupScheme.baseChange b).obj G)
    (p : H.X.left ⟶ G.X.left)
    (hf : f.hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom c ≫ p)
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    descentTransport c a hc H (F.comap f) =
      (descentTransport b a hb G F).comap f := by
  ext T x
  rw [mem_descentTransport_iff_descentPoint, mem_comap, mem_comap,
    mem_descentTransport_iff_descentPoint,
    descentPoint_comp_of_fst b c a hb hc G H f p hf]

end SubgroupFunctor

namespace SimplyConnectedAlmostSimpleProduct

variable {k E L : Type u} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L] [Algebra E L] [IsScalarTower k E L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- A factor fixed by the upper Galois group descends to the intermediate
field, with its actual inclusion recovered through the specified comparison. -/
theorem exists_factor_descent_of_fixes [IsAffineHom G.X.hom] [IsGalois E L]
    (i : D.Index)
    (e : (GroupScheme.baseChange (algebraBaseMap E L)).obj
        ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (he : e.hom.hom.hom.left ≫ pullback.fst G.X.hom (algebraBaseMap k L) =
      pullback.fst ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom
        (algebraBaseMap E L) ≫ pullback.fst G.X.hom (algebraBaseMap k E))
    (hi : ∀ σ : L ≃ₐ[E] L, D.galoisFactorIndex (σ.restrictScalars k) i = i) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of E)))
      (j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj G)
      (r : (GroupScheme.baseChange (algebraBaseMap E L)).obj H ≅ D.factor i),
      IsAffine H.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange (algebraBaseMap E L)).map j =
          r.hom ≫ (D.inclusion i ≫ e.inv) := by
  let GE := (GroupScheme.baseChange (algebraBaseMap k E)).obj G
  let : IsAffineHom GE.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k E)))
  let jL : D.factor i ⟶ (GroupScheme.baseChange (algebraBaseMap E L)).obj GE :=
    D.inclusion i ≫ e.inv
  have hjL : IsClosedSubgroup jL :=
    (D.isClosedSubgroup_inclusion i).comp_iso e.symm
  apply Descent.GaloisInvariantClosedSubgroup.exists_descent hjL
  intro σ
  have ht := SubgroupFunctor.descentTransport_comap_of_fst
    (algebraBaseMap k L) (algebraBaseMap E L) (galoisBaseMap E L σ)
    (galoisBaseMap_over k L (σ.restrictScalars k)) (galoisBaseMap_over E L σ)
    G GE e.hom (pullback.fst G.X.hom (algebraBaseMap k E)) he
    (SubgroupFunctor.range (D.inclusion i))
  change SubgroupFunctor.galoisTransport E L GE σ
      ((SubgroupFunctor.range (D.inclusion i)).comap e.hom) =
    (SubgroupFunctor.galoisTransport k L G (σ.restrictScalars k)
      (SubgroupFunctor.range (D.inclusion i))).comap e.hom at ht
  rw [← D.range_inclusion_galoisFactorIndex, hi σ] at ht
  have hr : SubgroupFunctor.range jL =
      (SubgroupFunctor.range (D.inclusion i)).comap e.hom :=
    SubgroupFunctor.range_comp_iso (D.inclusion i) e.symm
  rw [← hr] at ht
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _ at ht
  rwa [SubgroupFunctor.descentTransport_range] at ht

/-- Choose the actual affine closed model, its inclusion and its exact
recovery isomorphism for a fixed factor. -/
def factorDescentOfFixes [IsAffineHom G.X.hom] [IsGalois E L]
    (i : D.Index)
    (e : (GroupScheme.baseChange (algebraBaseMap E L)).obj
        ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (he : e.hom.hom.hom.left ≫ pullback.fst G.X.hom (algebraBaseMap k L) =
      pullback.fst ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom
        (algebraBaseMap E L) ≫ pullback.fst G.X.hom (algebraBaseMap k E))
    (hi : ∀ σ : L ≃ₐ[E] L, D.galoisFactorIndex (σ.restrictScalars k) i = i) :
    Σ H : GroupScheme (Spec (CommRingCat.of E)),
      Σ j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj G,
        {r : (GroupScheme.baseChange (algebraBaseMap E L)).obj H ≅ D.factor i //
          IsAffine H.X.left ∧ IsClosedSubgroup j ∧
            (GroupScheme.baseChange (algebraBaseMap E L)).map j =
              r.hom ≫ (D.inclusion i ≫ e.inv)} := by
  let h := D.exists_factor_descent_of_fixes i e he hi
  exact ⟨h.choose, h.choose_spec.choose,
    h.choose_spec.choose_spec.choose, h.choose_spec.choose_spec.choose_spec⟩

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
