import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent
import Langlands.GroupScheme.Descent.SquareSemilinear

/-! # Pairwise overlap comparisons imply all-test cover matching -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {K : Precoverage Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} K S) (i j : 𝒰.I₀)

/-- The canonical ambient group comparison on a pairwise cover overlap. -/
def overlapSquareIso (G : GroupScheme S) :
    (GroupScheme.baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).obj
        ((GroupScheme.baseChange (𝒰.f i)).obj G) ≅
      (GroupScheme.baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).obj
        ((GroupScheme.baseChange (𝒰.f j)).obj G) :=
  Descent.squareComparison (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j))
    (𝒰.f j) (pullback.snd (𝒰.f i) (𝒰.f j)) pullback.condition G

/-- The comparison commutes with every original group homomorphism. -/
@[reassoc] theorem overlapSquareIso_naturality
    {G H : GroupScheme S} (f : G ⟶ H) :
    (GroupScheme.baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).map
        ((GroupScheme.baseChange (𝒰.f i)).map f) ≫
          (overlapSquareIso 𝒰 i j H).hom =
      (overlapSquareIso 𝒰 i j G).hom ≫
        (GroupScheme.baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).map
          ((GroupScheme.baseChange (𝒰.f j)).map f) :=
  Descent.squareComparison_naturality _ _ _ _ _ f

/-- The inverse overlap comparison preserves the projection to the base group. -/
@[reassoc] theorem overlapSquareIso_inv_fst_fst (G : GroupScheme S) :
    (overlapSquareIso 𝒰 i j G).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange (𝒰.f i)).obj G).X.hom
          (pullback.fst (𝒰.f i) (𝒰.f j)) ≫ pullback.fst G.X.hom (𝒰.f i) =
      pullback.fst ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom
        (pullback.snd (𝒰.f i) (𝒰.f j)) ≫ pullback.fst G.X.hom (𝒰.f j) := by
  have h := Descent.squareComparison_hom_fst_fst (𝒰.f i)
    (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f j)
    (pullback.snd (𝒰.f i) (𝒰.f j)) pullback.condition G
  change (overlapSquareIso 𝒰 i j G).hom.hom.hom.left ≫ _ ≫ _ = _ at h
  rw [← h, ← Category.assoc (overlapSquareIso 𝒰 i j G).inv.hom.hom.left
    (overlapSquareIso 𝒰 i j G).hom.hom.hom.left]
  change ((overlapSquareIso 𝒰 i j G).inv ≫
    (overlapSquareIso 𝒰 i j G).hom).hom.hom.left ≫ _ = _
  simp

variable {G : GroupScheme S}

/-- Equality of transported ranges on every pairwise overlap implies matching
on every pair of relative test schemes and every comparison between them. -/
theorem isMatching_of_overlap_range_eq
    (N : ∀ i, GroupScheme (𝒰.X i))
    (r : ∀ i, N i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G)
    (h : ∀ i j,
      range ((GroupScheme.baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).map (r i)) =
        range ((GroupScheme.baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).map (r j) ≫
          (overlapSquareIso 𝒰 i j G).inv)) :
    IsMatching 𝒰 (fun i => range (r i)) := by
  intro i j V W a x hx
  let q : V.left ⟶ pullback (𝒰.f i) (𝒰.f j) :=
    pullback.lift V.hom (a.left ≫ W.hom) (by
      have w := Over.w a
      change a.left ≫ (W.hom ≫ 𝒰.f j) = V.hom ≫ 𝒰.f i at w
      simpa only [Category.assoc] using w.symm)
  let Z : Over (pullback (𝒰.f i) (𝒰.f j)) := Over.mk q
  let eV : (Over.map (pullback.fst (𝒰.f i) (𝒰.f j))).obj Z ≅ V :=
    Over.isoMk (Iso.refl _) (by simp [Z, q])
  let aW : (Over.map (pullback.snd (𝒰.f i) (𝒰.f j))).obj Z ⟶ W :=
    Over.homMk a.left (by simp [Z, q])
  let xj := (baseChangePointsEquiv (pullback.snd (𝒰.f i) (𝒰.f j))
    ((GroupScheme.baseChange (𝒰.f j)).obj G) Z).symm (aW ≫ x)
  have hxj : xj ∈
      (range ((GroupScheme.baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).map
        (r j))).carrier Z := by
    rw [range_baseChangeHom, mem_baseChange]
    simpa only [xj, MulEquiv.apply_symm_apply] using (range (r j)).comp_mem aW hx
  have hxi : xj ≫ (overlapSquareIso 𝒰 i j G).inv.hom.hom ∈
      (range ((GroupScheme.baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).map
        (r i))).carrier Z := by
    rw [h i j, mem_range]
    obtain ⟨y, hy⟩ := mem_range.mp hxj
    exact ⟨y, by rw [Grp.comp_hom_hom, ← Category.assoc, hy]⟩
  rw [range_baseChangeHom, mem_baseChange] at hxi
  have hmem := (range (r i)).comp_mem eV.inv hxi
  convert hmem using 1
  apply (baseChangePointsEquiv (𝒰.f i) G V).injective
  rw [MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  have hj := congrArg (fun z => z.left)
    ((baseChangePointsEquiv (pullback.snd (𝒰.f i) (𝒰.f j))
      ((GroupScheme.baseChange (𝒰.f j)).obj G) Z).apply_symm_apply (aW ≫ x))
  change xj.left ≫
    pullback.fst ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom
      (pullback.snd (𝒰.f i) (𝒰.f j)) = a.left ≫ x.left at hj
  change a.left ≫ (x.left ≫ pullback.fst G.X.hom (𝒰.f j)) =
    ((𝟙 V.left) ≫ ((xj.left ≫ (overlapSquareIso 𝒰 i j G).inv.hom.hom.left) ≫
      pullback.fst ((GroupScheme.baseChange (𝒰.f i)).obj G).X.hom
        (pullback.fst (𝒰.f i) (𝒰.f j)))) ≫ pullback.fst G.X.hom (𝒰.f i)
  simp only [Category.id_comp, Category.assoc, overlapSquareIso_inv_fst_fst]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ pullback.fst G.X.hom (𝒰.f j)) hj.symm

end Langlands.GroupScheme.SubgroupFunctor.CoverDescent
