import Langlands.GroupScheme.SubgroupFunctor.EtaleDescent
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Pairwise overlap compatibility and all-test étale matching -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

variable {S U V : Scheme.{u}}

/-- The two iterated ambient pullbacks to a pairwise overlap have their
canonical identification through the same direct pullback. -/
def pairwiseOverlapIso (f : U ⟶ S) (g : V ⟶ S) (G : GroupScheme S) :
    (GroupScheme.baseChange (pullback.fst f g)).obj ((GroupScheme.baseChange f).obj G) ≅
      (GroupScheme.baseChange (pullback.snd f g)).obj ((GroupScheme.baseChange g).obj G) :=
  pullbackComparison f (pullback.fst f g) (pullback.fst f g ≫ f) rfl G ≪≫
    (pullbackComparison g (pullback.snd f g) (pullback.fst f g ≫ f)
      pullback.condition.symm G).symm

/-- Canonical pairwise overlap transport preserves projection to the
original ambient group scheme. -/
@[reassoc] theorem pairwiseOverlapIso_hom_fst
    (f : U ⟶ S) (g : V ⟶ S) (G : GroupScheme S) :
    (pairwiseOverlapIso f g G).hom.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange g).obj G).X.hom (pullback.snd f g) ≫
        pullback.fst G.X.hom g =
      pullback.fst ((GroupScheme.baseChange f).obj G).X.hom (pullback.fst f g) ≫
        pullback.fst G.X.hom f := by
  change ((pullbackComparison f (pullback.fst f g) _ rfl G).hom.hom.hom.left ≫
    (pullbackComparison g (pullback.snd f g) _ pullback.condition.symm G).inv.hom.hom.left)
      ≫ _ ≫ _ = _
  simp only [Category.assoc, pullbackComparison_inv_fst, pullbackComparison_hom_fst]

end Descent

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Absolute membership in an inverse image is membership after the
underlying ambient homomorphism. -/
theorem schemeCondition_comap_iff (F : SubgroupFunctor G) (j : H ⟶ G)
    {Y : Scheme.{u}} (x : Y ⟶ H.X.left) :
    (F.comap j).schemeCondition x ↔ F.schemeCondition (x ≫ j.hom.hom.left) := by
  let T : Over S := Over.mk (x ≫ H.X.hom)
  let p : T ⟶ H.X := Over.homMk x rfl
  calc
    (F.comap j).schemeCondition x ↔ p ∈ (F.comap j).carrier T :=
      (F.comap j).schemeCondition_iff_mem p
    _ ↔ (p ≫ j.hom.hom) ∈ F.carrier T := Iff.rfl
    _ ↔ F.schemeCondition (x ≫ j.hom.hom.left) :=
      (F.schemeCondition_iff_mem (p ≫ j.hom.hom)).symm

/-- Containment on the pairwise overlap transfers membership between
points with the same projection to the original ambient group. -/
theorem schemeCondition_of_pairwiseOverlap_le
    {U V : Scheme.{u}} (f : U ⟶ S) (g : V ⟶ S)
    (F : SubgroupFunctor ((GroupScheme.baseChange f).obj G))
    (E : SubgroupFunctor ((GroupScheme.baseChange g).obj G))
    (hFE : (E.baseChange (pullback.snd f g)).comap
        (Descent.pairwiseOverlapIso f g G).hom ≤
      F.baseChange (pullback.fst f g))
    {Y : Scheme.{u}}
    (x : Y ⟶ ((GroupScheme.baseChange f).obj G).X.left)
    (y : Y ⟶ ((GroupScheme.baseChange g).obj G).X.left)
    (hxy : x ≫ pullback.fst G.X.hom f = y ≫ pullback.fst G.X.hom g)
    (hy : E.schemeCondition y) : F.schemeCondition x := by
  let A := (GroupScheme.baseChange f).obj G
  let B := (GroupScheme.baseChange g).obj G
  let p := pullback.fst f g
  let q := pullback.snd f g
  let e := Descent.pairwiseOverlapIso f g G
  have hbase : (x ≫ A.X.hom) ≫ f = (y ≫ B.X.hom) ≫ g := by
    change (x ≫ pullback.snd G.X.hom f) ≫ f =
      (y ≫ pullback.snd G.X.hom g) ≫ g
    simp only [Category.assoc, ← pullback.condition]
    rw [← Category.assoc, hxy, Category.assoc]
  let a : Y ⟶ pullback f g :=
    pullback.lift (x ≫ A.X.hom) (y ≫ B.X.hom) hbase
  let z : Y ⟶ ((GroupScheme.baseChange p).obj A).X.left :=
    pullback.lift x a (by
      change x ≫ A.X.hom = a ≫ p
      simp only [a, p, pullback.lift_fst])
  have hz : z ≫ e.hom.hom.hom.left ≫ pullback.fst B.X.hom q = y := by
    apply pullback.hom_ext
    · change (z ≫ e.hom.hom.hom.left ≫ pullback.fst B.X.hom q) ≫
        pullback.fst G.X.hom g = y ≫ pullback.fst G.X.hom g
      simp only [Category.assoc, e, B, q, Descent.pairwiseOverlapIso_hom_fst]
      simpa only [← Category.assoc, z, A, p, pullback.lift_fst] using hxy
    · change (z ≫ e.hom.hom.hom.left ≫ pullback.fst B.X.hom q) ≫ B.X.hom =
        y ≫ B.X.hom
      calc
        _ = z ≫ e.hom.hom.hom.left ≫ pullback.snd B.X.hom q ≫ q := by
          simp only [Category.assoc, pullback.condition]
        _ = z ≫ pullback.snd A.X.hom p ≫ q := by
          rw [← Category.assoc e.hom.hom.hom.left,
            show e.hom.hom.hom.left ≫ pullback.snd B.X.hom q =
              pullback.snd A.X.hom p from Over.w e.hom.hom.hom]
        _ = a ≫ q := by rw [← Category.assoc, pullback.lift_snd]
        _ = y ≫ B.X.hom := pullback.lift_snd _ _ _
  have hE : (E.baseChange q).schemeCondition (z ≫ e.hom.hom.hom.left) := by
    rw [← E.schemeCondition_baseChange_iff q, Category.assoc, hz]
    exact hy
  have hcomap : ((E.baseChange q).comap e.hom).schemeCondition z :=
    (schemeCondition_comap_iff _ _ z).mpr hE
  have hF : (F.baseChange p).schemeCondition z := hFE _ hcomap
  rw [← F.schemeCondition_baseChange_iff p] at hF
  change F.schemeCondition (z ≫ pullback.fst A.X.hom p) at hF
  have hzx : z ≫ pullback.fst A.X.hom p = x := pullback.lift_fst _ _ _
  rwa [hzx] at hF

variable (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- Pairwise overlap containment gives the universal test-comparison
condition used in effective étale subgroup descent. -/
theorem isMatchingEtale_of_pairwiseOverlap_le
    (hF : ∀ i j, ((F j).baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).comap
        (Descent.pairwiseOverlapIso (𝒰.f i) (𝒰.f j) G).hom ≤
      (F i).baseChange (pullback.fst (𝒰.f i) (𝒰.f j))) :
    IsMatchingEtale 𝒰 F := by
  intro i j V W a x hx
  let y := (baseChangePointsEquiv (𝒰.f i) G V).symm
    (a ≫ baseChangePointsEquiv (𝒰.f j) G W x)
  apply ((F i).schemeCondition_iff_mem y).mp
  apply schemeCondition_of_pairwiseOverlap_le (𝒰.f i) (𝒰.f j)
    (F i) (F j) (hF i j) y.left (a.left ≫ x.left)
  · have hy := congrArg CommaMorphism.left
      ((baseChangePointsEquiv (𝒰.f i) G V).apply_symm_apply
        (a ≫ baseChangePointsEquiv (𝒰.f j) G W x))
    simpa only [y, baseChangePointsEquiv_left, Over.comp_left, Category.assoc] using hy
  · exact (F j).schemeCondition_comp x.left a.left
      (((F j).schemeCondition_iff_mem x).mpr hx)

/-- Equality of local subgroup functors on every actual pairwise overlap
implies all-test étale matching. -/
theorem isMatchingEtale_of_pairwiseOverlap_eq
    (hF : ∀ i j, (F i).baseChange (pullback.fst (𝒰.f i) (𝒰.f j)) =
      ((F j).baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).comap
        (Descent.pairwiseOverlapIso (𝒰.f i) (𝒰.f j) G).hom) :
    IsMatchingEtale 𝒰 F :=
  isMatchingEtale_of_pairwiseOverlap_le 𝒰 F (fun i j => (hF i j).ge)

/-- Equality of local subgroup ranges in their common direct ambient
pullback supplies the matching condition for subgroup descent. -/
theorem isMatchingEtale_range_of_pairwiseOverlap_eq
    (B : ∀ i, GroupScheme (𝒰.X i))
    (j : ∀ i, B i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G)
    (hB : ∀ i k,
      let p := pullback.fst (𝒰.f i) (𝒰.f k)
      let q := pullback.snd (𝒰.f i) (𝒰.f k)
      let r := p ≫ 𝒰.f i
      let ei := Descent.pullbackComparison (𝒰.f i) p r rfl G
      let ek := Descent.pullbackComparison (𝒰.f k) q r pullback.condition.symm G
      range ((GroupScheme.baseChange p).map (j i) ≫ ei.hom) =
        range ((GroupScheme.baseChange q).map (j k) ≫ ek.hom)) :
    IsMatchingEtale 𝒰 (fun i => range (j i)) := by
  apply isMatchingEtale_of_pairwiseOverlap_eq
  intro i k
  rw [← range_baseChangeHom, ← range_baseChangeHom]
  let p := pullback.fst (𝒰.f i) (𝒰.f k)
  let q := pullback.snd (𝒰.f i) (𝒰.f k)
  let r := p ≫ 𝒰.f i
  let ei := Descent.pullbackComparison (𝒰.f i) p r rfl G
  let ek := Descent.pullbackComparison (𝒰.f k) q r pullback.condition.symm G
  have h := congrArg
    (fun P : SubgroupFunctor ((GroupScheme.baseChange r).obj G) => P.comap ei.hom)
    (hB i k)
  simpa only [ei, ek, r, p, q, range_comp_iso, ← comap_comp, Iso.hom_inv_id, comap_id,
    Descent.pairwiseOverlapIso, Iso.trans_hom, Iso.symm_hom] using h

end SubgroupFunctor

end Langlands.GroupScheme
