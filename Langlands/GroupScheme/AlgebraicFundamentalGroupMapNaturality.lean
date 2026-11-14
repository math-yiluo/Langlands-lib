import Langlands.GroupScheme.AlgebraicFundamentalGroupMapIndependence
import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorStatement

/-! # Naturality of induced fundamental-group maps from canonical comparisons -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup
namespace Choice

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a a' : Choice k H) (b c : Choice k G) (f : H ⟶ G)
  (E : Type u) [Field E] [Algebra k E] [IsSepClosure k E]
  (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
  (e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a'.torus ⟶
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus)
  (he : a.IsTorusFactorization E b f e)
  (he' : a'.IsTorusFactorization E c f e')
  (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj H))
  (s : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a'.torus)
  (hs : a.IsConjugationComparison E a' g s)

include he he' hs in
/-- A source conjugator extends to a compatible conjugation between containing
target maximal tori. -/
theorem exists_factorizationComparison_along_conjugation :
    ∃ (h : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (t : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus),
      b.IsConjugationComparison E c h t ∧ e ≫ t.hom = s.hom ≫ e' := by
  let F := GroupScheme.baseChange (algebraBaseMap k E)
  let j := F.map f
  let gG := g ≫ j.hom.hom
  have hGE := b.isCover.isConnectedReductive.baseChange_of_algebraicExtension (K := E)
  let := hGE.smooth
  let := hGE.isAffineHom
  let := hGE.connectedSpace
  change F.map a.inclusion ≫ j = CommGroupScheme.groupHom e ≫ F.map b.inclusion at he
  change F.map a'.inclusion ≫ j = CommGroupScheme.groupHom e' ≫ F.map c.inclusion at he'
  change F.map a.inclusion ≫ ((F.obj H).innerIso g).hom =
    CommGroupScheme.groupHom s.hom ≫ F.map a'.inclusion at hs
  have hinv : CommGroupScheme.groupHom s.inv ≫ CommGroupScheme.groupHom s.hom = 𝟙 _ :=
    congrArg CommGroupScheme.groupHom s.inv_hom_id
  have hcommon :
      (CommGroupScheme.groupHom s.inv ≫ CommGroupScheme.groupHom e) ≫
          (F.map b.inclusion ≫ ((F.obj G).innerIso gG).hom) =
        CommGroupScheme.groupHom e' ≫ F.map c.inclusion := by
    calc
      _ = CommGroupScheme.groupHom s.inv ≫
          (CommGroupScheme.groupHom e ≫ F.map b.inclusion) ≫
            ((F.obj G).innerIso gG).hom := by simp only [Category.assoc]
      _ = CommGroupScheme.groupHom s.inv ≫
          (F.map a.inclusion ≫ j) ≫ ((F.obj G).innerIso gG).hom := by rw [← he]
      _ = CommGroupScheme.groupHom s.inv ≫
          (F.map a.inclusion ≫ ((F.obj H).innerIso g).hom) ≫ j := by
        simp only [Category.assoc]
        rw [← innerIso_hom_comp j g]
      _ = CommGroupScheme.groupHom s.inv ≫
          (CommGroupScheme.groupHom s.hom ≫ F.map a'.inclusion) ≫ j := by rw [hs]
      _ = F.map a'.inclusion ≫ j := by
        simp only [← Category.assoc, hinv, Category.id_comp]
      _ = _ := he'
  obtain ⟨h, t, ht, hq, _⟩ := exists_conjugacy_of_split_torus_factorizations
    (G := F.obj G)
    (A := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a'.torus)
    (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
    (T' := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus)
    (a'.geometric_isSplitTorus E)
    (F.map b.inclusion ≫ ((F.obj G).innerIso gG).hom) (F.map c.inclusion)
    ((b.geometric_isMaximalSplitTorus E).comp_iso ((F.obj G).innerIso gG))
    (c.geometric_isMaximalSplitTorus E)
    (CommGroupScheme.groupHom s.inv ≫ CommGroupScheme.groupHom e)
    (CommGroupScheme.groupHom e') hcommon
  let tc : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus :=
    { hom := Additive.ofMul t.hom
      inv := Additive.ofMul t.inv
      hom_inv_id := congrArg Additive.ofMul t.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul t.inv_hom_id }
  refine ⟨h * gG, tc, ?_, ?_⟩
  · change F.map b.inclusion ≫ ((F.obj G).innerIso (h * gG)).hom =
      t.hom ≫ F.map c.inclusion
    rw [innerIso_mul_hom, ← Category.assoc]
    exact ht
  · have hq' := congrArg (fun q => CommGroupScheme.groupHom s.hom ≫ q) hq
    have hhom : CommGroupScheme.groupHom s.hom ≫ CommGroupScheme.groupHom s.inv = 𝟙 _ :=
      congrArg CommGroupScheme.groupHom s.hom_inv_id
    simp only [← Category.assoc, hhom, Category.id_comp] at hq'
    exact congrArg Additive.ofMul hq'

/-- Chosen compatible target conjugation data along a given source conjugator. -/
def factorizationComparisonAlongConjugation :
    Σ h : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G),
      {t : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus //
        b.IsConjugationComparison E c h t ∧ e ≫ t.hom = s.hom ≫ e'} :=
  let h := a.exists_factorizationComparison_along_conjugation a' b c f E e e' he he' g s hs
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

variable (hcomparison : AlgebraicFundamentalGroupComparisonStatement.{u})

include hcomparison in
/-- The selected induced map satisfies its defining law, assuming comparison. -/
theorem mapTo_isInducedMap_of_comparison :
    a.IsInducedMap E c f (a.mapTo E c f) :=
  a.mapTo_spec E c f (a.exists_isInducedMap_of_comparison c f E hcomparison)

omit [IsSepClosure k E] in
/-- A torus homomorphism over the original field commutes with lattice Galois
transport. -/
theorem cocharacter_galois_naturality (q : a.torus ⟶ b.torus)
    (σ : E ≃ₐ[k] E) (ν : a.lattice E) :
    cocharacterLattice.galoisRepresentation k E b.torus σ
        (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map q) =
      cocharacterLattice.galoisRepresentation k E a.torus σ ν ≫
        (CommGroupScheme.baseChange (algebraBaseMap k E)).map q := by
  apply Additive.ofMul.injective
  exact transportCocharacter_naturality (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ) (CommGroupScheme.groupHom q) (CommGroupScheme.groupHom ν)

include hcomparison in
/-- Every induced map is Galois equivariant. -/
theorem IsInducedMap.galois_of_comparison
    {m : a.atChoice E →ₗ[ℤ] c.atChoice E} (hm : a.IsInducedMap E c f m)
    (σ : E ≃ₐ[k] E) (x : a.atChoice E) :
    m (a.galoisRepresentation E σ x) = c.galoisRepresentation E σ (m x) := by
  obtain ⟨b, q, hq⟩ := a.exists_torusFactorization c f
  let qE := (CommGroupScheme.baseChange (algebraBaseMap k E)).map q
  have hqE : a.IsTorusFactorization E b f qE := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map f =
      (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom q) ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp, hq]
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  rw [galoisRepresentation_projection, hm.2 b qE hqE, hm.2 b qE hqE,
    ← (hcomparison k E G c.isCover.isConnectedReductive).1 b c |>.2.2.2.1 σ,
    galoisRepresentation_projection, a.cocharacter_galois_naturality b E q σ ν]

include hcomparison in
/-- Selected induced maps commute with simultaneous changes of source and target
presentations. -/
theorem mapTo_comparison_of_comparison (c' : Choice k G) :
    (c.comparison E c').comp (a.mapTo E c f) =
      (a'.mapTo E c' f).comp (a.comparison E a') := by
  have hm := a.mapTo_isInducedMap_of_comparison c f E hcomparison
  have hm' := a'.mapTo_isInducedMap_of_comparison c' f E hcomparison
  obtain ⟨b, q, hq⟩ := hm.1
  obtain ⟨d, q', hq'⟩ := hm'.1
  obtain ⟨g, s, hs, hsrc⟩ :=
    (hcomparison k E H a.isCover.isConnectedReductive).1 a a' |>.2.1
  obtain ⟨h, t, ht, hqt⟩ :=
    a.exists_factorizationComparison_along_conjugation a' b d f E q q' hq hq' g s hs
  have htarget := (hcomparison k E G c.isCover.isConnectedReductive).1 b d |>.2.2.2.2 h t ht
  have hcomp := (hcomparison k E G c.isCover.isConnectedReductive).2.2
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  change c.comparison E c' (a.mapTo E c f (a.projection E ν)) =
    a'.mapTo E c' f (a.comparison E a' (a.projection E ν))
  rw [hm.2 b q hq, hsrc, hm'.2 d q' hq']
  calc
    _ = b.comparison E c' (b.projection E (ν ≫ q)) :=
      congrArg (fun m => m (b.projection E (ν ≫ q))) (hcomp b c c')
    _ = d.comparison E c' (d.projection E ((ν ≫ s.hom) ≫ q')) := by
      rw [← hcomp b d c', LinearMap.comp_apply, htarget, Category.assoc, hqt,
        ← Category.assoc]

end Choice

/-- The full map statement follows from canonical coherent comparisons. -/
theorem algebraicFundamentalGroupMap_of_comparison
    (hcomparison : AlgebraicFundamentalGroupComparisonStatement.{u}) :
    AlgebraicFundamentalGroupMapStatement.{u} := by
  intro k E _ _ _ _ H G hH hG a c f
  have hm := a.mapTo_isInducedMap_of_comparison c f E hcomparison
  refine ⟨⟨a.mapTo E c f, hm, fun m hm' => ?_⟩, hm, ?_, ?_⟩
  · exact Choice.IsInducedMap.ext a c f E hm' hm
  · exact fun σ x => Choice.IsInducedMap.galois_of_comparison a c f E hcomparison hm σ x
  · exact fun a' c' => a.mapTo_comparison_of_comparison a' c f E hcomparison c'

end Langlands.GroupScheme.AlgebraicFundamentalGroup
