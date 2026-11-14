import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorStatement
import Langlands.GroupScheme.AlgebraicFundamentalGroupStatement

/-! # Identity and composition from the geometric induced-map laws -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Choice

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {H G J : GroupScheme (Spec (CommRingCat.of k))}

/-- The identity restricts to the identity of the chosen geometric torus. -/
theorem isTorusFactorization_id (a : Choice k H) :
    a.IsTorusFactorization E a (𝟙 H)
      (𝟙 ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus)) := by
  change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map (𝟙 H) =
    (𝟙 _) ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion
  simp

/-- Geometric restrictions to maximal tori compose. -/
theorem IsTorusFactorization.comp {a : Choice k H} {b : Choice k G}
    {c : Choice k J} {f : H ⟶ G} {g : G ⟶ J}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    {d : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus}
    (hf : a.IsTorusFactorization E b f e)
    (hg : b.IsTorusFactorization E c g d) :
    a.IsTorusFactorization E c (f ≫ g) (e ≫ d) := by
  unfold IsTorusFactorization at *
  rw [Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg,
    ← Category.assoc]
  rfl

end Choice

/-- The selected identity map is the canonical comparison as soon as the
induced-map specification is available. -/
theorem mapTo_id_of_mapStatement
    (hMap : AlgebraicFundamentalGroupMapStatement.{u})
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H)
    (a b : Choice k H) :
    a.mapTo E b (𝟙 H) = a.comparison E b := by
  have hm := (hMap k E H H hH hH a b (𝟙 H)).2.1
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  simpa using hm.2 a (𝟙 _) (a.isTorusFactorization_id (E := E)) ν

/-- The two published geometric map and comparison statements imply all
identity and composition laws for the selected maps. -/
theorem algebraicFundamentalGroupFunctor_of_map_and_comparison
    (hMap : AlgebraicFundamentalGroupMapStatement.{u})
    (hComparison : AlgebraicFundamentalGroupComparisonStatement.{u}) :
    AlgebraicFundamentalGroupFunctorStatement.{u} := by
  intro k E _ _ _ _
  refine ⟨mapTo_id_of_mapStatement hMap k E, ?_⟩
  intro H G J hH hG hJ a b c f g
  have hf := (hMap k E H G hH hG a b f).2.1
  obtain ⟨d, e, he⟩ := hf.1
  have hg := (hMap k E G J hG hJ d c g).2.1
  obtain ⟨t, q, hq⟩ := hg.1
  have hfg := (hMap k E H J hH hJ a c (f ≫ g)).2.1
  have hn := (hMap k E G J hG hJ d c g).2.2.2 b c
  rw [(hComparison k E J hJ).2.1 c, LinearMap.id_comp] at hn
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  change b.mapTo E c g (a.mapTo E b f (a.projection E ν)) = _
  rw [hf.2 d e he ν, ← LinearMap.comp_apply, ← hn,
    hg.2 t q hq (ν ≫ e)]
  simpa only [Category.assoc] using (hfg.2 t (e ≫ q) (he.comp hq) ν).symm

end Langlands.GroupScheme.AlgebraicFundamentalGroup
