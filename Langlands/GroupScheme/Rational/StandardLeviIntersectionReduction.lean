import Langlands.GroupScheme.Rational.StandardLeviIntersectionStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Nested standard Levi intersections from standard cocharacters and the parabolic order

For index sets `J ⊆ K` of simple relative roots, the decomposition of `L_K ∩ P_J` as
`(L_K ∩ U_J) ⋊ L_J` on every test scheme, and the product `U_J = (L_K ∩ U_J) U_K`, follow from
the dynamic decomposition `P(χ) = U(χ) ⋊ Z(χ)` of a standard cocharacter, once a standard
cocharacter for `J` realizes `L_J` and `U_J`, one for `K` realizes `L_K` and `U_K`, and the
standard subgroups satisfy `L_J ≤ L_K`, `P_J ≤ P_K` and `U_K ≤ U_J`. This file proves that
reduction. The realizing cocharacters and the inclusions are supplied by
`StandardCocharacterStatement` and `StandardParabolicOrderStatement`, which are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace StandardLeviIntersection

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A standard cocharacter `zeta` for `J` whose dynamic centralizer and unipotent subgroup
functors lie in the standard Levi `L_J` and the standard unipotent subgroup `U_J`. The reverse
inclusions hold for every standard cocharacter, so such a `zeta` realizes `L_J` and `U_J`. -/
def IsRealizingStandardCocharacter (J : Set (characterLattice T))
    (zeta : cocharacterLattice T) : Prop :=
  IsStandardCocharacter i ν J zeta ∧
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤ standardLevi i ν J ∧
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤ standardUnipotent i ν J

/-- Points of `P_J` normalize the points of `U_J`, on every test scheme and for every index
set `J`. -/
theorem conj_mem_standardUnipotent {J : Set (characterLattice T)}
    {Q : Over (Spec (CommRingCat.of k))} {p v : Q ⟶ G.X}
    (hp : p ∈ (standardParabolic i ν J).carrier Q)
    (hv : v ∈ (standardUnipotent i ν J).carrier Q) :
    p * v * p⁻¹ ∈ (standardUnipotent i ν J).carrier Q := by
  rw [mem_standardParabolic] at hp
  rw [mem_standardUnipotent] at hv ⊢
  intro zeta hzeta
  exact Dynamic.conj_mem_unipotent _ (hp zeta hzeta) (hv zeta hzeta)

/-- If `J` has a standard cocharacter, a point of both `L_J` and `U_J` is trivial. -/
theorem eq_one_of_mem_standardLevi_of_mem_standardUnipotent {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta)
    {Q : Over (Spec (CommRingCat.of k))} {g : Q ⟶ G.X}
    (hl : g ∈ (standardLevi i ν J).carrier Q) (hu : g ∈ (standardUnipotent i ν J).carrier Q) :
    g = 1 :=
  Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent _
    (fun _ _ _ _ h h' => h.unique _ h')
    (standardLevi_le_dynamicCentralizer i ν hzeta Q hl)
    (standardUnipotent_le_dynamicUnipotent i ν hzeta Q hu)

/-- If a standard cocharacter for `J` realizes `L_J` and `U_J`, every point of `P_J` is a
point of `U_J` times a point of `L_J`. -/
theorem exists_standardUnipotent_mul_standardLevi {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsRealizingStandardCocharacter i ν J zeta)
    {Q : Over (Spec (CommRingCat.of k))} {g : Q ⟶ G.X}
    (hg : g ∈ (standardParabolic i ν J).carrier Q) :
    ∃ v ∈ (standardUnipotent i ν J).carrier Q, ∃ l ∈ (standardLevi i ν J).carrier Q,
      v * l = g := by
  have hgP := standardParabolic_le_dynamicParabolic i ν hzeta.1 Q hg
  exact ⟨_, hzeta.2.2 Q (Dynamic.mul_inv_limit_mem_unipotent _ ⟨g, hgP⟩), _,
    hzeta.2.1 Q (Dynamic.limit_mem_centralizer _ ⟨g, hgP⟩), inv_mul_cancel_right _ _⟩

/-- The decomposition of `L_K ∩ P_J` as `(L_K ∩ U_J) ⋊ L_J` on a test scheme `Q`, from a
standard cocharacter for `J` realizing `L_J` and `U_J` and the inclusion `L_J ≤ L_K`. -/
theorem leviInterParabolic_decomposition {J K : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsRealizingStandardCocharacter i ν J zeta)
    (hLevi : standardLevi i ν J ≤ standardLevi i ν K) (Q : Over (Spec (CommRingCat.of k))) :
    let H := (standardLevi i ν K ⊓ standardParabolic i ν J).carrier Q
    let V := (standardLevi i ν K ⊓ standardUnipotent i ν J).carrier Q
    let L := (standardLevi i ν J).carrier Q
    V ≤ H ∧ L ≤ H ∧ (V.subgroupOf H).Normal ∧
      (V.subgroupOf H).IsComplement' (L.subgroupOf H) := by
  intro H V L
  have hVH : V ≤ H := fun g hg =>
    ⟨hg.1, standardUnipotent_le_standardParabolic i ν J Q hg.2⟩
  have hLH : L ≤ H := fun g hg =>
    ⟨hLevi Q hg, standardLevi_le_standardParabolic i ν J Q hg⟩
  refine ⟨hVH, hLH, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hVH]
    intro v h hv hh
    have hhK : h ∈ (standardLevi i ν K).carrier Q := hh.1
    have hvK : v ∈ (standardLevi i ν K).carrier Q := hv.1
    have hK : h * v * h⁻¹ ∈ (standardLevi i ν K).carrier Q :=
      mul_mem (mul_mem hhK hvK) (inv_mem hhK)
    exact ⟨hK, conj_mem_standardUnipotent i ν hh.2 hv.2⟩
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hv hl
      exact Subtype.ext
        (eq_one_of_mem_standardLevi_of_mem_standardUnipotent i ν hzeta.1 hl hv.2)
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨v, hv, l, hl, hvl⟩ := exists_standardUnipotent_mul_standardLevi i ν hzeta x.2.2
      have hxK : (x : Q ⟶ G.X) ∈ (standardLevi i ν K).carrier Q := x.2.1
      have hvK : v ∈ (standardLevi i ν K).carrier Q := by
        have h := mul_mem hxK (inv_mem (hLevi Q hl))
        rwa [← hvl, mul_inv_cancel_right] at h
      refine Set.mem_mul.2 ⟨⟨v, hVH ⟨hvK, hv⟩⟩, ⟨hvK, hv⟩, ⟨l, hLH hl⟩, hl, ?_⟩
      exact Subtype.ext hvl

/-- The product `U_J = (L_K ∩ U_J) U_K` on a test scheme `Q`, from a standard cocharacter for
`K` realizing `L_K` and `U_K` and the inclusions `P_J ≤ P_K` and `U_K ≤ U_J`. -/
theorem standardUnipotent_eq_leviInter_mul {J K : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsRealizingStandardCocharacter i ν K zeta)
    (hPar : standardParabolic i ν J ≤ standardParabolic i ν K)
    (hUni : standardUnipotent i ν K ≤ standardUnipotent i ν J)
    (Q : Over (Spec (CommRingCat.of k))) :
    (↑((standardUnipotent i ν J).carrier Q) : Set (Q ⟶ G.X)) =
      (↑((standardLevi i ν K).carrier Q ⊓ (standardUnipotent i ν J).carrier Q) :
        Set (Q ⟶ G.X)) * (↑((standardUnipotent i ν K).carrier Q) : Set (Q ⟶ G.X)) := by
  apply Set.Subset.antisymm
  · intro u hu
    have huK : u ∈ (standardParabolic i ν K).carrier Q :=
      hPar Q (standardUnipotent_le_standardParabolic i ν J Q hu)
    obtain ⟨w, hw, l, hl, hwl⟩ := exists_standardUnipotent_mul_standardLevi i ν hzeta huK
    have hlP : l⁻¹ ∈ (standardParabolic i ν K).carrier Q :=
      inv_mem (standardLevi_le_standardParabolic i ν K Q hl)
    have hb : l⁻¹ * w * l⁻¹⁻¹ ∈ (standardUnipotent i ν K).carrier Q :=
      conj_mem_standardUnipotent i ν hlP hw
    rw [inv_inv] at hb
    have hlu : l = u * (l⁻¹ * w * l)⁻¹ := by
      rw [← hwl]
      group
    have hlJ : l ∈ (standardUnipotent i ν J).carrier Q := by
      rw [hlu]
      exact mul_mem hu (inv_mem (hUni Q hb))
    refine Set.mem_mul.2 ⟨l, ⟨hl, hlJ⟩, l⁻¹ * w * l, hb, ?_⟩
    rw [← hwl]
    group
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem ha.2 (hUni Q hb)

end StandardLeviIntersection

open StandardLeviIntersection in
/-- `StandardCocharacterStatement` and `StandardParabolicOrderStatement` together imply
`StandardLeviIntersectionStatement`. -/
theorem standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder
    (hC : StandardCocharacterStatement.{u}) (hO : StandardParabolicOrderStatement.{u}) :
    StandardLeviIntersectionStatement.{u} := by
  intro k _ G hG T i hi ν hν J K hJ hK hJK
  have := hG.isAffineHom
  obtain ⟨⟨zJ, hzJ⟩, hJeq⟩ := hC k G hG T i hi ν hν J hJ
  obtain ⟨⟨zK, hzK⟩, hKeq⟩ := hC k G hG T i hi ν hν K hK
  obtain ⟨hJP, hJLU⟩ := (hO k G hG T i hi ν hν).1 J K hJ hK
  obtain ⟨_, hLJ, hUJ⟩ := hJeq zJ hzJ
  obtain ⟨_, hLK, hUK⟩ := hKeq zK hzK
  obtain ⟨hLevi, hUni⟩ := hJLU hJK
  refine ⟨fun Q => leviInterParabolic_decomposition i ν ⟨hzJ, hLJ.ge, hUJ.ge⟩ hLevi Q, ?_⟩
  exact standardUnipotent_eq_leviInter_mul i ν ⟨hzK, hLK.ge, hUK.ge⟩ (hJP.1 hJK) hUni _

end Langlands.GroupScheme
