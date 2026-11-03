import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.SubgroupIntersection

/-! # Intersections of two dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Let `G` be a smooth affine group over a field and `χ, χ'` cocharacters with the points of
`χ'` in `P_G(χ)`. Every group scheme representing `P_G(χ) ⊓ P_G(χ')` is smooth, and it has
connected underlying space when `G` does, given dynamic connectedness. The intersection is the
dynamic parabolic of `χ'` inside a representative of `P_G(χ)`. -/
theorem smooth_connected_of_isRepresentedBy_parabolic_inf
    (hCo : DynamicConnectedStatement.{u}) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ Dynamic.parabolic χ)
    {H : GroupScheme (Spec (CommRingCat.of k))} {c : H ⟶ G}
    (hc : (Dynamic.parabolic χ ⊓ Dynamic.parabolic χ').IsRepresentedBy c) :
    Smooth H.X.hom ∧ (ConnectedSpace G.X.left → ConnectedSpace H.X.left) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Q, iP, hiP, hiPc⟩ : ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (iP : Q ⟶ G),
      (Dynamic.parabolic χ).IsRepresentedBy iP ∧ IsClosedSubgroup iP :=
    ⟨_, _, Dynamic.Affine.isRepresentedBy_parabolicHom χ,
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ⟩
  have : Mono iP.hom.hom := hiP.1
  have : Mono c.hom.hom := hc.1
  have : Smooth Q.X.hom := (dynamicSmooth k G χ Q iP).1 hiP
  have : IsClosedImmersion iP.hom.hom.left := hiPc
  have : IsAffineHom Q.X.hom := by
    rw [← Over.w iP.hom.hom]
    infer_instance
  obtain ⟨χQ, hχQ⟩ : ∃ χQ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Q, χQ ≫ iP = χ' :=
    ⟨_, hiP.liftOfLE_comp χ' hχ'⟩
  have hcP : SubgroupFunctor.range c ≤ Dynamic.parabolic χ := by
    rw [hc.2]
    exact fun _ _ hx => hx.1
  have hcP' : SubgroupFunctor.range c ≤ Dynamic.parabolic χ' := by
    rw [hc.2]
    exact fun _ _ hx => hx.2
  set cQ := hiP.liftOfLE c hcP with hcQdef
  have hcQ : cQ ≫ iP = c := hiP.liftOfLE_comp c hcP
  have hcQh : cQ.hom.hom ≫ iP.hom.hom = c.hom.hom := by
    rw [← hcQ]
    rfl
  have hP : Dynamic.parabolic χQ = (Dynamic.parabolic χ').comap iP := by
    rw [← hχQ]
    exact Dynamic.parabolic_eq_comap_of_isClosedSubgroup χQ iP hiPc
  have hrep : (Dynamic.parabolic χQ).IsRepresentedBy cQ := by
    have : Mono cQ.hom.hom := by
      have : Mono (cQ.hom.hom ≫ iP.hom.hom) := by
        rw [hcQh]
        infer_instance
      exact mono_of_mono _ iP.hom.hom
    refine ⟨this, ?_⟩
    rw [hP]
    refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      apply hcP'
      refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
      rw [Category.assoc, hcQh]
    · intro hx
      have hxP : x ≫ iP.hom.hom ∈ (Dynamic.parabolic χ).carrier T := by
        rw [← hiP.2]
        exact SubgroupFunctor.mem_range.2 ⟨x, rfl⟩
      have hxc : x ≫ iP.hom.hom ∈ (SubgroupFunctor.range c).carrier T := by
        rw [hc.2]
        exact ⟨hxP, hx⟩
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hxc
      refine ⟨y, (cancel_mono iP.hom.hom).1 ?_⟩
      rw [Category.assoc, hcQh, hy]
  refine ⟨(dynamicSmooth k Q χQ H cQ).1 hrep, fun hG => ?_⟩
  have : ConnectedSpace Q.X.left := ((hCo k G χ Q iP).2 hG).1 hiP
  exact ((hCo k Q χQ H cQ).2 this).1 hrep

/-- A commutative subgroup `t : T ⟶ G` lies in the dynamic parabolic of each of its
cocharacters. -/
theorem range_le_parabolic_groupHom_comp {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    SubgroupFunctor.range t ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) :=
  (range_le_centralizer_groupHom_comp t ν).trans (Dynamic.centralizer_le_parabolic _)

/-- Let `t : T ⟶ G` be a commutative subgroup of a smooth affine group over a field, and let
`i, i'` be monomorphisms onto the dynamic parabolics of two cocharacters `ν, ν'` of `T`. Then
the intersection `pullback i i'` is smooth, it has connected underlying space when `G` does
(given dynamic connectedness), and `t` factors through its inclusion into `G`. -/
theorem smooth_connected_pullback_of_range_eq_parabolic
    (hCo : DynamicConnectedStatement.{u}) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (t : T.toGrp ⟶ G)
    (ν ν' : cocharacterLattice T) {P P' : GroupScheme (Spec (CommRingCat.of k))}
    {i : P ⟶ G} {i' : P' ⟶ G} [Mono i.hom.hom] [Mono i'.hom.hom]
    (hi : SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t))
    (hi' : SubgroupFunctor.range i' = Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t)) :
    Smooth (pullback i i').X.hom ∧
      (ConnectedSpace G.X.left → ConnectedSpace (pullback i i').X.left) ∧
      ∃ tH : T.toGrp ⟶ pullback i i', tH ≫ pullback.fst i i' ≫ i = t := by
  have hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t)).IsRepresentedBy
        (pullback.fst i i' ≫ i) := by
    have : Mono (subgroupIntersectionFst i i').hom.hom :=
      (subgroupIntersection_isPullback i i').mono_fst_of_mono
    refine ⟨?_, ?_⟩
    · change Mono ((subgroupIntersectionFst i i').hom.hom ≫ i.hom.hom)
      infer_instance
    · rw [← hi, ← hi']
      exact range_subgroupIntersectionHom i i'
  have hle : SubgroupFunctor.range (CommGroupScheme.groupHom ν' ≫ t) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) :=
    (SubgroupFunctor.range_comp_le _ t).trans (range_le_parabolic_groupHom_comp t ν)
  obtain ⟨hsm, hcon⟩ := smooth_connected_of_isRepresentedBy_parabolic_inf hCo _ _ hle hrep
  have hTle : SubgroupFunctor.range t ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t) :=
    fun U x hx => ⟨range_le_parabolic_groupHom_comp t ν U hx,
      range_le_parabolic_groupHom_comp t ν' U hx⟩
  exact ⟨hsm, hcon, hrep.liftOfLE t hTle, hrep.liftOfLE_comp t hTle⟩

end Langlands.GroupScheme
