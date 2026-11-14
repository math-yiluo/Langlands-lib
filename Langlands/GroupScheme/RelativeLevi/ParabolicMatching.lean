import Langlands.GroupScheme.RelativeLevi.ParabolicZariskiDescent
import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints

/-! # Ordinary matching and effective descent of actual parabolic families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M N T : Over S}

/-- A subgroup restriction is the pullback of its all-test condition along
the family point adjunction. -/
theorem restrict_val_eq (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G)) :
    (restrict hG a F).val =
      (F.val.baseChange a.left).comap
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).inv := by
  simp only [restrict, evaluate, familyHom, SubgroupFunctor.range_comp_iso,
    SubgroupFunctor.range_baseChangeHom, (parabolicRepresentative F).represents.2]

/-- Membership after restriction has its literal relative-test meaning. -/
theorem mem_restrict_iff (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (V : Over T.left) (x : V ⟶ ((GroupScheme.baseChange T.hom).obj G).X) :
    x ∈ (restrict hG a F).val.carrier V ↔
      familyPointsEquiv (G := G) a V x ∈
        F.val.carrier ((Over.map a.left).obj V) := by
  rw [restrict_val_eq]
  rfl

/-- Membership transfers along an arbitrary comparison of relative tests
whose original group-valued points agree. -/
theorem mem_restrict_of_original (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (V : Over T.left) (W : Over M.left)
    (b : (Over.map a.left).obj V ⟶ W)
    (x : V ⟶ ((GroupScheme.baseChange T.hom).obj G).X)
    (y : W ⟶ ((GroupScheme.baseChange M.hom).obj G).X)
    (h : x.left ≫ pullback.fst G.X.hom T.hom =
      b.left ≫ y.left ≫ pullback.fst G.X.hom M.hom)
    (hy : y ∈ F.val.carrier W) :
    x ∈ (restrict hG a F).val.carrier V := by
  rw [mem_restrict_iff hG, familyPointsEquiv_eq_of_original a V W b x y h]
  exact F.val.comp_mem b hy

/-- Equality of restricted families transfers local membership for points
with the same projection to the original ambient group. -/
theorem mem_of_restrict_eq (hG : IsReductive G) (a : T ⟶ M) (b : T ⟶ N)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (H : ParabolicSubgroup ((GroupScheme.baseChange N.hom).obj G))
    (hFH : restrict hG a F = restrict hG b H)
    (x : Over.mk a.left ⟶ ((GroupScheme.baseChange M.hom).obj G).X)
    (y : Over.mk b.left ⟶ ((GroupScheme.baseChange N.hom).obj G).X)
    (hxy : x.left ≫ pullback.fst G.X.hom M.hom =
      y.left ≫ pullback.fst G.X.hom N.hom)
    (hy : y ∈ H.val.carrier (Over.mk b.left)) :
    x ∈ F.val.carrier (Over.mk a.left) := by
  let R : Over T.left := Over.mk (𝟙 T.left)
  let q : (Over.map T.hom).obj R ⟶ G.X :=
    Over.homMk (x.left ≫ pullback.fst G.X.hom M.hom) (by
      have hx : x.left ≫ pullback.snd G.X.hom M.hom = a.left := Over.w x
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
      change a.left ≫ M.hom = (𝟙 T.left) ≫ T.hom
      simpa only [Category.id_comp] using Over.w a)
  let z := (baseChangePointsEquiv T.hom G R).symm q
  have hz : z.left ≫ pullback.fst G.X.hom T.hom =
      x.left ≫ pullback.fst G.X.hom M.hom :=
    congrArg (fun f => f.left) ((baseChangePointsEquiv T.hom G R).apply_symm_apply q)
  let d : (Over.map b.left).obj R ⟶ Over.mk b.left :=
    Over.homMk (𝟙 _) (by simp [R])
  have hzH := mem_restrict_of_original hG b H R (Over.mk b.left) d z y
    (by simpa only [d, Over.homMk_left, Category.id_comp] using hz.trans hxy) hy
  have hzF : z ∈ (restrict hG a F).val.carrier R := by
    rw [hFH]
    exact hzH
  rw [mem_restrict_iff hG] at hzF
  let c : Over.mk a.left ⟶ (Over.map a.left).obj R :=
    Over.homMk (𝟙 _) (by simp [R])
  have heq : c ≫ familyPointsEquiv (G := G) a R z = x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, c, Over.homMk_left, Category.id_comp,
        familyPointsEquiv_original] using hz
    · exact (Over.w (c ≫ familyPointsEquiv (G := G) a R z)).trans (Over.w x).symm
  simpa only [heq] using F.val.comp_mem c hzF

/-- Parabolicity is preserved by an isomorphism of the ambient group. -/
theorem isParabolic_comapIso {B : Scheme.{u}} {H J : GroupScheme B}
    (F : ParabolicSubgroup J) (e : H ≅ J) :
    IsParabolic (F.val.comap e.hom) := by
  let r := parabolicRepresentative F
  have h := isParabolic_range (r.hom ≫ e.inv) (r.parabolic.comp_iso e.symm)
  have hr : SubgroupFunctor.range (r.hom ≫ e.inv) =
      (SubgroupFunctor.range r.hom).comap e.hom :=
    SubgroupFunctor.range_comp_iso r.hom e.symm
  rwa [hr, r.represents.2] at h

variable (𝒰 : Scheme.OpenCover.{u} T.left)
    (F : ∀ i, ParabolicSubgroup
      ((GroupScheme.baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G))

/-- Express a family over a cover member as a subgroup of the iterated
ambient pullback, for use in subgroup descent over the parameter scheme. -/
def coverSubgroup (i : 𝒰.I₀) :
    ParabolicSubgroup ((GroupScheme.baseChange (𝒰.f i)).obj ((GroupScheme.baseChange T.hom).obj G)) :=
  let e := Descent.pullbackComparison T.hom (𝒰.f i)
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G
  ⟨(F i).val.comap e.hom, isParabolic_comapIso (F i) e⟩

/-- Ordinary matching: restricting either family along any common comparison
over the parameter scheme gives the same actual subgroup. -/
def IsMatchingParabolic (hG : IsReductive G) : Prop :=
  ∀ (i j : 𝒰.I₀) (A : Over S)
    (a : A ⟶ SubgroupFunctor.coverObj 𝒰 i)
    (b : A ⟶ SubgroupFunctor.coverObj 𝒰 j),
    a ≫ SubgroupFunctor.coverMap 𝒰 i = b ≫ SubgroupFunctor.coverMap 𝒰 j →
      restrict hG a (F i) = restrict hG b (F j)

/-- Presheaf matching implies the full all-test condition used to construct
the descended subgroup functor. -/
theorem isMatching_coverSubgroup (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG) :
    SubgroupFunctor.IsMatching 𝒰 (fun i => (coverSubgroup 𝒰 F i).val) := by
  let J := (GroupScheme.baseChange T.hom).obj G
  let e (i : 𝒰.I₀) := Descent.pullbackComparison T.hom (𝒰.f i)
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G
  intro i j V W a x hx
  let v := (baseChangePointsEquiv (𝒰.f i) J V).symm
    (a ≫ baseChangePointsEquiv (𝒰.f j) J W x)
  let xi := v ≫ (e i).hom.hom.hom
  let yj := x ≫ (e j).hom.hom.hom
  have hyj : yj ∈ (F j).val.carrier W := hx
  let A : Over S := Over.mk (V.hom ≫
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom)
  let ai : A ⟶ SubgroupFunctor.coverObj 𝒰 i := Over.homMk V.hom rfl
  have hbase : (a.left ≫ W.hom) ≫ 𝒰.f j = V.hom ≫ 𝒰.f i := by
    have ha : a.left ≫ (W.hom ≫ 𝒰.f j) = V.hom ≫ 𝒰.f i := Over.w a
    simpa only [Category.assoc] using ha
  let aj : A ⟶ SubgroupFunctor.coverObj 𝒰 j :=
    Over.homMk (a.left ≫ W.hom) (by
      change (a.left ≫ W.hom) ≫ (𝒰.f j ≫ T.hom) =
        V.hom ≫ (𝒰.f i ≫ T.hom)
      simp only [← Category.assoc, hbase])
  have hab : ai ≫ SubgroupFunctor.coverMap 𝒰 i =
      aj ≫ SubgroupFunctor.coverMap 𝒰 j := by
    apply Over.OverMorphism.ext
    exact hbase.symm
  let b : Over.mk aj.left ⟶ W := Over.homMk a.left rfl
  have hp : xi.left ≫ pullback.fst G.X.hom
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom =
      (b ≫ yj).left ≫ pullback.fst G.X.hom
        (SubgroupFunctor.coverObj 𝒰 j : Over S).hom := by
    have hv := congrArg (fun z => z.left ≫ pullback.fst G.X.hom T.hom)
      ((baseChangePointsEquiv (𝒰.f i) J V).apply_symm_apply
        (a ≫ baseChangePointsEquiv (𝒰.f j) J W x))
    simpa only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
      xi, yj, e, b, Over.homMk_left, Descent.pullbackComparison_hom_fst,
      Descent.pullbackComparison_hom_fst_assoc] using hv
  exact mem_of_restrict_eq hG ai aj (F i) (F j) (hF i j A ai aj hab)
    xi (b ≫ yj) hp ((F j).val.comp_mem b hyj)

/-- Ordinary base change is actual family restriction followed by the
direct-to-iterated ambient identification. -/
theorem baseChange_eq_comap_restrict (hG : IsReductive G)
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) (i : 𝒰.I₀) :
    F.val.baseChange (𝒰.f i) =
      (restrict hG (SubgroupFunctor.coverMap 𝒰 i) F).val.comap
        (Descent.pullbackComparison T.hom (𝒰.f i)
          (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).hom := by
  let e := Descent.pullbackComparison T.hom (𝒰.f i)
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G
  rw [restrict_val_eq]
  change F.val.baseChange (𝒰.f i) =
    ((F.val.baseChange (𝒰.f i)).comap e.inv).comap e.hom
  rw [← SubgroupFunctor.comap_comp, e.hom_inv_id, SubgroupFunctor.comap_id]

/-- Equality of actual parabolic families is detected on an open cover of
their parameter scheme. -/
theorem eq_of_restrict_cover (hG : IsReductive G)
    (F H : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G))
    (h : ∀ i, restrict hG (SubgroupFunctor.coverMap 𝒰 i) F =
      restrict hG (SubgroupFunctor.coverMap 𝒰 i) H) :
    F = H := by
  apply Subtype.ext
  apply (SubgroupFunctor.eq_iff_isRepresentedBy_baseChange_openCover 𝒰
    (parabolicRepresentative F).represents
    (parabolicRepresentative H).represents).mpr
  intro i
  rw [baseChange_eq_comap_restrict 𝒰 hG F i,
    baseChange_eq_comap_restrict 𝒰 hG H i, h i]

variable (F : ∀ i, ParabolicSubgroup
  ((GroupScheme.baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G))

/-- The actual all-test subgroup obtained from local parabolic families. -/
def matchingSubgroup : SubgroupFunctor ((GroupScheme.baseChange T.hom).obj G) :=
  SubgroupFunctor.descentSubgroup 𝒰 (fun i => (coverSubgroup 𝒰 F i).val)

/-- Under ordinary matching, the constructed subgroup has the prescribed
local base changes in the iterated ambient pullbacks. -/
theorem baseChange_matchingSubgroup (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG)
    (i : 𝒰.I₀) :
    (matchingSubgroup 𝒰 F).baseChange (𝒰.f i) = (coverSubgroup 𝒰 F i).val :=
  SubgroupFunctor.baseChange_descentSubgroup 𝒰 _
    (isMatching_coverSubgroup 𝒰 F hG hF) i

/-- The constructed subgroup has Zariski-local membership on all tests. -/
theorem isZariskiLocal_matchingSubgroup :
    SubgroupFunctor.IsZariskiLocal (matchingSubgroup 𝒰 F) :=
  SubgroupFunctor.isZariskiLocal_descentSubgroup 𝒰 _
    (fun i => isZariskiLocal_of_isParabolic (coverSubgroup 𝒰 F i))

/-- Once its parabolicity has been proved, the descended subgroup restricts
to each original actual family. -/
theorem restrict_matchingSubgroup (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG)
    (h : IsParabolic (matchingSubgroup 𝒰 F)) (i : 𝒰.I₀) :
    restrict hG (SubgroupFunctor.coverMap 𝒰 i) ⟨matchingSubgroup 𝒰 F, h⟩ = F i := by
  apply Subtype.ext
  rw [restrict_val_eq]
  change ((matchingSubgroup 𝒰 F).baseChange (𝒰.f i)).comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).inv = _
  rw [baseChange_matchingSubgroup 𝒰 F hG hF i]
  change ((F i).val.comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).hom).comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).inv = _
  rw [← SubgroupFunctor.comap_comp]
  simp only [Iso.inv_hom_id, SubgroupFunctor.comap_id]

/-- The subgroup built from ordinarily matching local parabolic families is
itself parabolic. -/
theorem isParabolic_matchingSubgroup (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG) : IsParabolic (matchingSubgroup 𝒰 F) :=
  isParabolic_descentSubgroup 𝒰 (fun i => coverSubgroup 𝒰 F i)
    (hG.baseChange T.hom) (isMatching_coverSubgroup 𝒰 F hG hF)

/-- Glue ordinarily matching actual parabolic families. -/
def matchingParabolic (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG) :
    ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G) :=
  ⟨matchingSubgroup 𝒰 F, isParabolic_matchingSubgroup 𝒰 F hG hF⟩

/-- The glued parabolic restricts to every original local family. -/
theorem restrict_matchingParabolic (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG) (i : 𝒰.I₀) :
    restrict hG (SubgroupFunctor.coverMap 𝒰 i)
      (matchingParabolic 𝒰 F hG hF) = F i :=
  restrict_matchingSubgroup 𝒰 F hG hF _ i

/-- Ordinary matching local parabolic families admit a unique actual global
parabolic family. -/
theorem existsUnique_restrict (hG : IsReductive G)
    (hF : IsMatchingParabolic 𝒰 F hG) :
    ∃! H : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G),
      ∀ i, restrict hG (SubgroupFunctor.coverMap 𝒰 i) H = F i := by
  refine ⟨matchingParabolic 𝒰 F hG hF,
    restrict_matchingParabolic 𝒰 F hG hF, ?_⟩
  intro H hH
  apply eq_of_restrict_cover 𝒰 hG
  intro i
  rw [hH i, restrict_matchingParabolic]

end Langlands.GroupScheme.ParabolicSubgroupModuli
