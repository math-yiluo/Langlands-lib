import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints

/-! # Matching admissible families and all-test subgroup descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M N T : Over S}

/-- Equality of restricted families transfers local membership for points
with the same projection to the original ambient group. -/
theorem mem_of_restrict_eq (a : T ⟶ M) (b : T ⟶ N)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G))
    (H : AdmissibleSubgroup ((baseChange N.hom).obj G))
    (hFH : restrict a F = restrict b H)
    (x : Over.mk a.left ⟶ ((baseChange M.hom).obj G).X)
    (y : Over.mk b.left ⟶ ((baseChange N.hom).obj G).X)
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
  have hzH := mem_restrict_of_original b H R (Over.mk b.left) d z y
    (by simpa only [d, Over.homMk_left, Category.id_comp] using hz.trans hxy) hy
  have hzF : z ∈ (restrict a F).val.carrier R := by
    rw [hFH]
    exact hzH
  rw [mem_restrict_iff] at hzF
  let c : Over.mk a.left ⟶ (Over.map a.left).obj R :=
    Over.homMk (𝟙 _) (by simp [R])
  have heq : c ≫ familyPointsEquiv (G := G) a R z = x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, c, Over.homMk_left, Category.id_comp,
        familyPointsEquiv_original] using hz
    · exact (Over.w (c ≫ familyPointsEquiv (G := G) a R z)).trans (Over.w x).symm
  simpa only [heq] using F.val.comp_mem c hzF

/-- Admissibility is preserved by an isomorphism of the ambient group. -/
theorem isAdmissible_comapIso {B : Scheme.{u}} {H J : GroupScheme B}
    (F : AdmissibleSubgroup J) (e : H ≅ J) :
    IsAdmissible (F.val.comap e.hom) := by
  let r := admissibleRepresentative F
  have h := isAdmissible_range (r.hom ≫ e.inv) (r.closed.comp_iso e.symm) r.torus
  have hr : SubgroupFunctor.range (r.hom ≫ e.inv) =
      (SubgroupFunctor.range r.hom).comap e.hom :=
    SubgroupFunctor.range_comp_iso r.hom e.symm
  rwa [hr, r.represents.2] at h

variable (𝒰 : Scheme.OpenCover.{u} T.left)
    (F : ∀ i, AdmissibleSubgroup
      ((baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G))

/-- Express a family over a cover member as a subgroup of the iterated
ambient pullback, for use in subgroup descent over the parameter scheme. -/
def coverSubgroup (i : 𝒰.I₀) :
    AdmissibleSubgroup ((baseChange (𝒰.f i)).obj ((baseChange T.hom).obj G)) :=
  let e := Descent.pullbackComparison T.hom (𝒰.f i)
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G
  ⟨(F i).val.comap e.hom, isAdmissible_comapIso (F i) e⟩

/-- Ordinary matching: restricting either family along any common comparison
over the parameter scheme gives the same actual subgroup. -/
def IsMatchingAdmissible : Prop :=
  ∀ (i j : 𝒰.I₀) (A : Over S)
    (a : A ⟶ SubgroupFunctor.coverObj 𝒰 i)
    (b : A ⟶ SubgroupFunctor.coverObj 𝒰 j),
    a ≫ SubgroupFunctor.coverMap 𝒰 i = b ≫ SubgroupFunctor.coverMap 𝒰 j →
      restrict a (F i) = restrict b (F j)

/-- Presheaf matching implies the full all-test condition used to construct
the descended subgroup functor. -/
theorem isMatching_coverSubgroup (hF : IsMatchingAdmissible 𝒰 F) :
    SubgroupFunctor.IsMatching 𝒰 (fun i => (coverSubgroup 𝒰 F i).val) := by
  let J := (baseChange T.hom).obj G
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
  exact mem_of_restrict_eq ai aj (F i) (F j) (hF i j A ai aj hab)
    xi (b ≫ yj) hp ((F j).val.comp_mem b hyj)

end Langlands.GroupScheme.TorusSubgroupModuli
