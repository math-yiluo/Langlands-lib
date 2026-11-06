import Langlands.GroupScheme.GeneratedFamily
import Langlands.GroupScheme.Cartan.Induction
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange

/-! # Generated smooth families under arbitrary field extension -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace FamilyBaseChange

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

abbrev extension : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
abbrev bc : GroupScheme (Spec (CommRingCat.of k)) ⥤ GroupScheme (Spec (CommRingCat.of K)) :=
  GroupScheme.baseChange (extension (k := k) K)

variable {Q : GroupScheme (Spec (CommRingCat.of K))}
    (q : Q ⟶ (bc (k := k) K).obj G)

/-- A smooth connected closed ground-field subgroup whose entire extension
lies in the specified closed competitor. -/
def IsAdmissible {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left ∧
    SubgroupFunctor.range ((bc (k := k) K).map i) ≤ SubgroupFunctor.range q

omit [Smooth G.X.hom] in
private theorem exists_admissible :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsAdmissible K q i := by
  refine ⟨Grp.trivial (Over (Spec (CommRingCat.of k))), kernelUnit G,
    kernelUnit_isClosedSubgroup G, ?_, ?_, ?_, ?_⟩
  · change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  · change IsAffineHom (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of k))
    infer_instance
  · rw [SubgroupFunctor.range_baseChangeHom, range_kernelUnit, SubgroupFunctor.bot_baseChange]
    intro W
    exact bot_le

private theorem dimension_le {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    Lie.dimension H ≤ Lie.dimension G := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact LinearMap.finrank_le_finrank_of_injective (Lie.targetMapLinear_injective i k)

private theorem exists_maximal_admissible :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
      (_hs : Smooth H.X.hom) (ha : IsAffineHom H.X.hom) (_hc : ConnectedSpace H.X.left),
      IsAdmissible K q i ∧ ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G)
        (hL : IsAffineHom L.X.hom), IsAdmissible K q j →
          @Lie.dimension k _ L hL ≤ @Lie.dimension k _ H ha := by
  classical
  let P (n : ℕ) : Prop :=
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
      (hs : Smooth H.X.hom) (ha : IsAffineHom H.X.hom) (hc : ConnectedSpace H.X.left),
      IsAdmissible K q i ∧ @Lie.dimension k _ H ha = n
  have hbound : ∀ n, P n → n ≤ Lie.dimension G := by
    rintro n ⟨H, i, hs, ha, hc, hi, rfl⟩
    let : IsAffineHom H.X.hom := ha
    exact dimension_le i hi.1
  obtain ⟨H₀, i₀, hi₀⟩ := exists_admissible K q
  let : IsAffineHom H₀.X.hom := hi₀.2.2.1
  have hp₀ : P (Lie.dimension H₀) :=
    ⟨H₀, i₀, hi₀.2.1, hi₀.2.2.1, hi₀.2.2.2.1, hi₀, rfl⟩
  obtain ⟨H, i, hs, ha, hc, hi, hdim⟩ :=
    Nat.findGreatest_spec (P := P) (hbound _ hp₀) hp₀
  refine ⟨H, i, hs, ha, hc, hi, ?_⟩
  intro L j hL hj
  rw [hdim]
  exact Nat.le_findGreatest (hbound _ ⟨L, j, hj.2.1, hL, hj.2.2.2.1, hj, rfl⟩)
    ⟨L, j, hj.2.1, hL, hj.2.2.2.1, hj, rfl⟩

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- A point of a pulled-back ground-field map belongs to the competitor
as soon as its full pulled-back range does. -/
private theorem point_mem {H : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (hi : SubgroupFunctor.range ((bc (k := k) K).map i) ≤ SubgroupFunctor.range q)
    (W : Over (Spec (CommRingCat.of K)))
    (y : (Over.map (extension (k := k) K)).obj W ⟶ H.X) :
    (baseChangePointsEquiv (extension (k := k) K) G W).symm (y ≫ i.hom.hom) ∈
      (SubgroupFunctor.range q).carrier W := by
  apply hi W
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    MulEquiv.apply_symm_apply]
  exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- Taking the generated product with any smooth connected ground-field
subgroup preserves containment after extension. -/
private theorem generated_admissible {H A : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (a : A ⟶ G)
    (hi : SubgroupFunctor.range ((bc (k := k) K).map i) ≤ SubgroupFunctor.range q)
    (ha : SubgroupFunctor.range ((bc (k := k) K).map a) ≤ SubgroupFunctor.range q)
    [IsAffineHom (H.X ⊗ A.X).hom]
    (D : GeneratedImage ((fst H.X A.X ≫ i.hom.hom) * (snd H.X A.X ≫ a.hom.hom)))
    [Smooth D.group.X.hom] [IsAffineHom D.group.X.hom]
    {n : ℕ} (hn : IsDominant (D.powerMap n).left) (hq : IsClosedSubgroup q) :
    SubgroupFunctor.range ((bc (k := k) K).map D.inclusion) ≤ SubgroupFunctor.range q := by
  apply EnvelopeBaseChange.range_baseChange_le_of_points K D hn q hq
  intro W y
  rw [MonObj.comp_mul, map_mul]
  exact ((SubgroupFunctor.range q).carrier W).mul_mem
    (by simpa only [Category.assoc] using point_mem K q i hi W (y ≫ fst _ _))
    (by simpa only [Category.assoc] using point_mem K q a ha W (y ≫ snd _ _))

variable {I : Type v} (A : I → GroupScheme (Spec (CommRingCat.of k))) (a : ∀ j, A j ⟶ G)
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧ ConnectedSpace (A j).X.left)
    (hq : IsClosedSubgroup q)
    (hfamily : ∀ j, SubgroupFunctor.range ((bc (k := k) K).map (a j)) ≤ SubgroupFunctor.range q)

include hA hq hfamily in
/-- There is a smooth connected closed ground-field subgroup containing
the entire family whose extension lies in the prescribed competitor. -/
theorem exists_closed_containing_family :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsAdmissible K q i ∧ ∀ j, FactorsThrough (a j).hom.hom i := by
  classical
  obtain ⟨H, i, hs, ha, hc, hi, hmax⟩ := exists_maximal_admissible K q
  let : Smooth H.X.hom := hs
  let : IsAffineHom H.X.hom := ha
  let : ConnectedSpace H.X.left := hc
  refine ⟨H, i, hi, ?_⟩
  intro j
  let : Smooth (A j).X.hom := (hA j).1
  let : IsAffineHom (A j).X.hom := (hA j).2.1
  let : ConnectedSpace (A j).X.left := (hA j).2.2
  have hgeom := smoothConnectedAffineGeometry.2 k H (A j) hs ha hc
    (hA j).1 (hA j).2.1 (hA j).2.2
  let f : H.X ⊗ (A j).X ⟶ G.X :=
    (fst H.X (A j).X ≫ i.hom.hom) * (snd H.X (A j).X ≫ (a j).hom.hom)
  let v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X ⊗ (A j).X := lift 1 1
  have hv₀ : v₀ ≫ f = 1 := by simp [v₀, f, MonObj.comp_mul, MonObj.one_comp]
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    (H.X ⊗ (A j).X) hgeom.1 hgeom.2.1 hgeom.2.2.2 v₀ f hv₀
  let : Smooth D.group.X.hom := hD.1
  let : IsAffineHom D.group.X.hom := hD.2.1
  let : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have hconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  obtain ⟨n, _, hn⟩ := hD.2.2.2
  have hDK := generated_admissible K q i (a j) hi.2.2.2.2 (hfamily j) D hn hq
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range D.inclusion := by
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨lift y 1 ≫ D.factor, ?_⟩
    rw [Category.assoc, D.factor_comp]
    simp only [f, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, mul_one]
  let b := D.represents.factorHom i (by rw [← D.represents.2]; exact hle)
  have hb : b ≫ D.inclusion = i := D.represents.factorHom_comp _ _
  have hbclosed : IsClosedSubgroup b :=
    IsClosedSubgroup.of_comp D.closed (by rw [hb]; exact hi.1)
  have hdim : Lie.dimension D.group ≤ Lie.dimension H :=
    hmax D.group D.inclusion inferInstance ⟨D.closed, hD.1, hD.2.1, hconn, hDK⟩
  have hbiso : IsIso b := by
    by_contra hnot
    have hlt := Lie.dimension_lt_of_proper_closedSubgroup b hbclosed hnot
    omega
  let : IsIso b := hbiso
  have hinv : inv b ≫ i = D.inclusion := by
    rw [← hb, IsIso.inv_hom_id_assoc]
  refine ⟨lift 1 (𝟙 (A j).X) ≫ D.factor ≫ (inv b).hom.hom, ?_⟩
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hinv, D.factor_comp]
  simp only [f, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, one_mul, Category.id_comp]

end FamilyBaseChange

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {I : Type v} (A : I → GroupScheme (Spec (CommRingCat.of k))) (a : ∀ j, A j ⟶ G)
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧ ConnectedSpace (A j).X.left)
    {H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}

include hA in
/-- Closed algebraic generation by a smooth connected family is preserved
by every field extension, including inseparable and transcendental extensions. -/
theorem IsGeneratedByFamily.baseChange (hi : IsGeneratedByFamily A a i) :
    IsGeneratedByFamily (fun j => (FamilyBaseChange.bc (k := k) K).obj (A j))
      (fun j => (FamilyBaseChange.bc (k := k) K).map (a j)) ((FamilyBaseChange.bc (k := k) K).map i) := by
  let b := FamilyBaseChange.extension (k := k) K
  let B := GroupScheme.baseChange b
  have hir : (SubgroupFunctor.range i).IsRepresentedBy i := by
    let : IsClosedImmersion i.hom.hom.left := hi.1
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  refine ⟨hi.1.baseChange b, ?_, ?_⟩
  · intro j
    have hle := (factorsThrough_hom_iff_range_le (a j) i).mp (hi.2.1 j)
    let c := hir.factorHom (a j) hle
    have hc : c ≫ i = a j := hir.factorHom_comp _ _
    refine ⟨(B.map c).hom.hom, ?_⟩
    change (B.map c ≫ B.map i).hom.hom = (B.map (a j)).hom.hom
    rw [← Functor.map_comp, hc]
  · intro Q q hq hfamily
    obtain ⟨L, j, hj, hjfamily⟩ := FamilyBaseChange.exists_closed_containing_family K q A a hA hq
      (fun t => (factorsThrough_hom_iff_range_le _ q).mp (hfamily t))
    have hle := hi.2.2 L j hj.1 hjfamily
    apply le_trans _ hj.2.2.2.2
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    exact fun W x hx => hle _ hx

variable (hi : IsGeneratedByFamily A a i)
    {Q : GroupScheme (Spec (CommRingCat.of K))}
    (q : Q ⟶ (FamilyBaseChange.bc (k := k) K).obj G)
    (hq : IsGeneratedByFamily (fun j => (FamilyBaseChange.bc (k := k) K).obj (A j))
      (fun j => (FamilyBaseChange.bc (k := k) K).map (a j)) q)

/-- The actual base-changed generated subgroup is canonically isomorphic
to any independently chosen generated representative over the extension field. -/
def IsGeneratedByFamily.baseChangeIso :
    (FamilyBaseChange.bc (k := k) K).obj H ≅ Q := by
  have hib := IsGeneratedByFamily.baseChange K A a hA hi
  have heq : SubgroupFunctor.range ((FamilyBaseChange.bc (k := k) K).map i) =
      SubgroupFunctor.range q :=
    le_antisymm (hib.2.2 Q q hq.1 hq.2.1)
      (hq.2.2 _ _ hib.1 hib.2.1)
  let : IsClosedImmersion ((FamilyBaseChange.bc (k := k) K).map i).hom.hom.left := hib.1
  let : IsClosedImmersion q.hom.hom.left := hq.1
  have hir : (SubgroupFunctor.range ((FamilyBaseChange.bc (k := k) K).map i)).IsRepresentedBy
      ((FamilyBaseChange.bc (k := k) K).map i) := ⟨Over.mono_of_mono_left _, rfl⟩
  have hqr : (SubgroupFunctor.range ((FamilyBaseChange.bc (k := k) K).map i)).IsRepresentedBy q :=
    ⟨Over.mono_of_mono_left _, heq.symm⟩
  exact hir.isoOfIsRepresentedBy hqr

/-- The comparison preserves the actual inclusion in the extended ambient group. -/
theorem IsGeneratedByFamily.baseChangeIso_hom_comp :
    (IsGeneratedByFamily.baseChangeIso K A a hA hi q hq).hom ≫ q =
      (FamilyBaseChange.bc (k := k) K).map i := by
  unfold IsGeneratedByFamily.baseChangeIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme
