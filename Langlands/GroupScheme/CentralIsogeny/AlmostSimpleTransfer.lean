import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementProof
import Langlands.GroupScheme.Reductive.Noncommutativity
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties

/-! # Almost simplicity reflected through central isogenies -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A homomorphism from a smooth connected affine field group to a finite group is trivial. -/
theorem hom_eq_one_of_finite_target
    {H F : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsFinite F.X.hom] (f : H ⟶ F) : f.hom.hom = 1 := by
  let q : F ⟶ Grp.trivial (Over (Spec (CommRingCat.of k))) := default
  let b : H ⟶ F := Grp.homMk (toUnit H.X ≫ η[F.X])
  have hq : q.hom.hom = toUnit F.X := toUnit_unique _ _
  have : IsFinite q.hom.hom.left := by
    rw [hq]
    exact inferInstanceAs (IsFinite F.X.hom)
  have hf : f ≫ q = b ≫ q := by
    apply Grp.hom_ext
    exact toUnit_unique _ _
  exact congrArg (fun a => a.hom.hom) (finiteHom_cancel q hf)

/-- A central homomorphism from a smooth connected affine group into a group
with finite full centre is trivial. -/
theorem IsCentral.eq_one_of_hasFiniteCenter
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {f : H ⟶ G} (hf : IsCentral f) (hG : HasFiniteCenter G) :
    f.hom.hom = 1 := by
  obtain ⟨Z, z, hz, hfin⟩ := hG
  have : IsFinite Z.X.hom := hfin
  let a : H ⟶ Z := hz.isRepresentedBy.factorHom f (by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact hf T y)
  have ha : a ≫ z = f := hz.isRepresentedBy.factorHom_comp _ _
  have ha1 : a.hom.hom = 1 := hom_eq_one_of_finite_target a
  change f.hom.hom = 1
  rw [← ha, Grp.comp_hom_hom, ha1, MonObj.one_comp]

/-- The range functor is trivial exactly when the underlying homomorphism is
the unit morphism. -/
theorem SubgroupFunctor.range_eq_bot_iff_hom_eq_one
    {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G) :
    SubgroupFunctor.range f = ⊥ ↔ f.hom.hom = 1 := by
  constructor
  · intro h
    have hf : 𝟙 H.X ≫ f.hom.hom ∈ (SubgroupFunctor.range f).carrier H.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
    simpa only [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot,
      Category.id_comp] using hf
  · intro hf
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      change y ≫ f.hom.hom = 1
      rw [hf, MonObj.comp_one]
    · rintro rfl
      exact Subgroup.one_mem _

/-- A finite homomorphism reflects triviality on smooth connected affine
source groups. -/
theorem hom_eq_one_of_comp_eq_one
    {H D C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (p : D ⟶ C) [IsFinite p.hom.hom.left] (f : H ⟶ D)
    (hf : (f ≫ p).hom.hom = 1) : f.hom.hom = 1 := by
  let b : H ⟶ D := Grp.homMk (toUnit H.X ≫ η[D.X])
  have hfb : f ≫ p = b ≫ p := by
    apply Grp.hom_ext
    change (f ≫ p).hom.hom = (1 : H.X ⟶ D.X) ≫ p.hom.hom
    rw [hf, MonObj.one_comp]
  exact congrArg (fun a => a.hom.hom) (finiteHom_cancel p hfb)

/-- Commuting with an epimorphic range implies centrality, using the closed
fixed subgroup of the conjugation action. -/
theorem isCentral_of_commute_of_epi
    {H K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom K.X.hom]
    (f : H ⟶ G) [Epi f.hom.hom] (g : K ⟶ G)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k)))
      (x : T ⟶ H.X) (y : T ⟶ K.X),
      Commute (x ≫ f.hom.hom) (y ≫ g.hom.hom)) : IsCentral g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let a : AutomorphicAction K G := AutomorphicAction.conjugation g
  obtain ⟨F, j, hj, hjc⟩ :=
    fieldFixedSubgroupRepresentability k K G inferInstance a
  have hfF : SubgroupFunctor.range f ≤ a.fixedSubgroup := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V b z
    have e : ((z ≫ g.hom.hom) * ((b ≫ y) ≫ f.hom.hom) *
        (z ≫ g.hom.hom)⁻¹) = (b ≫ y) ≫ f.hom.hom := by
      rw [(hc V (b ≫ y) z).symm.eq, mul_inv_cancel_right]
    rw [AutomorphicAction.conjugation_act]
    simpa only [Category.assoc] using e
  have hFtop : a.fixedSubgroup = ⊤ :=
    SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le
      ⟨F, j, hjc, hj⟩ f hfF
  intro T y V b x
  have hx : x ∈ a.fixedSubgroup.carrier V := by
    rw [hFtop]
    exact Subgroup.mem_top _
  have e := hx V (𝟙 V) (b ≫ y)
  rw [Category.id_comp, AutomorphicAction.conjugation_act] at e
  rw [← Category.assoc]
  exact mul_inv_eq_iff_eq_mul.mp e

/-- The smooth connected source of a central isogeny onto an almost-simple
group is almost simple over any field. -/
theorem IsAlmostSimple.of_isCentralIsogeny
    {D C : GroupScheme (Spec (CommRingCat.of k))}
    (p : D ⟶ C) (hp : IsCentralIsogeny p) (hC : IsAlmostSimple C)
    (hDs : Smooth D.X.hom) (hDc : ConnectedSpace D.X.left) :
    IsAlmostSimple D := by
  have hD := IsSemisimple.of_isCentralIsogeny p hp hC.isSemisimple hDs hDc
  have : Smooth D.X.hom := hDs
  have : ConnectedSpace D.X.left := hDc
  have : IsAffineHom D.X.hom := hD.isConnectedReductive.isAffineHom
  have : IsAffineHom C.X.hom := hC.isSemisimple.isConnectedReductive.isAffineHom
  have : Smooth C.X.hom := hC.isSemisimple.isConnectedReductive.smooth
  have : IsFinite p.hom.hom.left := hp.isFinite
  have : Flat p.hom.hom.left := hp.flat
  have : Surjective p.hom.hom.left := hp.surjective
  have : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi p.hom.hom := Over.epi_of_epi_left _
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have hnt : SubgroupFunctor.range (𝟙 D) ≠ ⊥ := by
    intro hbot
    have hid := (SubgroupFunctor.range_eq_bot_iff_hom_eq_one (𝟙 D)).mp hbot
    change (𝟙 D.X : D.X ⟶ D.X) = 1 at hid
    have hp1 : p.hom.hom = 1 := by
      calc
        p.hom.hom = (𝟙 D.X) ≫ p.hom.hom := (Category.id_comp _).symm
        _ = 1 := by rw [hid, MonObj.one_comp]
    have hCid : (𝟙 C.X : C.X ⟶ C.X) = 1 := by
      apply (cancel_epi p.hom.hom).mp
      rw [Category.comp_id, MonObj.comp_one, hp1]
    apply hC.noncommutative
    intro T x y
    have hx : x = 1 := by
      calc
        x = x ≫ (𝟙 C.X) := (Category.comp_id _).symm
        _ = 1 := by rw [hCid, MonObj.comp_one]
    have hy : y = 1 := by
      calc
        y = y ≫ (𝟙 C.X) := (Category.comp_id _).symm
        _ = 1 := by rw [hCid, MonObj.comp_one]
    rw [hx, hy]
  refine ⟨hD, hD.noncommutative_of_nontrivial hnt, ?_⟩
  intro H j hj hs hc hn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨E, e, q, he, hqe, hqf, hqs, hqq, hql, hEs, hEc, hEa⟩ :=
    HomImage.exists_image (j ≫ p)
  have : Flat q.hom.hom.left := hqf
  have : Surjective q.hom.hom.left := hqs
  have : QuasiCompact q.hom.hom.left := hqq
  have : IsClosedImmersion e.hom.hom.left := he
  have : Mono e.hom.hom := Over.mono_of_mono_left _
  have hEn : (SubgroupFunctor.range e).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square j p q e hqe.symm hn
  rcases hC.normalSubgroup_trivial_or_full E e he hEs hEc hEn with hEb | hEt
  · left
    apply (SubgroupFunctor.range_eq_bot_iff_hom_eq_one j).mpr
    apply hom_eq_one_of_comp_eq_one p j
    rw [← hqe, Grp.comp_hom_hom,
      (SubgroupFunctor.range_eq_bot_iff_hom_eq_one e).mp hEb, MonObj.comp_one]
  · right
    have hmem : (𝟙 C.X : C.X ⟶ C.X) ∈ (SubgroupFunctor.range e).carrier C.X := by
      rw [hEt]
      exact Subgroup.mem_top _
    obtain ⟨s, hse⟩ := SubgroupFunctor.mem_range.mp hmem
    have : Epi e.hom.hom := epi_of_epi_fac hse
    have : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
    have : Epi q.hom.hom := Over.epi_of_epi_left _
    have : Epi (j ≫ p).hom.hom := by
      rw [← hqe, Grp.comp_hom_hom]
      infer_instance
    obtain ⟨_, K, i, hK, hi, _, _, hcomm, hm⟩ :=
      semisimpleNormalIsogenyComplement k D H hD j hj hs hc hn
    have : Smooth K.X.hom := hK.isConnectedReductive.smooth
    have : ConnectedSpace K.X.left := hK.isConnectedReductive.connectedSpace
    have : IsAffineHom K.X.hom := hK.isConnectedReductive.isAffineHom
    have hic : IsCentral (i ≫ p) := by
      apply isCentral_of_commute_of_epi (j ≫ p) (i ≫ p)
      intro T x y
      have h := (hcomm T x y).map ((yonedaGrp.map p).app (Opposite.op T)).hom
      change Commute ((x ≫ j.hom.hom) ≫ p.hom.hom)
        ((y ≫ i.hom.hom) ≫ p.hom.hom) at h
      simpa only [Grp.comp_hom_hom, Category.assoc] using h
    have hi1 : i.hom.hom = 1 :=
      hom_eq_one_of_comp_eq_one p i
        (hic.eq_one_of_hasFiniteCenter hC.isSemisimple.hasFiniteCenter)
    let m := commutingSubgroupMultiplicationHom j i hcomm
    have : Flat m.hom.hom.left := hm.flat
    have : Surjective m.hom.hom.left := hm.surjective
    have : Epi m.hom.hom.left := Flat.epi_of_flat_of_surjective _
    have : Epi m.hom.hom := Over.epi_of_epi_left _
    apply SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le
      ⟨H, j, hj, ⟨Over.mono_of_mono_left _, rfl⟩⟩ m
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ fst H.X K.X, ?_⟩
    change (y ≫ fst H.X K.X) ≫ j.hom.hom = y ≫ subgroupMultiplication j i
    rw [subgroupMultiplication, MonObj.comp_mul, Category.assoc,
      hi1, MonObj.comp_one, MonObj.comp_one, mul_one]

/-- Almost simplicity reflects through a central isogeny from a smooth
connected source, over an arbitrary field. -/
def AlmostSimpleCentralIsogenyStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (D C : GroupScheme (Spec (CommRingCat.of k))) (p : D ⟶ C),
    IsCentralIsogeny p → IsAlmostSimple C →
      Smooth D.X.hom → ConnectedSpace D.X.left → IsAlmostSimple D

/-- The derived almost-simple central-isogeny statement. -/
theorem almostSimpleCentralIsogeny : AlmostSimpleCentralIsogenyStatement.{u} := by
  intro k _ D C p hp hC hs hc
  exact IsAlmostSimple.of_isCentralIsogeny p hp hC hs hc

end Langlands.GroupScheme
