import Langlands.GroupScheme.Torus.MultiplicativeTypeLargestSubtorusStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeStructure
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuotients
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFinite
import Langlands.GroupScheme.Torus.DiagonalizableUniversalSubtorus
import Langlands.GroupScheme.Torus.UniversalSubtorusTransport
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.NormalizedSubgroup

/-! # Proof: the largest subtorus of a group of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LargestSubtorus

variable {k : Type u} [Field k]

set_option synthInstance.maxHeartbeats 400000 in
/-- A finite group of multiplicative type over a field is killed by a nonzero integer. -/
theorem exists_multiplication_eq_one_of_isFinite
    {Q : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Q.X]
    (hQ : IsMultiplicativeType Q) (hfin : IsFinite Q.X.hom) :
    ∃ n : ℤ, n ≠ 0 ∧ multiplication Q n = 1 := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hQ
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  have : Surjective b := hsurj
  have : Flat b := hflat
  have : QuasiCompact b := hqc
  let F := GroupScheme.baseChange b
  let D := Diagonalizable.groupScheme (CommRingCat.of K) Λ
  have hQK : IsFinite (F.obj Q).X.hom := by
    change IsFinite (pullback.snd Q.X.hom b)
    infer_instance
  have : IsIso e.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  have : IsFinite D.toGrp.X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  have : Finite Λ :=
    RelativeMultiplicativeType.finite_characters_of_isFinite (CommRingCat.of K) Λ
  let n : ℤ := (AddMonoid.exponent Λ : ℤ)
  have hn : n ≠ 0 := Int.natCast_ne_zero.mpr AddMonoid.exponent_ne_zero_of_finite
  refine ⟨n, hn, ?_⟩
  have hD : multiplication D.toGrp n = 1 :=
    Diagonalizable.multiplication_exponent_eq_one (CommRingCat.of K) Λ
  have hK' : multiplication (F.obj Q) n = 1 := by
    have h1 := multiplication_naturality e.hom n
    rw [hD] at h1
    have h2 : multiplication (F.obj Q) n = (multiplication (F.obj Q) n ≫ e.hom) ≫ e.inv := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [h2, h1]
    apply Grp.hom_ext
    simp
  apply Grp.hom_ext
  apply (Over.pullback b).map_injective
  have h3 : (Over.pullback b).map (multiplication Q n).hom.hom =
      (multiplication (F.obj Q) n).hom.hom := by
    rw [← multiplication_baseChange b Q n]
    rfl
  rw [h3, hK']
  change (1 : (Over.pullback b).obj Q.X ⟶ (Over.pullback b).obj Q.X) =
    (Over.pullback b).map (1 : Q.X ⟶ Q.X)
  exact ((Functor.homMonoidHom (Over.pullback b)).map_one).symm

/-- A closed torus of a multiplicative-type group whose fppf quotient is finite is a
universal subtorus. -/
theorem isUniversalSubtorus_of_finiteQuotient
    {H T Q : GroupScheme (Spec (CommRingCat.of k))} (hH : IsMultiplicativeType H)
    (t : T ⟶ H) (hT : IsTorus T) (ht : IsClosedSubgroup t)
    (q : H ⟶ Q) (hQ : IsFinite Q.X.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q) :
    IsUniversalSubtorus t := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hQm : IsMultiplicativeType Q := hH.of_fppfHom q
  have : IsCommMonObj Q.X := hQm.isCommMonObj
  obtain ⟨n, hn, hmul⟩ := exists_multiplication_eq_one_of_isFinite hQm hQ
  exact isUniversalSubtorus_of_kernel_torsion t q ht hT.isRelativeTorus hq.2.2.2.symm hn hmul

/-- Over a field, a universal subtorus is a largest closed subtorus for the field-level
torus predicate. -/
theorem isLargest_of_isUniversalSubtorus
    {H T : GroupScheme (Spec (CommRingCat.of k))} {t : T ⟶ H}
    (hu : IsUniversalSubtorus t) :
    IsTorus T ∧ IsClosedSubgroup t ∧
      ∀ (T' : GroupScheme (Spec (CommRingCat.of k))) (t' : T' ⟶ H),
        IsTorus T' → IsClosedSubgroup t' → ∃ f : T' ⟶ T, f ≫ t = t' :=
  ⟨hu.2.1.isTorus, hu.1, fun _ t' hT' _ => hu.factor t' hT'.isRelativeTorus⟩

/-- Product with a fixed scheme preserves flat surjective morphisms, hence epimorphisms. -/
theorem epi_whiskerLeft {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] (U : Over B) : Epi (U ◁ f) := by
  have hp : (@Flat ⊓ @Surjective : MorphismProperty Scheme.{u}) (U ◁ f).left :=
    MorphismProperty.pullbackMap (P := @Flat ⊓ @Surjective)
      (by change (@Flat ⊓ @Surjective : MorphismProperty Scheme.{u}) (𝟙 U.left)
          exact ⟨inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance⟩ (by simp) (Over.w f).symm
  obtain ⟨hf, hs⟩ := hp
  have : Flat (U ◁ f).left := hf
  have : Surjective (U ◁ f).left := hs
  have : Epi (U ◁ f).left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

/-- If a closed torus `t` of `H` is the full kernel of a homomorphism to a group killed by a
nonzero integer, and `H` is a normal closed subgroup of `G`, then the image of the torus is
normal in `G`. -/
theorem range_comp_isNormal_of_kernel_torsion
    {G H T Q : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Q.X]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) (hnorm : (SubgroupFunctor.range h).IsNormal)
    (t : T ⟶ H) (hT : IsTorus T) (q : H ⟶ Q)
    (hker : SubgroupFunctor.range t = SubgroupFunctor.range (kernelι q))
    {n : ℤ} (hn : n ≠ 0) (hQ : multiplication Q n = 1) :
    (SubgroupFunctor.range (t ≫ h)).IsNormal := by
  have : Mono h.hom.hom := hh.mono_overHom
  have : IsCommMonObj T.X := hT.isCommMonObj
  have hn' : (SubgroupFunctor.range h).IsNormalizedBy (SubgroupFunctor.range (𝟙 G)) :=
    fun U g x _ hx => hnorm U g x (Subgroup.mem_top g) hx
  let c := SubgroupFunctor.normalizedConjugation h (𝟙 G) hn'
  have hc : ∀ {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X) (x : U ⟶ H.X),
      (lift g x ≫ c) ≫ h.hom.hom = g * (x ≫ h.hom.hom) * g⁻¹ := by
    intro U g x
    rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp]
    simp
  have hcpow : ∀ {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X) (x : U ⟶ H.X),
      lift g (x ^ n) ≫ c = (lift g x ≫ c) ^ n := by
    intro U g x
    apply (cancel_mono h.hom.hom).mp
    rw [hc, GrpObj.zpow_comp, GrpObj.zpow_comp, hc, conj_zpow]
  let TT : CommGroupScheme (Spec (CommRingCat.of k)) := { T with comm := inferInstance }
  obtain ⟨hflat, hsurj⟩ := IsTorus.flat_and_surjective_multiplication (T := TT) hT hn
  have : Flat (multiplication T n).hom.hom.left := hflat
  have : Surjective (multiplication T n).hom.hom.left := hsurj
  have hepi : Epi (G.X ◁ (multiplication T n).hom.hom) :=
    epi_whiskerLeft (multiplication T n).hom.hom G.X
  let φ : G.X ⊗ T.X ⟶ Q.X :=
    lift (fst G.X T.X) (snd G.X T.X ≫ t.hom.hom) ≫ c ≫ q.hom.hom
  have hφ : φ = 1 := by
    apply (cancel_epi (G.X ◁ (multiplication T n).hom.hom)).mp
    rw [MonObj.comp_one]
    have hl : (G.X ◁ (multiplication T n).hom.hom) ≫
        lift (fst G.X T.X) (snd G.X T.X ≫ t.hom.hom) =
        lift (fst G.X T.X) ((snd G.X T.X ≫ t.hom.hom) ^ n) := by
      apply hom_ext
      · simp
      · simp only [whiskerLeft_snd_assoc, comp_lift, lift_snd]
        rw [← Category.assoc, points_multiplication, GrpObj.zpow_comp]
    simp only [φ]
    rw [← Category.assoc, hl, ← Category.assoc, hcpow, GrpObj.zpow_comp,
      ← points_multiplication, hQ]
    simp
  intro U g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hmem : lift g (y ≫ t.hom.hom) ≫ c ∈ (SubgroupFunctor.range t).carrier U := by
    rw [hker, mem_range_kernelι_iff]
    have e := congrArg (fun f => lift g y ≫ f) hφ
    simp only [φ, MonObj.comp_one] at e
    rw [← e]
    simp only [← Category.assoc, comp_lift, lift_fst, lift_snd]
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hmem
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hz, hc]
  simp [Category.assoc]

end LargestSubtorus

open LargestSubtorus in
/-- **The largest subtorus of a group of multiplicative type** (Milne, *Algebraic Groups*,
Notation 12.29), in every universe. -/
theorem multiplicativeTypeLargestSubtorus : MultiplicativeTypeLargestSubtorusStatement.{u} := by
  intro k _ H hH
  obtain ⟨T₁, j₁, hT₁, hj₁, Q, q, hQ, hq⟩ := hH.exists_torus_finiteQuotient
  have hu₁ : IsUniversalSubtorus j₁ :=
    isUniversalSubtorus_of_finiteQuotient hH j₁ hT₁ hj₁ q hQ hq
  have huniv : ∀ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
      IsTorus T → IsClosedSubgroup t →
      (∀ (T' : GroupScheme (Spec (CommRingCat.of k))) (t' : T' ⟶ H),
        IsTorus T' → IsClosedSubgroup t' → ∃ f : T' ⟶ T, f ≫ t = t') →
      IsUniversalSubtorus t := by
    intro T t hT ht hfac
    obtain ⟨a, ha⟩ := hfac T₁ j₁ hT₁ hj₁
    exact hu₁.of_factor ht hT.isRelativeTorus a ha
  refine ⟨⟨T₁, j₁, isLargest_of_isUniversalSubtorus hu₁⟩, ?_, ?_, ?_⟩
  · rintro T t hT ht ⟨Q', q', hQ', hq'⟩
    exact isLargest_of_isUniversalSubtorus
      (isUniversalSubtorus_of_finiteQuotient hH t hT ht q' hQ' hq')
  · rintro K _ _ T t ⟨hT, ht, hfac⟩
    exact isLargest_of_isUniversalSubtorus
      ((huniv T t hT ht hfac).baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  · rintro G h - - hh hnorm T t ⟨hT, ht, hfac⟩
    have hu := huniv T t hT ht hfac
    have : Flat q.hom.hom.left := hq.1
    have : Surjective q.hom.hom.left := hq.2.1
    have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
    have hQm : IsMultiplicativeType Q := hH.of_fppfHom q
    have : IsCommMonObj Q.X := hQm.isCommMonObj
    obtain ⟨n, hn, hmul⟩ := exists_multiplication_eq_one_of_isFinite hQm hQ
    have hker : SubgroupFunctor.range t = SubgroupFunctor.range (kernelι q) := by
      rw [← hu₁.range_eq hu, hq.2.2.2]
    exact range_comp_isNormal_of_kernel_torsion h hh hnorm t hT q hker hn hmul

end Langlands.GroupScheme
