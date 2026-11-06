import Langlands.GroupScheme.CentralIsogeny.StabilizerTorusStatement
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.SplittingAssembly
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Stabilizers of torus-centralized points under central isogenies -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]

/-- The quotient of a torus `T` by the kernel of a homomorphism `f : T ⟶ A`
embeds into `A` as a closed subgroup through which `f` factors. -/
theorem exists_closedEmbedding_of_isTorus {T A : GroupScheme (Spec (CommRingCat.of K))}
    (hT : IsTorus T) (f : T ⟶ A) (hf : IsFinite f.hom.hom.left) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of K))) (q : T ⟶ Q) (φ : Q ⟶ A),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ IsCentralIsogeny q ∧
        IsClosedSubgroup φ ∧ q ≫ φ = f := by
  have : IsSeparated A.X.hom := fieldSeparated K A
  have : IsCommMonObj T.X := hT.isCommMonObj
  have : Smooth T.X.hom := hT.smooth
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  have hN : IsClosedSubgroup (kernelι f) :=
    inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left)
  have hNfin : IsFinite (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf
  have hNc : IsCentral (kernelι f) := fun _ _ _ _ _ => Commute.all _ _
  have hNn : (SubgroupFunctor.range (kernelι f)).IsNormal := by
    intro Z g y _ hy
    rw [mem_range_kernelι_iff] at hy ⊢
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hy, mul_one, mul_inv_cancel]
  obtain ⟨Q, q, hQs, hQa, hq, hqk⟩ :=
    exists_centralIsogeny_of_finite_central_subgroup K T (kernel f) (kernelι f)
      hN hNfin hNc hNn
  have : Smooth Q.X.hom := hQs
  have : IsFinite q.hom.hom.left := hq.isFinite
  have : Flat q.hom.hom.left := hq.flat
  have : Surjective q.hom.hom.left := hq.surjective
  have hk : kernelι q ≫ f = 0 := by
    apply Grp.hom_ext
    change (kernelι q).hom.hom ≫ f.hom.hom = 1
    apply (mem_range_kernelι_iff f _).mp
    rw [← hqk]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  let φ : Q ⟶ A := FpqcHomDescent.hom q f hk
  have hφ : q ≫ φ = f := FpqcHomDescent.fac q f hk
  have : Mono φ.hom.hom := FpqcHomDescent.mono_of_kernel_range_le q f φ hφ hqk.ge
  have : Mono φ.hom.hom.left := Over.mono_left_of_mono _
  have hcomp : q.hom.hom.left ≫ φ.hom.hom.left = f.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hφ
  have : UniversallyClosed (q.hom.hom.left ≫ φ.hom.hom.left) := by
    rw [hcomp]
    infer_instance
  have : UniversallyClosed φ.hom.hom.left :=
    UniversallyClosed.of_comp_surjective q.hom.hom.left _
  have : LocallyOfFiniteType φ.hom.hom.left := by
    have : LocallyOfFiniteType (φ.hom.hom.left ≫ A.X.hom) := by
      rw [Over.w φ.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp _ A.X.hom
  have : IsProper φ.hom.hom.left := ⟨⟩
  exact ⟨Q, q, φ, hQs, hQa, hq,
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩, hφ⟩

/-- **Stabilizer tori through central isogenies.** The stabilizer of `x` in `A` lies in the
closed torus image of `T` in `A`. -/
theorem centralIsogenyStabilizerTorus : CentralIsogenyStabilizerTorusStatement.{u} := by
  intro K _ G A π hπ a ha x T i hT hi hcent
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsFinite π.hom.hom.left := hπ.isFinite
  have : Flat π.hom.hom.left := hπ.flat
  have : Surjective π.hom.hom.left := hπ.surjective
  have hf : IsFinite (i ≫ π).hom.hom.left := by
    change IsFinite (i.hom.hom.left ≫ π.hom.hom.left)
    infer_instance
  obtain ⟨Q, q, φ, hQs, hQa, _, hφc, hφ⟩ := exists_closedEmbedding_of_isTorus hT (i ≫ π) hf
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  obtain ⟨Z, jZ, fZ, hZ, hjZ, hfZ⟩ := torusImageClosedTorusStatement K Q T hT q
  have : IsClosedImmersion jZ.hom.hom.left := hjZ
  have : IsClosedImmersion φ.hom.hom.left := hφc
  have hJ : IsClosedImmersion (jZ ≫ φ).hom.hom.left := by
    change IsClosedImmersion (jZ.hom.hom.left ≫ φ.hom.hom.left)
    infer_instance
  refine ⟨Z.toGrp, jZ ≫ φ, hZ, hJ, ?_⟩
  intro W c hc
  let r : pullback c.left π.hom.hom.left ⟶ W.left := pullback.fst _ _
  let W' : Over (Spec (CommRingCat.of K)) := Over.mk (r ≫ W.hom)
  let rr : W' ⟶ W := Over.homMk r rfl
  let h : W' ⟶ G.X := Over.homMk (pullback.snd c.left π.hom.hom.left) (by
    rw [← Over.w π.hom.hom, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w c]
    rfl)
  have hh : h ≫ π.hom.hom = rr ≫ c := Over.OverMorphism.ext pullback.condition.symm
  have hfix : a.act (rr ≫ c) (toUnit W' ≫ x) = toUnit W' ≫ x := by
    have hu : rr ≫ toUnit W = toUnit W' := comp_toUnit _
    rw [← hu, Category.assoc, ← a.naturality, hc]
  have hconj : h * (toUnit W' ≫ x) * h⁻¹ = toUnit W' ≫ x := by
    rw [← ha, hh, hfix]
  have hcomm : h * (toUnit W' ≫ x) = (toUnit W' ≫ x) * h := by
    calc h * (toUnit W' ≫ x) = h * (toUnit W' ≫ x) * h⁻¹ * h := by group
      _ = (toUnit W' ≫ x) * h := by rw [hconj]
  obtain ⟨t, ht⟩ := hcent h hcomm
  let J := (jZ ≫ φ).hom.hom.left
  let s' : pullback c.left π.hom.hom.left ⟶ Z.X.left := (t ≫ fZ.hom.hom).left
  have hs' : s' ≫ J = r ≫ c.left := by
    have : (t ≫ fZ.hom.hom) ≫ (jZ ≫ φ).hom.hom = rr ≫ c := by
      rw [← hh, ← ht, Category.assoc, Category.assoc]
      congr 1
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← Category.assoc, hfZ, hφ]
    exact congrArg (fun g => g.left) this
  have : Mono J := inferInstance
  let s : W.left ⟶ Z.X.left := EffectiveEpi.desc r s' (by
    intro Y g₁ g₂ hg
    apply (cancel_mono J).mp
    rw [Category.assoc, Category.assoc, hs', ← Category.assoc, hg, Category.assoc])
  have hrs : r ≫ s = s' := EffectiveEpi.fac r s' _
  have hsJ : s ≫ J = c.left := by
    apply (cancel_epi r).mp
    rw [← Category.assoc, hrs, hs']
  refine ⟨Over.homMk s ?_, Over.OverMorphism.ext hsJ⟩
  rw [← Over.w (jZ ≫ φ).hom.hom, ← Category.assoc]
  change (s ≫ J) ≫ A.X.hom = W.hom
  rw [hsJ, Over.w c]

end Langlands.GroupScheme
