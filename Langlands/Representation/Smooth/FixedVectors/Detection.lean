import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Compact.SurjectivityProof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace Langlands

open scoped MonoidAlgebra

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field R] [Group G] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Fixed vectors generate a semisimple representation if they meet every
simple subrepresentation nontrivially. -/
theorem eq_top_of_fixedVectors_le_of_semisimple
    (ρ : Representation R G V) (K : Subgroup G)
    [Representation.IsSemisimpleRepresentation ρ]
    (hK : ∀ S : Subrepresentation ρ, IsAtom S →
      ∃ v : V, v ∈ S ∧ v ∈ fixedVectors ρ K ∧ v ≠ 0)
    (T : Subrepresentation ρ) (hT : fixedVectors ρ K ≤ T.toSubmodule) : T = ⊤ := by
  let : IsSemisimpleModule R[G] ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      inferInstance
  have htop : T.asSubmodule = ⊤ := by
    apply top_unique
    rw [← IsSemisimpleModule.sSup_simples_eq_top R[G] ρ.asModule]
    apply sSup_le
    intro M hM
    let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' M
    have hS : IsAtom S := by
      apply (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S).mp
      exact isSimpleModule_iff_isAtom.mp hM
    obtain ⟨v, hvS, hvK, hv⟩ := hK S hS
    have hne : S ⊓ T ≠ ⊥ := by
      intro h
      have hmem : v ∈ (S ⊓ T).toSubmodule := ⟨hvS, hT hvK⟩
      rw [h] at hmem
      exact hv hmem
    have heq : S ⊓ T = S := (hS.le_iff_eq hne).mp inf_le_left
    have hle : S ≤ T := by
      rw [← heq]
      exact inf_le_right
    exact hle
  apply Subrepresentation.subrepresentationSubmoduleOrderIso.injective
  exact htop

/-- An intertwiner is detected by its restriction to fixed vectors when those
fixed vectors generate the source. -/
theorem intertwiner_eq_zero_of_fixedVectorsMap_eq_zero
    {ρ : Representation R G V} {σ : Representation R G W}
    (K : Subgroup G)
    (hgen : ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤)
    (f : ρ.IntertwiningMap σ) (hf : fixedVectorsMap f K = 0) : f = 0 := by
  have hk : f.ker = ⊤ := hgen f.ker (by
    intro v hv
    have h := LinearMap.congr_fun hf ⟨v, hv⟩
    exact congrArg Subtype.val h)
  ext v
  have hmem : v ∈ f.ker.toSubmodule := by rw [hk]; trivial
  exact hmem

private theorem finrank_lt_of_injective_not_surjective
    [FiniteDimensional R W] (f : V →ₗ[R] W)
    (hi : Function.Injective f) (hs : ¬ Function.Surjective f) :
    Module.finrank R V < Module.finrank R W := by
  let : FiniteDimensional R V := Module.Finite.of_injective f hi
  refine lt_of_le_of_ne (LinearMap.finrank_le_finrank_of_injective hi) ?_
  intro heq
  exact hs ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hi)

private theorem finrank_lt_of_surjective_not_injective
    [FiniteDimensional R V] (f : V →ₗ[R] W)
    (hs : Function.Surjective f) (hi : ¬ Function.Injective f) :
    Module.finrank R W < Module.finrank R V := by
  let : FiniteDimensional R W := Module.Finite.of_surjective f hs
  refine lt_of_le_of_ne (LinearMap.finrank_le_finrank_of_surjective hs) ?_
  intro heq
  exact hi ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).mpr hs)

namespace SmoothRep

open CategoryTheory

variable [TopologicalSpace G]

/-- A nonzero restriction to fixed vectors makes the fixed-vector dimension of
the kernel strictly smaller. -/
theorem finrank_fixedVectors_kernel_lt
    {A : SmoothRep.{uR, uG, uV} R G} (K : Subgroup G)
    [FiniteDimensional R (fixedVectors A.representation K)] (f : A ⟶ A)
    (hf : fixedVectorsMap (hom f) K ≠ 0) :
    Module.finrank R (fixedVectors (kernel f).representation K) <
      Module.finrank R (fixedVectors A.representation K) := by
  let j := fixedVectorsMap (hom (kernelι f)) K
  apply finrank_lt_of_injective_not_surjective j
    (fixedVectorsMap_injective _ (subtype_injective A (hom f).ker) K)
  intro hs
  apply hf
  ext v
  obtain ⟨w, hw⟩ := hs v
  have hw' : (hom (kernelι f)) w.val = (v : A) := congrArg Subtype.val hw
  change (hom f) (v : A) = 0
  rw [← hw']
  exact w.val.property

variable [IsTopologicalGroup G]

private def rangeFactor {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) : A ⟶ image f :=
  ofHom {
    toLinearMap := (hom f).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }

/-- A noninjective endomorphism of the finite fixed-vector space has image
representation with strictly fewer compact-open fixed vectors. -/
theorem finrank_fixedVectors_image_lt
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)] (f : A ⟶ A)
    (hf : ¬ Function.Injective (fixedVectorsMap (hom f) K.toSubgroup)) :
    Module.finrank ℂ (fixedVectors (image f).representation K.toSubgroup) <
      Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) := by
  let j := fixedVectorsMap (hom (imageι f)) K.toSubgroup
  have he : Function.Surjective
      (fixedVectorsMap (hom (rangeFactor f)) K.toSubgroup) :=
    Compact.fixedVectorSurjectivity G A (image f) A.representation (image f).representation
      A.isSmooth (image f).isSmooth K hK (hom (rangeFactor f))
      (by rintro ⟨v, w, hw⟩; exact ⟨w, Subtype.ext hw⟩)
  apply finrank_lt_of_injective_not_surjective j
    (fixedVectorsMap_injective _ (subtype_injective A (hom f).range) K.toSubgroup)
  intro hs
  apply hf
  apply (LinearMap.injective_iff_surjective).mpr
  intro v
  obtain ⟨w, hw⟩ := hs v
  obtain ⟨u, hu⟩ := he w
  refine ⟨u, ?_⟩
  exact (congrArg j hu).trans hw

/-- A nonzero fixed-vector endomorphism gives a cokernel with strictly fewer
compact-open fixed vectors. -/
theorem finrank_fixedVectors_cokernel_lt
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)] (f : A ⟶ A)
    (hf : fixedVectorsMap (hom f) K.toSubgroup ≠ 0) :
    Module.finrank ℂ (fixedVectors (cokernel f).representation K.toSubgroup) <
      Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) := by
  let q := fixedVectorsMap (hom (cokernelπ f)) K.toSubgroup
  have hq : Function.Surjective q :=
    Compact.fixedVectorSurjectivity G A (cokernel f) A.representation
      (cokernel f).representation A.isSmooth (cokernel f).isSmooth K hK
      (hom (cokernelπ f)) (mkQ_surjective A (hom f).range)
  apply finrank_lt_of_surjective_not_injective q hq
  intro hi
  apply hf
  ext v
  have hz : q (fixedVectorsMap (hom f) K.toSubgroup v) = q 0 := by
    apply Subtype.ext
    change (hom (cokernelπ f)) (hom f (v : A)) = 0
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨(v : A), rfl⟩
  exact congrArg Subtype.val (hi hz)

/-- An endomorphism preserving a subquotient presentation and acting by zero
on a quotient with nonzero fixed vectors cannot be injective on fixed vectors. -/
theorem not_injective_fixedVectorsMap_of_subquotient_witness
    {A C D : SmoothRep.{0, uG, uV} ℂ G}
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)]
    [Nontrivial (fixedVectors D.representation K.toSubgroup)]
    (i : C ⟶ A) (q : C ⟶ D)
    (hi : Function.Injective (hom i)) (hq : Function.Surjective (hom q))
    (fA : A ⟶ A) (fC : C ⟶ C)
    (hcomm : (hom i).comp (hom fC) = (hom fA).comp (hom i))
    (hzero : (hom q).comp (hom fC) = 0) :
    ¬ Function.Injective (fixedVectorsMap (hom fA) K.toSubgroup) := by
  let j := fixedVectorsMap (hom i) K.toSubgroup
  let t := fixedVectorsMap (hom fC) K.toSubgroup
  let r := fixedVectorsMap (hom q) K.toSubgroup
  have hj : Function.Injective j := fixedVectorsMap_injective _ hi K.toSubgroup
  let : FiniteDimensional ℂ (fixedVectors C.representation K.toSubgroup) :=
    Module.Finite.of_injective j hj
  have hr : Function.Surjective r :=
    Compact.fixedVectorSurjectivity G C D C.representation D.representation
      C.isSmooth D.isSmooth K hK (hom q) hq
  intro hA
  have ht : Function.Injective t := by
    intro x y hxy
    apply hj
    apply hA
    apply Subtype.ext
    have hxc := congrArg (fun f => f (x : C)) hcomm
    have hyc := congrArg (fun f => f (y : C)) hcomm
    exact hxc.symm.trans ((congrArg Subtype.val (congrArg j hxy)).trans hyc)
  have hts : Function.Surjective t := LinearMap.injective_iff_surjective.mp ht
  obtain ⟨d, hd⟩ := exists_ne (0 : fixedVectors D.representation K.toSubgroup)
  obtain ⟨c, hc⟩ := hr d
  obtain ⟨b, hb⟩ := hts c
  apply hd
  apply Subtype.ext
  have hz := congrArg (fun f => f (b : C)) hzero
  have hbr : r (t b) = d := (congrArg r hb).trans hc
  exact (congrArg Subtype.val hbr).symm.trans hz

end SmoothRep

end Langlands
