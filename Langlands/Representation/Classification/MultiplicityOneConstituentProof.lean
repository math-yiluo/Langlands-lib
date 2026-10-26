import Langlands.Representation.Classification.MultiplicityOneConstituentStatement
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Classification.HeadQuotientCriterionProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Basic.Complex.Basic

/-!
# Multiplicity-one criteria for actual strong constituents

The product constructions retain actual kernels and images; the aggregate
theorem proves the published focused statement.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory
open scoped MonoidAlgebra

universe uG uH uV uW uT

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Monoid H]

private def smoothProduct (P Q : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.{0, uG, uV} ℂ G :=
  SmoothRep.of (P.representation.prod Q.representation) (by
    intro x
    obtain ⟨K, hK⟩ := P.isSmooth x.1
    obtain ⟨L, hL⟩ := Q.isSmooth x.2
    refine ⟨K ⊓ L, ?_⟩
    rw [mem_fixedVectors_iff]
    intro k
    exact Prod.ext ((mem_fixedVectors_iff _ _).mp hK ⟨k, k.2.1⟩)
      ((mem_fixedVectors_iff _ _).mp hL ⟨k, k.2.2⟩))

/-- The images of the actual product inclusions split the pair of image
projections. Only preservation of zero morphisms is used here. -/
private theorem mappedProductSplitting
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H) [F.Additive]
    (P Q : SmoothRep.{0, uG, uV} ℂ G) :
    ∃ (u : (F.obj (smoothProduct P Q)).ρ.IntertwiningMap
        ((F.obj P).ρ.prod (F.obj Q).ρ))
      (v : ((F.obj P).ρ.prod (F.obj Q).ρ).IntertwiningMap
        (F.obj (smoothProduct P Q)).ρ),
      Function.Surjective u ∧ Function.Injective v := by
  let p₁ : smoothProduct P Q ⟶ P :=
    SmoothRep.ofHom (Representation.IntertwiningMap.fst ℂ P.representation Q.representation)
  let p₂ : smoothProduct P Q ⟶ Q :=
    SmoothRep.ofHom (Representation.IntertwiningMap.snd ℂ P.representation Q.representation)
  let i₁ : P ⟶ smoothProduct P Q :=
    SmoothRep.ofHom (Representation.IntertwiningMap.inl ℂ P.representation Q.representation)
  let i₂ : Q ⟶ smoothProduct P Q :=
    SmoothRep.ofHom (Representation.IntertwiningMap.inr ℂ P.representation Q.representation)
  have h₁₁ : i₁ ≫ p₁ = 𝟙 P :=
    congrArg (fun f => SmoothRep.ofHom f)
      (Representation.IntertwiningMap.fst_comp_inl (A := ℂ) (ρ := P.representation)
        (σ := Q.representation))
  have h₁₂ : i₁ ≫ p₂ = 0 :=
    congrArg (fun f => SmoothRep.ofHom f)
      (Representation.IntertwiningMap.snd_comp_inl (A := ℂ) (ρ := P.representation)
        (σ := Q.representation))
  have h₂₁ : i₂ ≫ p₁ = 0 :=
    congrArg (fun f => SmoothRep.ofHom f)
      (Representation.IntertwiningMap.fst_comp_inr (A := ℂ) (ρ := P.representation)
        (σ := Q.representation))
  have h₂₂ : i₂ ≫ p₂ = 𝟙 Q :=
    congrArg (fun f => SmoothRep.ofHom f)
      (Representation.IntertwiningMap.snd_comp_inr (A := ℂ) (ρ := P.representation)
        (σ := Q.representation))
  have H₁₁ : F.map i₁ ≫ F.map p₁ = 𝟙 (F.obj P) := by
    rw [← F.map_comp, h₁₁, F.map_id]
  have H₁₂ : F.map i₁ ≫ F.map p₂ = 0 := by
    rw [← F.map_comp, h₁₂, F.map_zero]
  have H₂₁ : F.map i₂ ≫ F.map p₁ = 0 := by
    rw [← F.map_comp, h₂₁, F.map_zero]
  have H₂₂ : F.map i₂ ≫ F.map p₂ = 𝟙 (F.obj Q) := by
    rw [← F.map_comp, h₂₂, F.map_id]
  let u := (F.map p₁).hom.prod (F.map p₂).hom
  let v : ((F.obj P).ρ.prod (F.obj Q).ρ).IntertwiningMap
      (F.obj (smoothProduct P Q)).ρ :=
    (F.map i₁).hom.comp (Representation.IntertwiningMap.fst ℂ _ _) +
      (F.map i₂).hom.comp (Representation.IntertwiningMap.snd ℂ _ _)
  have huv (x : (F.obj P).V × (F.obj Q).V) : u (v x) = x := by
    apply Prod.ext
    · change (F.map p₁).hom ((F.map i₁).hom x.1 + (F.map i₂).hom x.2) = x.1
      rw [map_add]
      have h₁ := congrArg (fun f : F.obj P ⟶ F.obj P => f.hom x.1) H₁₁
      have h₂ := congrArg (fun f : F.obj Q ⟶ F.obj P => f.hom x.2) H₂₁
      change (F.map p₁).hom ((F.map i₁).hom x.1) = x.1 at h₁
      change (F.map p₁).hom ((F.map i₂).hom x.2) = 0 at h₂
      rw [h₁, h₂, add_zero]
    · change (F.map p₂).hom ((F.map i₁).hom x.1 + (F.map i₂).hom x.2) = x.2
      rw [map_add]
      have h₁ := congrArg (fun f : F.obj P ⟶ F.obj Q => f.hom x.1) H₁₂
      have h₂ := congrArg (fun f : F.obj Q ⟶ F.obj Q => f.hom x.2) H₂₂
      change (F.map p₂).hom ((F.map i₁).hom x.1) = 0 at h₁
      change (F.map p₂).hom ((F.map i₂).hom x.2) = x.2 at h₂
      rw [h₁, h₂, zero_add]
  exact ⟨u, v, fun x => ⟨v x, huv x⟩, fun x y h =>
    (huv x).symm.trans ((congrArg u h).trans (huv y))⟩

omit [TopologicalSpace G] in
private theorem isAtom_embedding_range
    {V W : Type uV} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    (hπ : Representation.IsIrreducible π)
    (j : π.IntertwiningMap ρ) (hj : Function.Injective j) :
    IsAtom j.range := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let f : π.asModule →ₗ[ℂ[G]] e j.range :=
    (Representation.IntertwiningMap.equivLinearMapAsModule π ρ j).codRestrict
      (e j.range) (fun w => ⟨w, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hj (congrArg Subtype.val h), ?_⟩
    rintro ⟨v, w, hw⟩
    exact ⟨w, Subtype.ext hw⟩
  apply (e.isAtom_iff j.range).mp
  apply isSimpleModule_iff_isAtom.mp
  exact (f.isSimpleModule_iff_of_bijective hf).mp
    ((Representation.irreducible_iff_isSimpleModule_asModule π).mp hπ)

/-- A single count in a functor image forces equality of all actual
irreducible quotient kernels. -/
theorem multiplicityOneHeadCore
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H)
    (hA : HasJordanHolderMultiplicity (F.obj A) τ 1)
    (hex : ∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ q : A ⟶ P, Function.Surjective (SmoothRep.hom q))
    (hpos : ∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ q : A ⟶ P, Function.Surjective (SmoothRep.hom q) →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) :
    HasIrreducibleHead A.representation := by
  obtain ⟨P, hP, q, hq⟩ := hex
  obtain ⟨mP, hmP, hPpos⟩ := hpos P hP q hq
  refine ⟨P, inferInstance, inferInstance, P.representation,
    hP, SmoothRep.hom q, hq, ?_⟩
  intro W _ _ π hπ q' hq'
  by_contra hne
  let Q : SmoothRep.{0, uG, uV} ℂ G :=
    SmoothRep.of π (isSmooth_of_surjective q' hq' A.isSmooth)
  let qQ : A ⟶ Q := SmoothRep.ofHom q'
  obtain ⟨mQ, hmQ, hQpos⟩ := hpos Q hπ qQ hq'
  let r : A ⟶ smoothProduct Q P :=
    SmoothRep.ofHom (q'.prod (SmoothRep.hom q))
  have hr : Function.Surjective (SmoothRep.hom r) :=
    unequalIrreducibleQuotientKernels G A W P A.representation π P.representation
      hπ hP q' (SmoothRep.hom q) hq' hq hne
  let : Epi r := (SmoothRep.epi_iff_surjective r).mpr hr
  have hFr : Function.Surjective (F.map r).hom :=
    (Rep.epi_iff_surjective (F.map r)).mp inferInstance
  obtain ⟨u, -, hu, -⟩ := mappedProductSplitting F Q P
  let f := u.comp (F.map r).hom
  have hf : Function.Surjective f := hu.comp hFr
  have hprod := jordanHolderProductAdditivity ℂ H (F.obj Q) (F.obj P) τ
    mQ mP hmQ hmP
  have hle := jordanHolderSurjectiveMonotonicity ℂ H (F.obj A)
    (Rep.of ((F.obj Q).ρ.prod (F.obj P).ρ)) τ f hf 1 (mQ + mP) hA hprod
  omega

/-- A single count in a functor image forces equality of all actual
irreducible subrepresentation images. -/
theorem multiplicityOneSocleCore
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesMonomorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H)
    (hA : HasJordanHolderMultiplicity (F.obj A) τ 1)
    (hex : ∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ j : P ⟶ A, Function.Injective (SmoothRep.hom j))
    (hpos : ∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ j : P ⟶ A, Function.Injective (SmoothRep.hom j) →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) :
    HasIrreducibleSocle A.representation := by
  obtain ⟨P, hP, j, hj⟩ := hex
  obtain ⟨mP, hmP, hPpos⟩ := hpos P hP j hj
  refine ⟨P, inferInstance, inferInstance, P.representation,
    hP, SmoothRep.hom j, hj, ?_⟩
  intro W _ _ π hπ j' hj'
  by_contra hne
  let Q : SmoothRep.{0, uG, uV} ℂ G :=
    SmoothRep.of π (isSmooth_of_injective j' hj' A.isSmooth)
  let jQ : Q ⟶ A := SmoothRep.ofHom j'
  obtain ⟨mQ, hmQ, hQpos⟩ := hpos Q hπ jQ hj'
  have hdis : Disjoint j'.range (SmoothRep.hom j).range :=
    (isAtom_embedding_range hπ j' hj').disjoint_of_ne
      (isAtom_embedding_range hP (SmoothRep.hom j) hj)
      (fun h => hne (congrArg Subrepresentation.toSubmodule h))
  have hdis' : Disjoint j'.toLinearMap.range (SmoothRep.hom j).toLinearMap.range :=
    disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule (disjoint_iff.mp hdis))
  let r : smoothProduct Q P ⟶ A :=
    SmoothRep.ofHom
      (j'.comp (Representation.IntertwiningMap.fst ℂ _ _) +
        (SmoothRep.hom j).comp (Representation.IntertwiningMap.snd ℂ _ _))
  have hr : Function.Injective (SmoothRep.hom r) := by
    apply (injective_iff_map_eq_zero (SmoothRep.hom r)).mpr
    rintro ⟨w, p⟩ h
    change j' w + (SmoothRep.hom j) p = 0 at h
    obtain ⟨hw, hp⟩ := Submodule.disjoint_iff_add_eq_zero.mp hdis'
      ⟨w, rfl⟩ ⟨p, rfl⟩ h
    exact Prod.ext ((map_eq_zero_iff j' hj').mp hw)
      ((map_eq_zero_iff (SmoothRep.hom j) hj).mp hp)
  let : Mono r := (SmoothRep.mono_iff_injective r).mpr hr
  have hFr : Function.Injective (F.map r).hom :=
    (Rep.mono_iff_injective (F.map r)).mp inferInstance
  obtain ⟨-, v, -, hv⟩ := mappedProductSplitting F Q P
  let f := (F.map r).hom.comp v
  have hf : Function.Injective f := hFr.comp hv
  have hprod := jordanHolderProductAdditivity ℂ H (F.obj Q) (F.obj P) τ
    mQ mP hmQ hmP
  have hle := jordanHolderInjectiveMonotonicity ℂ H
    (Rep.of ((F.obj Q).ρ.prod (F.obj P).ρ)) (F.obj A) τ f hf (mQ + mP) 1 hprod hA
  omega

/-- The two actual strong-constituent criteria, with the exact aggregate
statement as target. -/
theorem multiplicityOneConstituentCriterion :
    MultiplicityOneConstituentCriterionStatement.{uG, uH, uV, uW, uT} := by
  constructor
  · intro G _ _ H _ F _ _ A τ hA hex hpos
    exact multiplicityOneHeadCore F A τ hA hex hpos
  · intro G _ _ H _ F _ _ A τ hA hex hpos
    exact multiplicityOneSocleCore F A τ hA hex hpos

end Langlands.Classification
