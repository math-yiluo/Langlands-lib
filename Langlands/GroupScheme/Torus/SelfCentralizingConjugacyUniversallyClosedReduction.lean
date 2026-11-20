import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyUniversallyClosedStatement
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyValuationLiftStatement
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction
import Langlands.GroupScheme.HomScheme.GeneralLinearTorusModuliAffineSumStatement
import Langlands.AlgebraicGeometry.AlgClosedValuativeSpecialization
import Langlands.AlgebraicGeometry.ClosedRationalPoints

/-! # Reducing universal closedness of the conjugacy map to valuative lifting -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SelfCentralizingConjugacyUniversallyClosedReduction

open Langlands.AlgebraicGeometry

section AlgClosedPointLift

variable {X Y : Scheme.{u}} (q : X ⟶ Y) [LocallyOfFiniteType q] [Surjective q]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Over an algebraically closed field `Ω`, every `Ω`-point of the target of a
surjective morphism locally of finite type lifts to an `Ω`-point of the source. -/
theorem exists_algClosedPoint_lift (a : Spec (CommRingCat.of Ω) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ q = a := by
  let P : Over (Spec (CommRingCat.of Ω)) := Over.mk (pullback.snd q a)
  have : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd q a)
    infer_instance
  have hne : ((⊤ : P.left.Opens) : Set P.left).Nonempty := by
    obtain ⟨z, -⟩ := (pullback.snd q a).surjective (IsLocalRing.closedPoint Ω)
    exact ⟨z, trivial⟩
  obtain ⟨x, -⟩ := ClosedRationalPoints.exists_rationalPoint_mem (X := P) ⊤ hne
  have hx : x.left ≫ pullback.snd q a = 𝟙 _ := Over.w x
  refine ⟨x.left ≫ pullback.fst q a, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
  exact Category.id_comp a

/-- **A lift of an algebraically closed point.** For a surjective morphism `q`
locally of finite type and an algebraically closed field `Ω`, a chosen `Ω`-point of
the source of `q` over a given `Ω`-point `a` of its target. -/
def algClosedPointLift (a : Spec (CommRingCat.of Ω) ⟶ Y) : Spec (CommRingCat.of Ω) ⟶ X :=
  Classical.choose (exists_algClosedPoint_lift q a)

@[reassoc (attr := simp)]
theorem algClosedPointLift_comp (a : Spec (CommRingCat.of Ω) ⟶ Y) :
    algClosedPointLift q a ≫ q = a :=
  Classical.choose_spec (exists_algClosedPoint_lift q a)

end AlgClosedPointLift

/-- Lifts for valuation subrings of algebraically closed fields pass to every
pullback square. -/
theorem hasAlgClosedValuationLifts_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    (H : HasAlgClosedValuationLifts f) {i₁ : X' ⟶ X} {i₂ : Y' ⟶ Y} {f' : X' ⟶ Y'}
    (hP : IsPullback f' i₁ i₂ f) : HasAlgClosedValuationLifts f' := by
  intro K _ _ A b a ha
  have hw : (a ≫ i₁) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ (b ≫ i₂) := by
    rw [Category.assoc, ← hP.w, ← Category.assoc, ha, Category.assoc]
  obtain ⟨l, hl₁, hl₂⟩ := H K A (b ≫ i₂) (a ≫ i₁) hw
  refine ⟨hP.lift b l hl₂.symm, ?_, hP.lift_fst _ _ _⟩
  apply hP.hom_ext
  · rw [Category.assoc, hP.lift_fst, ha]
  · rw [Category.assoc, hP.lift_snd, hl₁]

/-- A morphism from a quasi-compact scheme to a scheme that is the union of pairwise
disjoint affine opens is quasi-compact. -/
theorem quasiCompact_of_disjointAffineCover {Y M : Scheme.{u}} (φ : Y ⟶ M)
    [CompactSpace Y] {J : Type u} (U : J → M.Opens)
    (hU : ∀ k, IsAffineOpen (U k)) (hdisj : Pairwise (Function.onFun Disjoint U))
    (htop : iSup U = ⊤) : QuasiCompact φ := by
  have hclosed : ∀ k, IsClosed (U k : Set M) := by
    intro k
    rw [← isOpen_compl_iff]
    have hc : (U k : Set M)ᶜ = ⋃ l ∈ {l | l ≠ k}, (U l : Set M) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe,
        exists_prop]
      constructor
      · intro hx
        have hx' : x ∈ (iSup U : M.Opens) := by rw [htop]; trivial
        obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
        exact ⟨l, fun hlk => hx (hlk ▸ hl), hl⟩
      · rintro ⟨l, hlk, hl⟩ hk
        have h := (hdisj hlk).le_bot (show x ∈ U l ⊓ U k from ⟨hl, hk⟩)
        simp at h
    rw [hc]
    exact isOpen_biUnion fun l _ => (U l).isOpen
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U htop fun k => ?_
  have : IsAffine (U k) := hU k
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
  exact isCompact_iff_compactSpace.mp ((hclosed k).preimage φ.base.hom.continuous).isCompact

/-- **Reduction of universal closedness to valuative lifting.** The statements
`GeneralLinearAffineSumStatement` and `SelfCentralizingConjugacyValuationLiftStatement`
imply `SelfCentralizingConjugacyUniversallyClosedStatement`. The descended map `φ` is
quasi-compact because its source is quasi-compact and its target is a disjoint union
of affine opens. It is a monomorphism, and the valuative lifting statement gives lifts
for valuation subrings of algebraically closed fields; such lifts give universal
specialization. -/
theorem selfCentralizingConjugacyUniversallyClosed_of_valuationLift
    (hGL : TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u})
    (hV : SelfCentralizingConjugacyValuationLiftStatement.{u}) :
    SelfCentralizingConjugacyUniversallyClosedStatement.{u} := by
  intro R G hsm hsep hqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he hπf hπs hπl hπe
    M K j hj hK huni f hf Y p hpf hps hpl hp φ hφ
  have : Flat π.hom.hom.left := hπf
  have : Surjective π.hom.hom.left := hπs
  have : LocallyOfFinitePresentation π.hom.hom.left := hπl
  have : Flat p.left := hpf
  have : Surjective p.left := hps
  have : LocallyOfFinitePresentation p.left := hpl
  have : IsClosedImmersion e.hom.hom.left := he
  have he' : Mono e.hom.hom := Over.mono_of_mono_left _
  have hfib' : ∀ (U : Over (Spec R)) (g h : U ⟶ G.X), g ≫ p = h ≫ p ↔ g ≫ f = h ≫ f :=
    fun U g h => (hp U g h).trans
      (SelfCentralizingConjugacyClosedEmbeddingReduction.comp_eq_iff_mem_torusNormalizer
        ρ t π e hρ hcent he' hπe j hj hK huni f hf g h).symm
  have hmono : Mono φ.left := by
    have h₀ := SelfCentralizingConjugacyClosedEmbeddingReduction.mono_desc_of_fppf_fiber_iff
      p f hfib'
    have : Epi p := SelfCentralizingConjugacyClosedEmbeddingReduction.epi_of_fppf p
    have heq : φ = HomogeneousQuotientComparison.desc p f
        (fun U a b hab => (hfib' U a b).mp hab) := by
      apply (cancel_epi p).mp
      rw [hφ, HomogeneousQuotientComparison.fac_desc]
    rw [heq]
    exact h₀
  have hφl : p.left ≫ φ.left = f.left := by rw [← Over.comp_left, hφ]
  obtain ⟨J, U, hU, hdisj, htop⟩ := hGL R (Fin m) M K j hj hK huni
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : CompactSpace Y.left :=
    Function.Surjective.compactSpace p.left.base.hom.continuous hps.surj
  have hqcφ : QuasiCompact φ.left := quasiCompact_of_disjointAffineCover φ.left U hU hdisj htop
  have hlift : HasAlgClosedValuationLifts φ.left := by
    intro Ω _ _ A b a ha
    let g := algClosedPointLift p.left a
    have hgb : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ b = g ≫ f.left := by
      rw [← ha, ← algClosedPointLift_comp p.left a, Category.assoc, hφl]
    obtain ⟨h, hh⟩ := hV R G hsm hsep hqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he
      hπf hπs hπl hπe M K j hj hK huni f hf Ω A g b hgb
    refine ⟨h ≫ p.left, ?_, ?_⟩
    · apply (cancel_mono φ.left).mp
      rw [Category.assoc, Category.assoc, hφl, hh, ha]
    · rw [Category.assoc, hφl, hh]
  rw [universallyClosed_eq_universallySpecializing]
  exact ⟨fun X' Y' i₁ i₂ f' H => specializingMap_of_algClosed_valuation_lifts f'
    (hasAlgClosedValuationLifts_of_isPullback hlift H), hqcφ⟩

end SelfCentralizingConjugacyUniversallyClosedReduction

end Langlands.GroupScheme
