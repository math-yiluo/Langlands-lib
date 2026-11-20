import Langlands.GroupScheme.IdentityJetBaseChange
import Langlands.GroupScheme.IdentityJetFiniteProjection
import Langlands.RingTheory.Smooth.SectionJetSmoothRankLocus
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.LocallyFree

/-! # Smoothness and rank along the unit in affine coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

/-- Formal smoothness of the actual stalk maps at the points of the unit section. -/
def SmoothAlongUnit {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  ∀ s : S, (G.X.hom.stalkMap (G.identitySection s)).hom.FormallySmooth

/-- Formal smoothness at the unit stalks, together with a flat first-jet projection
of rank `1 + r` at every base point. -/
def SmoothAlongUnitOfRank {S : Scheme.{u}} (G : GroupScheme S) (r : ℕ) : Prop :=
  SmoothAlongUnit G ∧ Flat (projection G 1) ∧ ∀ s : S, (projection G 1).finrank s = 1 + r

section Neighborhood

variable {S W : Scheme.{u}} [IsAffine S] [IsAffine W] (G : GroupScheme S)
    (v : W ⟶ G.X.left) [IsOpenImmersion v] (e : S ⟶ W) (he : e ≫ v = G.identitySection)

/-- The algebra of the affine unit neighborhood over the affine base. -/
abbrev neighborhoodAlgebra : Algebra Γ(S, ⊤) Γ(W, ⊤) := (v ≫ G.X.hom).appTop.hom.toAlgebra

/-- The affine algebra augmentation induced by the lifted unit section. -/
def neighborhoodAugmentation :
    letI := neighborhoodAlgebra G v
    Γ(W, ⊤) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) := by
  letI := neighborhoodAlgebra G v
  refine { toRingHom := e.appTop.hom, commutes' := ?_ }
  intro r
  have h : e ≫ (v ≫ G.X.hom) = 𝟙 S := by rw [← Category.assoc, he, G.identitySection_comp]
  have hh := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hh
  exact ConcreteCategory.congr_hom hh r

private theorem ker_ideal_top {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    f.ker.ideal ⟨⊤, isAffineOpen_top Y⟩ = RingHom.ker f.appTop.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp

private theorem ker_of_open_factor {X Y V : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (v : V ⟶ Y) [IsOpenImmersion v] (j : X ⟶ V) (hj : j ≫ v = i) :
    j.ker = i.ker.comap v := by
  have h : IsPullback j (𝟙 X) v i := IsPullback.of_vert_isIso_mono ⟨by simpa using hj⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

section Separated

variable [IsSeparated G.X.hom]

/-- The actual identity-jet section algebra, without assuming smoothness of
the group, is the augmentation quotient on any affine unit neighborhood. -/
def neighborhoodJetAlgEquiv (n : ℕ) :
    letI := neighborhoodAlgebra G v
    letI := (projection G n).appTop.hom.toAlgebra
    Algebra.SectionJet.Quotient (neighborhoodAugmentation G v e he) n ≃ₐ[Γ(S, ⊤)]
      Γ(scheme G n, ⊤) := by
  letI := neighborhoodAlgebra G v
  letI := (projection G n).appTop.hom.toAlgebra
  have : IsAffineHom (projection G n) := projection_isAffineHom_of_isSeparated G n
  have : IsAffine (scheme G n) := isAffine_of_isAffineHom (projection G n)
  let k := inclusion G n
  let q := v ≫ G.X.hom
  have hsub : Set.range k ⊆ Set.range v := by
    rw [show Set.range k = Set.range G.identitySection from range_inclusion_eq_range_identitySection G n, ← he]
    exact Set.range_comp_subset_range e v
  let j := IsOpenImmersion.lift v k hsub
  have hj : j ≫ v = k := IsOpenImmersion.lift_fac _ _ _
  have hjq : j ≫ q = projection G n := by rw [← Category.assoc, hj]; rfl
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ v) := hj ▸ (inclusion_isClosedImmersion G n)
    exact IsClosedImmersion.of_comp _ v
  have hker : RingHom.ker j.appTop.hom = RingHom.ker (neighborhoodAugmentation G v e he) ^ (n + 1) := by
    have h₁ := ker_of_open_factor k v j hj
    have h₂ := ker_of_open_factor G.identitySection v e he
    rw [show k.ker = ideal G n from Scheme.IdealSheafData.ker_subschemeι _] at h₁
    change j.ker = (G.identitySection.ker ^ (n + 1)).comap v at h₁
    rw [idealSheaf_comap_pow, ← h₂] at h₁
    have htop := congrArg (fun I : W.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) h₁
    change RingHom.ker j.appTop.hom = RingHom.ker e.appTop.hom ^ (n + 1)
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ker_ideal_top] using htop
  have hjSurj : Function.Surjective j.appTop := (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
  let E := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hjSurj)
  refine { toRingEquiv := E, commutes' := ?_ }
  intro r
  change j.appTop (q.appTop r) = (projection G n).appTop r
  exact ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop j q).symm.trans
    (congrArg Scheme.Hom.appTop hjq)) r

end Separated

private theorem primeIdealOf_top {X : Scheme.{u}} [IsAffine X] (x : X) :
    (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ = X.isoSpec.hom x := by
  apply X.isoSpec.inv.isOpenEmbedding.injective
  rw [← IsAffineOpen.fromSpec_top, IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_top]
  simp [← Scheme.Hom.comp_apply]

variable [LocallyOfFinitePresentation G.X.hom]

/-- Smoothness of the group along its unit is the smoothness condition on
primes of any affine neighborhood along the restricted augmentation. -/
theorem smoothAlongUnit_iff_neighborhood :
    letI := neighborhoodAlgebra G v
    SmoothAlongUnit G ↔ ∀ (p : Ideal Γ(S, ⊤)) [p.IsPrime],
      Algebra.IsSmoothAt Γ(S, ⊤) (p.comap (neighborhoodAugmentation G v e he).toRingHom) := by
  let := neighborhoodAlgebra G v
  let q := v ≫ G.X.hom
  let ε := neighborhoodAugmentation G v e he
  have h (s : S) :
      (G.X.hom.stalkMap (G.identitySection s)).hom.FormallySmooth ↔
        Algebra.IsSmoothAt Γ(S, ⊤) ((S.isoSpec.hom s).asIdeal.comap ε.toRingHom) := by
    have he' : v (e s) = G.identitySection s := by
      rw [← Scheme.Hom.comp_apply, he]
    have hpoint : (S.isoSpec.hom s).comap e.appTop.hom = W.isoSpec.hom (e s) := by
      exact congrArg (fun f : S ⟶ Spec Γ(W, ⊤) => f s) (Scheme.isoSpec_hom_naturality e)
    rw [← Scheme.Hom.mem_smoothLocus, ← he', ← Scheme.Hom.mem_preimage,
      Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_smoothLocus]
    change (q.stalkMap (e s)).hom.FormallySmooth ↔
      (S.isoSpec.hom s).comap e.appTop.hom ∈ Algebra.smoothLocus Γ(S, ⊤) Γ(W, ⊤)
    rw [hpoint]
    have htop : q.appLE ⊤ ⊤ (by simp) = q.appTop :=
      (Scheme.Hom.app_eq_appLE q (U := ⊤)).symm
    have hstalk := formallySmooth_stalkMap_iff (f := q) (x := e s) ⊤ (isAffineOpen_top S)
      ⊤ (isAffineOpen_top W) (by simp) (by trivial)
    dsimp only at hstalk
    rw [htop, primeIdealOf_top] at hstalk
    exact hstalk
  constructor
  · intro hs p hp
    let s := S.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(S, ⊤))
    have hs' : S.isoSpec.hom s = (⟨p, hp⟩ : PrimeSpectrum Γ(S, ⊤)) := by
      simp [s, ← Scheme.Hom.comp_apply]
    have hh := (h s).mp (hs s)
    rwa [hs'] at hh
  · intro hp s
    exact (h s).mpr (hp (S.isoSpec.hom s).asIdeal)

private theorem finrank_eq_rankAtStalk {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    letI := f.appTop.hom.toAlgebra
    f.finrank y = Module.rankAtStalk Γ(X, ⊤) (Y.isoSpec.hom y) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr f.flat_appTop
  let : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
  have hp : IsPullback X.isoSpec.hom f (Spec.map f.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hp,
    Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]
  rfl

variable [IsSeparated G.X.hom]

private theorem neighborhoodJetRank_iff [Flat (projection G 1)] (r : ℕ) :
    letI := neighborhoodAlgebra G v
    (∀ s : S, (projection G 1).finrank s = 1 + r) ↔
    ∀ p : PrimeSpectrum Γ(S, ⊤), Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.Fiber (RingHom.ker (neighborhoodAugmentation G v e he)).Cotangent) = r := by
  let := neighborhoodAlgebra G v
  let R := Γ(S, ⊤)
  let ε := neighborhoodAugmentation G v e he
  let C := Γ(scheme G 1, ⊤)
  let J := (RingHom.ker ε).Cotangent
  let := (projection G 1).appTop.hom.toAlgebra
  have : IsFinite (projection G 1) := finite_projection G 1
  have : IsAffine (scheme G 1) := isAffine_of_isAffineHom (projection G 1)
  have : Module.Flat R C := (projection G 1).flat_appTop
  have : Module.Finite R C := (projection G 1).finite_appTop
  let E : C ≃ₗ[R] R × J := (neighborhoodJetAlgEquiv G v e he 1).symm.toLinearEquiv ≪≫ₗ
    Algebra.SectionJet.firstSplitEquiv ε
  have : Module.Flat R (R × J) := Module.Flat.of_linearEquiv E.symm
  have : Module.Flat R J := Module.Flat.of_retract (LinearMap.inr R R J) (LinearMap.snd R R J) (by ext; rfl)
  have : Module.Finite R J := Module.Finite.of_surjective
    ((LinearMap.snd R R J).comp E.toLinearMap)
    ((LinearMap.snd_surjective (R := R) (M := R) (M₂ := J)).comp E.surjective)
  have hr (p : PrimeSpectrum R) : Module.rankAtStalk C p = 1 +
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber J) := by
    have : Nontrivial R := nontrivial_of_ne (0 : R) 1
      (fun h => p.isPrime.one_notMem (h ▸ p.asIdeal.zero_mem))
    rw [Module.rankAtStalk_eq_of_equiv E, Module.rankAtStalk_prod, Pi.add_apply,
      Module.rankAtStalk_self, Pi.one_apply, Module.rankAtStalk_eq]
  constructor
  · intro hs p
    let s := S.isoSpec.inv p
    have hp : S.isoSpec.hom s = p := by simp [s, ← Scheme.Hom.comp_apply]
    have h := hs s
    rw [finrank_eq_rankAtStalk, hp, hr] at h
    exact Nat.add_left_cancel h
  · intro hp s
    rw [finrank_eq_rankAtStalk, hr, hp]

/-- Affine recognition of fixed-rank smoothness along the actual unit. -/
theorem smoothAlongUnitOfRank_iff_neighborhood (r : ℕ) :
    letI := neighborhoodAlgebra G v
    SmoothAlongUnitOfRank G r ↔
      Algebra.SectionJet.SmoothAlongSectionOfRank (neighborhoodAugmentation G v e he) r := by
  let := neighborhoodAlgebra G v
  rw [SmoothAlongUnitOfRank, Algebra.SectionJet.SmoothAlongSectionOfRank,
    smoothAlongUnit_iff_neighborhood G v e he]
  refine and_congr_right fun hs => ⟨?_, ?_⟩
  · rintro ⟨hflat, hr⟩
    exact (neighborhoodJetRank_iff G v e he r).mp hr
  · intro hr
    let R := Γ(S, ⊤)
    let ε := neighborhoodAugmentation G v e he
    let C := Γ(scheme G 1, ⊤)
    let q := v ≫ G.X.hom
    have : LocallyOfFinitePresentation q := inferInstance
    have : Algebra.FinitePresentation R Γ(W, ⊤) := HasRingHomProperty.appTop
      (P := @LocallyOfFinitePresentation) q inferInstance
    obtain ⟨a, ha, hsmooth⟩ := Algebra.SectionJet.exists_smooth_away_of_section ε hs
    let : Algebra.Smooth R (Localization.Away a) := hsmooth
    have : Module.Projective R (RingHom.ker ε).Cotangent :=
      Algebra.SectionJet.projective_cotangent_of_smooth_away ε a (ha ▸ isUnit_one)
    let : Algebra R C := (projection G 1).appTop.hom.toAlgebra
    let E := (neighborhoodJetAlgEquiv G v e he 1).symm.toLinearEquiv ≪≫ₗ
      Algebra.SectionJet.firstSplitEquiv ε
    have : Module.Flat R C := Module.Flat.of_linearEquiv E
    have : IsAffineHom (projection G 1) := projection_isAffineHom_of_isSeparated G 1
    have : IsAffine (scheme G 1) := isAffine_of_isAffineHom (projection G 1)
    have : Flat (projection G 1) := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
      (inferInstanceAs (Module.Flat R C))
    exact ⟨inferInstance, (neighborhoodJetRank_iff G v e he r).mpr hr⟩

end Neighborhood
end Langlands.GroupScheme.IdentityJet
