import Langlands.GroupScheme.Rational.GaloisCoordinateDensity
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Rational.FiniteFieldBorelConjugacy
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangGroupScheme
import Langlands.GroupScheme.Dynamic.DescentTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Absolute.BorelDynamicConjugacy
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Descent of a Galois-permuted triple of dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Conjugate

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  (M : GroupScheme (Spec (CommRingCat.of F)))

/-- On rational points of the base change, the Galois conjugation is precomposition of the
corresponding `K`-point with the spectrum map of the automorphism. -/
theorem rationalConjugate_eq_ringTestMap (σ : K ≃ₐ[F] K)
    (x : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) :
    GaloisPointComparison.rationalConjugate F K M σ x =
      (baseChangeBasePointsEquiv (algebraBaseMap F K) M).symm
        (ringTestMap F σ.toAlgHom ≫ baseChangeBasePointsEquiv (algebraBaseMap F K) M x) := by
  apply (baseChangeBasePointsEquiv (algebraBaseMap F K) M).injective
  rw [MulEquiv.apply_symm_apply]
  change GaloisPointComparison.baseChangeCoeffEquiv F K M
    (GaloisPointComparison.rationalConjugate F K M σ x) = _
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate,
    FiniteFieldTorsorPoint.ringTestMap_eq_algSpec_map]
  rfl

end Conjugate

section Helpers

/-- Canonical Galois transport preserves binary intersections of subgroup functors. -/
theorem galoisTransport_inf {F K : Type u} [Field F] [Field K] [Algebra F K]
    (M : GroupScheme (Spec (CommRingCat.of F))) (σ : K ≃ₐ[F] K)
    (A B : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) :
    SubgroupFunctor.galoisTransport F K M σ (A ⊓ B) =
      SubgroupFunctor.galoisTransport F K M σ A ⊓ SubgroupFunctor.galoisTransport F K M σ B := by
  ext U x
  change x ∈ (SubgroupFunctor.descentTransport _ _ _ _ (A ⊓ B)).carrier U ↔
    x ∈ (SubgroupFunctor.descentTransport _ _ _ _ A ⊓
      SubgroupFunctor.descentTransport _ _ _ _ B).carrier U
  rfl

variable {S : Scheme.{u}} {G H₀ H₁ H₂ J : GroupScheme S}

/-- The range of a monomorphism followed by an isomorphism is the preimage of the range. -/
theorem range_comp_iso_eq_comap (i : H₀ ⟶ G) [Mono i.hom.hom] (e : G ≅ G) :
    SubgroupFunctor.range (i ≫ e.hom) = (SubgroupFunctor.range i).comap e.inv :=
  (SubgroupFunctor.IsRepresentedBy.comp_iso (F := SubgroupFunctor.range i)
    ⟨inferInstance, rfl⟩ e).2

/-- Applying one ambient isomorphism to three subgroups and to a representative of their
intersection preserves the intersection identity. -/
theorem range_inf_inf_comp_iso (i₀ : H₀ ⟶ G) (i₁ : H₁ ⟶ G) (i₂ : H₂ ⟶ G) (j : J ⟶ G)
    [Mono i₀.hom.hom] [Mono i₁.hom.hom] [Mono i₂.hom.hom] [Mono j.hom.hom] (e : G ≅ G)
    (h : SubgroupFunctor.range i₀ ⊓ SubgroupFunctor.range i₁ ⊓ SubgroupFunctor.range i₂ =
      SubgroupFunctor.range j) :
    SubgroupFunctor.range (i₀ ≫ e.hom) ⊓ SubgroupFunctor.range (i₁ ≫ e.hom) ⊓
        SubgroupFunctor.range (i₂ ≫ e.hom) = SubgroupFunctor.range (j ≫ e.hom) := by
  rw [range_comp_iso_eq_comap, range_comp_iso_eq_comap, range_comp_iso_eq_comap,
    range_comp_iso_eq_comap, ← h]
  ext U x
  simp only [SubgroupFunctor.mem_comap]
  rfl

/-- Conjugating a subgroup by `g` or by `h` gives the same range when `h⁻¹ g` lies in it. -/
theorem range_comp_innerIso_eq_of_inv_mul_mem (i : H₀ ⟶ G)
    (g h : Over.mk (𝟙 S) ⟶ G.X) (p : Over.mk (𝟙 S) ⟶ H₀.X) (hp : h⁻¹ * g = p ≫ i.hom.hom) :
    SubgroupFunctor.range (i ≫ (G.innerIso g).hom) =
      SubgroupFunctor.range (i ≫ (G.innerIso h).hom) :=
  range_eq_of_innerIso_transport (i ≫ (G.innerIso g).hom) i i g 1 h (h⁻¹ * g) p hp rfl
    (by rw [innerIso_one_hom, Category.comp_id]) (by group)

end Helpers

section Descent

/-- The range of a centralizer representative followed by an isomorphism is the centralizer of
the transported cocharacter. -/
theorem range_comp_iso_eq_centralizer {S : Scheme.{u}} {G H : GroupScheme S}
    {i : H ⟶ G} [Mono i.hom.hom]
    {χ : (Gm S).toGrp ⟶ G} (h : SubgroupFunctor.range i = Dynamic.centralizer χ) (e : G ≅ G) :
    SubgroupFunctor.range (i ≫ e.hom) = Dynamic.centralizer (χ ≫ e.hom) := by
  have hrep : (Dynamic.centralizer χ).IsRepresentedBy i := ⟨inferInstance, h⟩
  rw [(hrep.comp_iso e).2, Dynamic.centralizer_eq_comap_of_iso (χ ≫ e.hom) e.symm, Iso.symm_hom,
    Dynamic.comp_hom_comp_inv]

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

set_option maxHeartbeats 1600000 in
/-- Let `K/F` be a Galois extension with cyclic Galois group of order three generated by `σ`,
and `M` a connected reductive `F`-group with a split torus `s : S ⟶ M_K`. Let `ν₀, ν₁, ν₂` be
cocharacters of `S` with zero sum, each root negative at no more than one of them and vanishing
at all three exactly when it vanishes at `ν₀ - ν₁`. Suppose the Galois transports of the
dynamic parabolic of `ν₀` by `σ` and `σ²` are rational conjugates of those of `ν₁` and `ν₂`.
Then a rational conjugate of the dynamic centralizer of `ν₀ - ν₁` descends to a connected
reductive closed subgroup of `M`. -/
theorem exists_tripleParabolic_descent [Infinite F] [FiniteDimensional F K] [IsGalois F K]
    (σ : K ≃ₐ[F] K) (hgen : ∀ τ : K ≃ₐ[F] K, ∃ n : ℕ, τ = σ ^ n) (hσ3 : σ ^ 3 = 1)
    (h01 : (1 : K ≃ₐ[F] K) ≠ σ) (h02 : (1 : K ≃ₐ[F] K) ≠ σ ^ 2) (h12 : σ ≠ σ ^ 2)
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of K))} (hS : IsSplitTorus S.toGrp)
    (s : S.toGrp ⟶ ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) (ν : Fin 3 → cocharacterLattice S) (hsum : ν 0 + ν 1 + ν 2 = 0)
    (hneg : ∀ α ∈ relativeRoots s, (∀ i, latticePairing S α (ν i) = 0) ∨
      ∃! i, latticePairing S α (ν i) < 0)
    (hzero : ∀ α ∈ relativeRoots s, latticePairing S α (ν 0 - ν 1) = 0 →
      ∀ i, latticePairing S α (ν i) = 0)
    (m₁ m₂ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M))
    (htype₁ : SubgroupFunctor.galoisTransport F K M σ
        (Dynamic.parabolic (CommGroupScheme.groupHom (ν 0) ≫ s)) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ν 1) ≫ s ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m₁).hom))
    (htype₂ : SubgroupFunctor.galoisTransport F K M (σ ^ 2)
        (Dynamic.parabolic (CommGroupScheme.groupHom (ν 0) ≫ s)) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ν 2) ≫ s ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m₂).hom)) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (j : C ⟶ M) (h : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)),
      IsClosedSubgroup j ∧ IsConnectedReductive C ∧
        SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F K)).map j) =
          Dynamic.centralizer (CommGroupScheme.groupHom (ν 0 - ν 1) ≫ s ≫
            (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) := by
  classical
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have hMK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap F K)).obj M) := connectedReductiveFieldExtensionStatement F K M hM
  have : Smooth ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom := hMK.smooth
  have : ConnectedSpace ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.left := hMK.connectedSpace
  have : IsAffine ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom
  let χ (i : Fin 3) := CommGroupScheme.groupHom (ν i) ≫ s
  let χ₀ := CommGroupScheme.groupHom (ν 0 - ν 1) ≫ s
  let i₀ := Dynamic.Affine.parabolicHom (χ 0)
  let i₁ := Dynamic.Affine.parabolicHom (χ 1)
  let i₂ := Dynamic.Affine.parabolicHom (χ 2)
  let jZ := Dynamic.Affine.centralizerHom χ₀
  have hi₀ := Dynamic.Affine.isRepresentedBy_parabolicHom (χ 0)
  have hi₁ := Dynamic.Affine.isRepresentedBy_parabolicHom (χ 1)
  have hi₂ := Dynamic.Affine.isRepresentedBy_parabolicHom (χ 2)
  have hjZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ₀
  have hjZc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ₀
  have : Mono i₀.hom.hom := hi₀.1
  have : Mono i₁.hom.hom := hi₁.1
  have : Mono i₂.hom.hom := hi₂.1
  have : Mono jZ.hom.hom := hjZ.1
  -- The open slice and a Galois point in it.
  obtain ⟨U, hU1, hlift⟩ := exists_open_tripleParabolic_rationalLift hS s ν hsum hneg hzero
  let e := baseChangeBasePointsEquiv (algebraBaseMap F K) M
  have hdense := galoisTripleCoordinateDensity F K M hM 1 σ (σ ^ 2) h01 h02 h12
    (e 1) (e m₁) (e m₂)
  obtain ⟨x, hxU, hxd⟩ := hdense.inter_open_nonempty U U.isOpen ⟨_, hU1⟩
  obtain ⟨f, a, ha⟩ := Set.mem_iUnion.mp hxd
  let g₀ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M) := e.symm f
  let g₁ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M) := GaloisPointComparison.rationalConjugate F K M σ g₀ * m₁
  let g₂ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M) :=
    GaloisPointComparison.rationalConjugate F K M (σ ^ 2) g₀ * m₂
  have hconj (τ : K ≃ₐ[F] K) (m : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) :
      e.symm (@HMul.hMul (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) instHMul
        (ringTestMap F τ.toAlgHom ≫ f) (e m)) =
        GaloisPointComparison.rationalConjugate F K M τ g₀ * m := by
    rw [rationalConjugate_eq_ringTestMap]
    have hf : e g₀ = f := e.apply_symm_apply f
    refine (map_mul e.symm (ringTestMap F τ.toAlgHom ≫ f) (e m)).trans ?_
    congr 1
    · exact congrArg (fun y => e.symm (ringTestMap F τ.toAlgHom ≫ y)) hf.symm
    · exact e.symm_apply_apply m
  have hpoint : (lift (e.symm (@HMul.hMul (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) instHMul
        (ringTestMap F (1 : K ≃ₐ[F] K).toAlgHom ≫ f) (e 1)))
      (lift (e.symm (@HMul.hMul (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) instHMul
        (ringTestMap F σ.toAlgHom ≫ f) (e m₁)))
        (e.symm (@HMul.hMul (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) (ringTest F K ⟶ M.X) instHMul
        (ringTestMap F (σ ^ 2).toAlgHom ≫ f) (e m₂)))) :
      Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ groupCube ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) =
      lift (![g₀, g₁, g₂] 0) (lift (![g₀, g₁, g₂] 1) (![g₀, g₁, g₂] 2)) := by
    rw [hconj, hconj, hconj, GaloisPointComparison.rationalConjugate_one, mul_one]
    rfl
  have hmemU : (lift (![g₀, g₁, g₂] 0) (lift (![g₀, g₁, g₂] 1) (![g₀, g₁, g₂] 2)) :
      Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ groupCube ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)).left
        (IsLocalRing.closedPoint K) ∈ U := by
    rw [← hpoint]
    have hac : a = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [← hac, ha]
    exact hxU
  obtain ⟨h, hh⟩ := hlift ![g₀, g₁, g₂] hmemU
  have hmem (k : Fin 3) (P : GroupScheme (Spec (CommRingCat.of K)))
      (ik : P ⟶ ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) (hk : SubgroupFunctor.range ik = Dynamic.parabolic (χ k)) :
      ∃ p, h⁻¹ * ![g₀, g₁, g₂] k = p ≫ ik.hom.hom := by
    have := hh k
    rw [← hk] at this
    exact SubgroupFunctor.mem_range.1 this |>.imp fun p hp => hp.symm
  obtain ⟨p₀, hp₀⟩ := hmem 0 _ i₀ hi₀.2
  obtain ⟨p₁, hp₁⟩ := hmem 1 _ i₁ hi₁.2
  obtain ⟨p₂, hp₂⟩ := hmem 2 _ i₂ hi₂.2
  -- The three conjugated parabolics.
  set B := SubgroupFunctor.range (i₀ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso g₀).hom) with hBdef
  have hB : B = SubgroupFunctor.range (i₀ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) :=
    range_comp_innerIso_eq_of_inv_mul_mem i₀ g₀ h p₀ hp₀
  have htrans (τ : K ≃ₐ[F] K) {P : GroupScheme (Spec (CommRingCat.of K))}
      (X : P ⟶ ((GroupScheme.baseChange (algebraBaseMap F K)).obj M)) :
      SubgroupFunctor.galoisTransport F K M τ (SubgroupFunctor.range X) =
        SubgroupFunctor.range (radicalGaloisHom X τ) := by
    change SubgroupFunctor.descentTransport _ _ _ _ _ = _
    rw [SubgroupFunctor.descentTransport_range]
    rfl
  have hBσ : SubgroupFunctor.galoisTransport F K M σ B =
      SubgroupFunctor.range (i₁ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) := by
    rw [hBdef, htrans, radicalGaloisHom_comp_innerIso]
    refine range_eq_of_innerIso_transport _ (radicalGaloisHom i₀ σ) i₁ _ m₁ h (h⁻¹ * g₁) p₁
      hp₁ rfl ?_ (mul_inv_cancel_left h g₁).symm
    rw [← htrans, hi₀.2, htype₁, range_comp_iso_eq_parabolic hi₁.2]
    simp only [χ, Category.assoc]
  have hBσ2 : SubgroupFunctor.galoisTransport F K M (σ ^ 2) B =
      SubgroupFunctor.range (i₂ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) := by
    rw [hBdef, htrans, radicalGaloisHom_comp_innerIso]
    refine range_eq_of_innerIso_transport _ (radicalGaloisHom i₀ (σ ^ 2)) i₂ _ m₂ h
      (h⁻¹ * g₂) p₂ hp₂ rfl ?_ (mul_inv_cancel_left h g₂).symm
    rw [← htrans, hi₀.2, htype₂, range_comp_iso_eq_parabolic hi₂.2]
    simp only [χ, Category.assoc]
  -- The triple intersection.
  have hint := parabolic_inf_parabolic_inf_parabolic_eq_centralizer hS s (ν 0) (ν 1) (ν 2) hsum
    (fun α hα h' => ⟨hzero α hα h' 0, hzero α hα h' 1, hzero α hα h' 2⟩)
  have hQ : SubgroupFunctor.range (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) =
      B ⊓ SubgroupFunctor.galoisTransport F K M σ B ⊓
        SubgroupFunctor.galoisTransport F K M (σ ^ 2) B := by
    rw [hBσ, hBσ2, hB]
    refine (range_inf_inf_comp_iso i₀ i₁ i₂ jZ _ ?_).symm
    rw [hi₀.2, hi₁.2, hi₂.2, hjZ.2]
    exact hint
  -- Galois invariance.
  have hinvσ : SubgroupFunctor.galoisTransport F K M σ
      (SubgroupFunctor.range (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom)) =
      SubgroupFunctor.range (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) := by
    have h3 : SubgroupFunctor.galoisTransport F K M σ
        (SubgroupFunctor.galoisTransport F K M (σ ^ 2) B) = B := by
      have e3 : SubgroupFunctor.galoisTransport F K M (σ * σ ^ 2) B = B := by
        rw [← pow_succ', hσ3, map_one]
        rfl
      rw [map_mul] at e3
      exact e3
    have h2 : SubgroupFunctor.galoisTransport F K M σ
        (SubgroupFunctor.galoisTransport F K M σ B) =
          SubgroupFunctor.galoisTransport F K M (σ ^ 2) B := by
      have e2 : SubgroupFunctor.galoisTransport F K M (σ * σ) B =
          SubgroupFunctor.galoisTransport F K M (σ ^ 2) B := by
        rw [← sq]
      rw [map_mul] at e2
      exact e2
    rw [hQ, galoisTransport_inf, galoisTransport_inf, h2, h3]
    ext T x
    simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf]
    tauto
  have hinv (τ : K ≃ₐ[F] K) : SubgroupFunctor.range
      (radicalGaloisHom (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) τ) =
      SubgroupFunctor.range (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) := by
    obtain ⟨n, rfl⟩ := hgen τ
    rw [← htrans]
    exact SubgroupFunctor.galoisTransport_pow_eq_self F K M σ _ hinvσ n
  -- Descent.
  have hcl : IsClosedSubgroup (jZ ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso h).hom) :=
    hjZc.comp_iso _
  obtain ⟨C, j, r, _, hj, hjr⟩ :=
    Descent.GaloisInvariantClosedSubgroup.exists_descent hcl hinv
  have hred : IsConnectedReductive (Dynamic.Affine.centralizerScheme χ₀) :=
    dynamicCentralizerReductive K ((GroupScheme.baseChange (algebraBaseMap F K)).obj M) hMK χ₀ _ jZ hjZc hjZ
  refine ⟨C, j, h, hj, IsConnectedReductive.of_fieldExtension
    (IsConnectedReductive.of_iso r hred), ?_⟩
  rw [hjr, SubgroupFunctor.range_iso_comp]
  exact range_comp_iso_eq_centralizer hjZ.2 _

end Descent

end Langlands.GroupScheme
