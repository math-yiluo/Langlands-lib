import Langlands.Geometry.Building.QuasiSplitApartmentAssembly
import Langlands.Geometry.Building.QuasiSplitMultipliableOpposite
import Langlands.GroupScheme.Rational.MultipliableRootNoncommutation

/-! # Quasi-split apartments over henselian integer-valued fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (t : S ⟶ T) (jT : T.toGrp ⟶ G) (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

omit [Smooth G.X.hom] in
private theorem rationalExtend_injective' :
    Function.Injective (rationalExtend k K G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y h
  apply (rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k K G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv k K G) h

omit [Smooth G.X.hom] in
/-- **Galois automorphisms are piece symmetries.** A Galois automorphism `τ` of `K/k` acts on
the rational points of `G_K` by `rationalConjugate` and on the root indices of a root datum of
`j_K` by `galoisRootIndexEquiv`; together they form a piece symmetry over `a_K a`. -/
theorem isPieceSymmetry_galois [Mono (j_K).hom.hom.left] {J : Type*}
    {P : RootDatum J (characterLattice T_K) (cocharacterLattice T_K)}
    (hP : IsRootDatumOf (T := T_K) j_K P) (a : characterLattice S) (τ : K ≃ₐ[k] K) :
    IsPieceSymmetry (S := S_K) (T := T_K) j_K P t_K (a_K a)
      (rationalConjugate k K G τ).toMonoidHom
      (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k K jT hP τ) where
  injective w w' h := (rationalConjugate k K G τ).injective h
  index_injective := (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k K jT hP τ).injective
  root_add i₀ i₁ i₂ h := by
    rw [IsRootDatumOf.galoisRootIndexEquiv_root, IsRootDatumOf.galoisRootIndexEquiv_root,
      IsRootDatumOf.galoisRootIndexEquiv_root, h, map_add]
  restrict i₀ n h := by
    rw [IsRootDatumOf.galoisRootIndexEquiv_root,
      ← characterLattice.galoisRepresentation_precompose, h, map_zsmul,
      characterLattice.galoisRepresentation_baseChange]
  mem i₀ w hw := by
    change rationalConjugate k K G τ w ∈ rootGroupPoints (S := T_K) j_K
      (P.root (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k K jT hP τ i₀))
    rw [IsRootDatumOf.galoisRootIndexEquiv_root]
    exact (RelativeRoot.rationalConjugate_mem_subgroup_iff k K jT τ _ w).mpr hw

/-- **V 5 at multipliable roots for the descended family.** Under the hypotheses of
`QuasiSplitMultipliableOppositeStatement`, the torus-then-field restriction of a Galois-fixed
point `x` of a normalizer-stable apartment class of `j_K` satisfies
`ψ_{-a}(g') + ψ_a(g) = 0` whenever `a` and `2a` are relative roots, `g ≠ 1` lies in `U_a(k)`,
`g', g''` lie in `U_{-a}(k)` and `g' g g''` normalizes `i`. -/
theorem torusFieldRestrictedRootFunctionFamily_opposite_of_two_mem
    [FiniteDimensional k K] [IsGalois k K]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [Mono (j_K).hom.hom.left] [Mono (CommGroupScheme.groupHom t_K ≫ j_K).hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hit : CommGroupScheme.groupHom t ≫ jT = i) (hjc : IsClosedSubgroup jT)
    (hj : (torusCentralizer i).IsRepresentedBy jT)
    (hGK : IsConnectedReductive G_K) (hjK : IsMaximalTorus (T := T_K) j_K)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {ω : Kˣ → ℝ} (D : KPApartmentData (S := T_K) j_K ω) (x : D.Apartment)
    (hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val)
    (hfactor : CommGroupScheme.groupHom t_K ≫ j_K = i_K)
    {J : Type u} [Finite J] {P : RootDatum J (characterLattice T_K) (cocharacterLattice T_K)}
    (hP : IsRootDatumOf (T := T_K) j_K P) [P.IsReduced]
    {a : characterLattice S} (ha : a ∈ relativeRoots i) (h2a : 2 • a ∈ relativeRoots i)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) (hg1 : g ≠ 1)
    {g' g'' : rationalPoints G} (hg' : g' ∈ rootGroupPoints i (-a))
    (hg'' : g'' ∈ rootGroupPoints i (-a)) (hN : g' * g * g'' ∈ normalizerPoints i) :
    torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE x.isValuation
        t_K (-a) g' +
      torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE
        x.isValuation t_K a g = 0 := by
  classical
  have hSK : IsSplitTorus (S_K).toGrp := hS.baseChange b
  have : LocallyOfFiniteType (G_K).X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance
  have hjcK : IsClosedSubgroup j_K := hjK.2.1
  have hjKmax : IsMaximalSplitTorus (T := T_K) j_K := hjK.isMaximalSplitTorus hT
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T_K) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice T_K) :=
    Function.Injective.isAddTorsionFree toRat hT.character_toRat_injective
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice S_K) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice S_K) :=
    Function.Injective.isAddTorsionFree toRat hSK.character_toRat_injective
  -- structural facts about the centralizer torus
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsClosedImmersion jT.hom.hom.left := hjc
  have : Mono jT.hom.hom.left := inferInstance
  have hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ jT) := hit ▸ hi
  have hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ jT)).IsRepresentedBy jT :=
    hit ▸ hj
  have ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t) :=
    (hf.of_comp hjc).isLargestSplitSubtorus
  have hnorm : ∀ n : normalizerPoints i, (n : rationalPoints G) ∈ normalizerPoints jT :=
    mem_normalizerPoints_of_torusCentralizer i jT hj
  have hzero : ∀ ψ ∈ relativeRoots (T := T_K) j_K, t_K ≫ ψ ≠ 0 := fun ψ hψ =>
    root_restrict_ne_zero_of_torusCentralizer k K t jT hS hT hcent ⟨ψ, hψ⟩
  have horbit : ∀ (c : characterLattice S),
      ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ ψ ∈ relativeRoots (T := T_K) j_K,
      t_K ≫ χ = (a_K c) → t_K ≫ ψ = (a_K c) →
      ∃ σ : K ≃ₐ[k] K, characterLattice.galoisRepresentation k K T σ χ = ψ := by
    intro c χ hχ ψ hψ hχc hψc
    have hβ : (⟨χ, hχ⟩ : roots (T := T_K) j_K) ∈ rootRestrictionFiber k K jT t c := hχc
    have horb := rootOrbit_eq_restrictionFiber_of_torusCentralizer k K t jT hf hjc hcent hT hP c hβ
    have hmem : (⟨ψ, hψ⟩ : roots (T := T_K) j_K) ∈ MulAction.orbit (K ≃ₐ[k] K)
        (⟨χ, hχ⟩ : roots (T := T_K) j_K) := by
      rw [horb]
      exact hψc
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hmem
    exact ⟨σ, congrArg Subtype.val hσ⟩
  have hEbase : RelativeRoot.HasOppositeFactorPairs i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs i hS).mp
      (rootRankOneFactorization k G hG S i hi)
  -- the relative root over `K`
  have haK : (a_K a) ∈ relativeRoots (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have ha0 : (a_K a) ≠ 0 := haK.1
  have hnsmul : ∀ n m : ℕ, n • (a_K a) = m • (a_K a) → n = m := fun n m h => by
    have h' : ((n : ℤ) • (a_K a)) = ((m : ℤ) • (a_K a)) := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact_mod_cast smul_left_injective ℤ ha0 h'
  -- the restrictions of roots lie on the multipliable line through `a`
  have hline : RestrictsToMultipliableLine t_K P (a_K a) := by
    intro l n hl
    have hK : n • (a_K a) ∈ roots (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) := by
      refine (mem_roots_comp_iff (T := T_K) (T' := S_K) hT hSK t_K j_K _).mpr
        ⟨?_, P.root l, root_mem_relativeRoots (T := T_K) j_K hP l, hl⟩
      rw [← hl]
      exact hzero _ (root_mem_relativeRoots (T := T_K) j_K hP l)
    rw [hfactor, ← map_zsmul] at hK
    have hroot := (mem_roots_baseChange_iff (K := K) G S hS i (n • a)).mp hK
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [natCast_zsmul] at hroot
      have := hEbase.eq_one_or_two_of_nsmul_mem i hS hroot
      omega
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
      rw [neg_smul, natCast_zsmul, ← smul_neg] at hroot
      have := hEbase.eq_one_or_two_of_nsmul_mem i hS hroot
      omega
  -- an obtuse pair over `a`
  obtain ⟨r₁, r₂, -, ⟨hr₁, hr₂, -, hr⟩, -, -⟩ :=
    MultipliableRootNoncommutation.exists_partner k K t jT hS ht hT hjK.2.1 hP
      (fun β => hzero β.val β.property)
      (fun r h => P.nsmul_notMem_range_root (n := 2) (i := r) (by rwa [two_nsmul]))
      (by rw [hit]; exact ha) (by rw [hit]; exact h2a)
  -- Galois automorphisms as piece symmetries
  let s : (K ≃ₐ[k] K) → rationalPoints G_K →* rationalPoints G_K := fun τ =>
    (rationalConjugate k K G τ).toMonoidHom
  let σi : (K ≃ₐ[k] K) → J → J := fun τ =>
    IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k K jT hP τ
  have hσroot : ∀ τ (i₀ : J), P.root (σi τ i₀) =
      characterLattice.galoisRepresentation k K T τ (P.root i₀) := fun τ i₀ =>
    IsRootDatumOf.galoisRootIndexEquiv_root k K jT hP τ i₀
  have hsym : ∀ τ, IsPieceSymmetry (S := S_K) (T := T_K) j_K P t_K (a_K a) (s τ) (σi τ) :=
    fun τ => isPieceSymmetry_galois t jT hP a τ
  have hval : ∀ τ (i₀ : J) (w : rationalPoints G_K),
      x.val (P.root (σi τ i₀)) (s τ w) = x.val (P.root i₀) w := by
    intro τ i₀ w
    rw [hσroot]
    calc x.val (characterLattice.galoisRepresentation k K T τ (P.root i₀)) (s τ w)
        = RootFunctionFamily.galoisAction k K T G τ x.val
            (characterLattice.galoisRepresentation k K T τ (P.root i₀))
            (rationalConjugate k K G τ w) := by rw [hfix τ]; rfl
      _ = x.val (P.root i₀) w :=
          RootFunctionFamily.galoisAction_apply_conjugate k K T G τ x.val (P.root i₀) w
  have htrans : ∀ (i₀ i₁ : J) (n : ℤ), t_K ≫ P.root i₀ = n • (a_K a) →
      t_K ≫ P.root i₁ = n • (a_K a) → ∃ τ, σi τ i₀ = i₁ := by
    intro i₀ i₁ n h₀ h₁
    rw [← map_zsmul] at h₀ h₁
    obtain ⟨τ, hτ⟩ := horbit (n • a) _ (root_mem_relativeRoots (T := T_K) j_K hP i₀) _
      (root_mem_relativeRoots (T := T_K) j_K hP i₁) h₀ h₁
    exact ⟨τ, P.root.injective (by rw [hσroot, hτ])⟩
  -- scalar extensions of the points and of the normalizer
  have hgK : rationalExtend k K G g ∈
      rootGroupPoints (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (a_K a) := by
    rw [hfactor]
    exact rationalExtend_mem_rootGroupPoints (K := K) i a hg
  have hg1K : rationalExtend k K G g ≠ 1 := fun h =>
    hg1 (rationalExtend_injective' (K := K) (by rw [h, map_one]))
  have hg'K : rationalExtend k K G g' ∈
      rootGroupPoints (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (-(a_K a)) := by
    rw [hfactor, ← map_neg]
    exact rationalExtend_mem_rootGroupPoints (K := K) i (-a) hg'
  have hg''K : rationalExtend k K G g'' ∈
      rootGroupPoints (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (-(a_K a)) := by
    rw [hfactor, ← map_neg]
    exact rationalExtend_mem_rootGroupPoints (K := K) i (-a) hg''
  have hNK : rationalExtend k K G g' * rationalExtend k K G g * rationalExtend k K G g'' ∈
      normalizerPoints (T := T_K) j_K := by
    rw [← map_mul, ← map_mul]
    exact (normalizerPointsFieldExtend (K := K) jT ⟨_, hnorm ⟨_, hN⟩⟩).prop
  have hN'K : rationalExtend k K G g' * rationalExtend k K G g * rationalExtend k K G g'' ∈
      normalizerPoints (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) := by
    rw [← map_mul, ← map_mul, hfactor]
    exact (normalizerPointsFieldExtend (K := K) i ⟨_, hN⟩).prop
  have key := torusRestricted_opposite_of_pieceSymmetries (S := S_K) (T := T_K) j_K hT hjcK hP
    hE hline D hGK hjKmax x hSK ha0 hnsmul hr₁ hr₂ hr s σi hsym hval htrans hgK hg1K hg'K hg''K
    hNK hN'K (fun τ => rationalConjugate_rationalExtend k K G τ g)
    (fun τ => rationalConjugate_rationalExtend k K G τ g')
  simp only [torusFieldRestrictedRootFunctionFamily, RootFunctionFamily.fieldRestrict_apply,
    map_neg]
  exact key

end Galois

/-- **V 5 at multipliable roots.** `QuasiSplitMultipliableOppositeStatement` holds. -/
theorem quasiSplitMultipliableOpposite : QuasiSplitMultipliableOppositeStatement.{u} := by
  intro k K _ _ _ _ _ S T G _ _ _ _ _ _ _ t jT i _ _ _ hS hT hG hi hit hjc hj hGK hjK hE ω D x
    hfix hfactor J _ P hP hred a ha h2a g hg hg1 g' hg' g'' hg'' hN
  have := hred
  exact torusFieldRestrictedRootFunctionFamily_opposite_of_two_mem t jT i hS hT hG hi hit hjc hj
    hGK hjK hE D x hfix hfactor hP ha h2a hg hg1 hg' hg'' hN

/-- **Quasi-split apartments over henselian integer-valued fields.** For a henselian discrete
valuation `v` on `k` and a quasi-split connected reductive group with maximal split torus `i`,
there are a normalizer-stable apartment class of `i` for the integer order of `v` and a
centralizer datum with which it is compatible. -/
theorem quasiSplitIntegerApartmentExistence : QuasiSplitIntegerApartmentExistenceStatement.{u} :=
  quasiSplitIntegerApartmentExistence_of_multipliableOpposite quasiSplitMultipliableOpposite

end Langlands.Geometry.Building
