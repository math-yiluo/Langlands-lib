import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationStatement
import Langlands.Geometry.Building.RootDatumValuationGaloisAction
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # Finite averaging for twisted-fixed reduced translations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open TensorProduct CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.LinearAlgebra.FiniteAveraging

variable {Γ X A : Type*} [Group Γ] [AddCommGroup X] [AddCommGroup A]

/-- **Finite averaging over a lattice.** Let a group act on an additive group `X` through
`W` with finite image, and suppose every `W`-fixed element of `X` lies in the range of `φ`.
A real vector of `ℝ ⊗ X` that every `W σ` fixes modulo a real subspace `R` lies in the real
span of the range of `φ` plus `R`. -/
theorem mem_range_baseChange_sup_of_sub_mem (W : Γ →* (X ≃ₗ[ℤ] X))
    (hW : (Set.range W).Finite) (φ : A →ₗ[ℤ] X)
    (hfix : ∀ x : X, (∀ σ, W σ x = x) → x ∈ LinearMap.range φ)
    (R : Submodule ℝ (ℝ ⊗[ℤ] X)) (v : ℝ ⊗[ℤ] X)
    (hv : ∀ σ, LinearEquiv.baseChange ℤ ℝ X X (W σ) v - v ∈ R) :
    v ∈ LinearMap.range (φ.baseChange ℝ) ⊔ R := by
  classical
  have hfin : Finite W.range := by
    have : Finite (Set.range W) := hW.to_subtype
    rw [← MonoidHom.coe_range] at this
    exact this
  let : Fintype W.range := Fintype.ofFinite _
  -- the integral orbit sum
  let P : X →ₗ[ℤ] X := ∑ g : W.range, ((g : X ≃ₗ[ℤ] X) : X →ₗ[ℤ] X)
  have hP : ∀ x, P x = ∑ g : W.range, (g : X ≃ₗ[ℤ] X) x := by
    intro x
    simp only [P, LinearMap.sum_apply, LinearEquiv.coe_coe]
  have hPfix : ∀ x σ, W σ (P x) = P x := by
    intro x σ
    rw [hP, map_sum]
    let a : W.range := ⟨W σ, σ, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun g => rfl)
  -- the real orbit sum
  let Q : (ℝ ⊗[ℤ] X) →ₗ[ℝ] (ℝ ⊗[ℤ] X) :=
    ∑ g : W.range, (LinearEquiv.baseChange ℤ ℝ X X (g : X ≃ₗ[ℤ] X) :
      (ℝ ⊗[ℤ] X) →ₗ[ℝ] (ℝ ⊗[ℤ] X))
  have hQ : ∀ w, Q w = ∑ g : W.range, LinearEquiv.baseChange ℤ ℝ X X (g : X ≃ₗ[ℤ] X) w := by
    intro w
    simp only [Q, LinearMap.sum_apply, LinearEquiv.coe_coe]
  have hQrange : ∀ w, Q w ∈ LinearMap.range (φ.baseChange ℝ) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul r x =>
      have hx : Q (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] P x := by
        rw [hQ, hP, tmul_sum]
        rfl
      obtain ⟨a, ha⟩ := hfix (P x) (hPfix x)
      rw [hx, ← ha]
      exact ⟨r ⊗ₜ[ℤ] a, rfl⟩
    | add w z hw hz => rw [map_add]; exact Submodule.add_mem _ hw hz
  have hQsub : Q v - (Fintype.card W.range : ℝ) • v ∈ R := by
    have : Q v - (Fintype.card W.range : ℝ) • v =
        ∑ g : W.range, (LinearEquiv.baseChange ℤ ℝ X X (g : X ≃ₗ[ℤ] X) v - v) := by
      rw [Finset.sum_sub_distrib, hQ, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [this]
    refine Submodule.sum_mem _ fun g _ => ?_
    obtain ⟨σ, hσ⟩ := g.2
    rw [← hσ]
    exact hv σ
  have hcard : (Fintype.card W.range : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Submodule.mem_sup]
  refine ⟨(Fintype.card W.range : ℝ)⁻¹ • Q v, Submodule.smul_mem _ _ (hQrange v),
    -((Fintype.card W.range : ℝ)⁻¹ • (Q v - (Fintype.card W.range : ℝ) • v)),
    R.neg_mem (R.smul_mem _ hQsub), ?_⟩
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  abel

/-- The quotient form of `mem_range_baseChange_sup_of_sub_mem`. -/
theorem mkQ_mem_map_range_baseChange (W : Γ →* (X ≃ₗ[ℤ] X))
    (hW : (Set.range W).Finite) (φ : A →ₗ[ℤ] X)
    (hfix : ∀ x : X, (∀ σ, W σ x = x) → x ∈ LinearMap.range φ)
    (R : Submodule ℝ (ℝ ⊗[ℤ] X)) (v : ℝ ⊗[ℤ] X)
    (hv : ∀ σ, LinearEquiv.baseChange ℤ ℝ X X (W σ) v - v ∈ R) :
    R.mkQ v ∈ (LinearMap.range (φ.baseChange ℝ)).map R.mkQ := by
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    Submodule.mem_sup.1 (mem_range_baseChange_sup_of_sub_mem W hW φ hfix R v hv)
  refine ⟨y, hy, ?_⟩
  rw [map_add, Submodule.mkQ_apply R z, (Submodule.Quotient.mk_eq_zero R).2 hz, add_zero]

end Langlands.LinearAlgebra.FiniteAveraging

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.TwistedFixedTranslationAveraging


variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (iT : T.toGrp ⟶ G)

local notation "T_K" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "i_K" =>
  CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) iT

variable [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left]

/-- The integral twisted coefficient map `λ ↦ n_σ · σ(λ)` on the cocharacter lattice of
`T_K`: the Galois transport of `λ` followed by the torus automorphism through which `n_σ`
normalizes `T_K`. -/
def twistedLatticeAut (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (σ : K ≃ₐ[k] K) : cocharacterLattice T_K ≃ₗ[ℤ] cocharacterLattice T_K :=
  cocharacterAut (normalizingAut (T := T_K) i_K (n σ)) *
    cocharacterLattice.galoisEquiv k K T σ

omit [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left] in
theorem twistedLatticeAut_apply (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (σ : K ≃ₐ[k] K) (ν : cocharacterLattice T_K) :
    twistedLatticeAut iT n σ ν =
      cocharacterLattice.galoisRepresentation k K T σ ν ≫
        (normalizingAut (T := T_K) i_K (n σ)).hom :=
  rfl

/-- The real twisted coefficient map `v ↦ n_σ · σ(v)` on `V(T_K)` is the real scalar
extension of `twistedLatticeAut`. -/
theorem normalizerAction_galoisCocharacterAction_eq
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K) (σ : K ≃ₐ[k] K) (x : V T_K) :
    normalizerAction (T := T_K) i_K (n σ) (galoisCocharacterAction k K T σ x) =
      LinearEquiv.baseChange ℤ ℝ _ _ (twistedLatticeAut iT n σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r ν =>
    rw [galoisCocharacterAction_tmul, normalizerAction_tmul, LinearEquiv.baseChange_tmul]
    exact congrArg (fun z => r ⊗ₜ[ℤ] z) (twistedLatticeAut_apply iT n σ ν).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Galois transport of cocharacters intertwines the automorphism through which a normalizer
point acts with the automorphism of its Galois conjugate. -/
theorem galoisRepresentation_comp_normalizingAut (σ : K ≃ₐ[k] K)
    (m : normalizerPoints (T := T_K) i_K) (ν : cocharacterLattice T_K) :
    cocharacterLattice.galoisRepresentation k K T σ
        (ν ≫ (normalizingAut (T := T_K) i_K m).hom) =
      cocharacterLattice.galoisRepresentation k K T σ ν ≫
        (normalizingAut (T := T_K) i_K (normalizerGaloisAction k K iT σ m)).hom := by
  have hn : normalizingAut (T := T_K) i_K (normalizerGaloisAction k K iT σ m) =
      torusAutGaloisTransport k K σ (normalizingAut (T := T_K) i_K m) :=
    (isNormalizingPoint_normalizingAut (T := T_K) i_K _).unique (T := T_K) i_K
      ((isNormalizingPoint_normalizingAut (T := T_K) i_K m).rationalConjugate k K iT σ)
  rw [hn]
  exact (cocharacterLattice.transport_descentPostcomp (algebraBaseMap k K)
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T
    (normalizingAut (T := T_K) i_K m) ν).symm

omit [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left] in
/-- The cocycle `n_σ = h⁻¹ σ(h)` satisfies `n_{στ} = n_σ · σ(n_τ)`. -/
theorem cocycle_of_eq_inv_mul_conjugate (h : rationalPoints (baseChanged k K G))
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hn : ∀ σ, (n σ : rationalPoints (baseChanged k K G)) =
      h⁻¹ * rationalConjugate k K G σ h) (σ τ : K ≃ₐ[k] K) :
    n (σ * τ) = n σ * normalizerGaloisAction k K iT σ (n τ) := by
  apply Subtype.ext
  change (n (σ * τ) : rationalPoints (baseChanged k K G)) =
    (n σ : rationalPoints (baseChanged k K G)) *
      (normalizerGaloisAction k K iT σ (n τ)).val
  rw [normalizerGaloisAction_coe, hn, hn, hn, map_mul, map_inv, rationalConjugate_mul]
  group

/-- For a cocycle `n`, the integral twisted coefficient maps compose multiplicatively. -/
theorem twistedLatticeAut_mul (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hcoc : ∀ σ τ, n (σ * τ) = n σ * normalizerGaloisAction k K iT σ (n τ))
    (σ τ : K ≃ₐ[k] K) :
    twistedLatticeAut iT n (σ * τ) = twistedLatticeAut iT n σ * twistedLatticeAut iT n τ := by
  apply LinearEquiv.ext
  intro ν
  have hN : normalizingAut (T := T_K) i_K (n σ * normalizerGaloisAction k K iT σ (n τ)) =
      normalizingAut (T := T_K) i_K (normalizerGaloisAction k K iT σ (n τ)) ≪≫
        normalizingAut (T := T_K) i_K (n σ) :=
    (isNormalizingPoint_normalizingAut (T := T_K) i_K _).unique (T := T_K) i_K
      ((isNormalizingPoint_normalizingAut (T := T_K) i_K (n σ)).mul
        (isNormalizingPoint_normalizingAut (T := T_K) i_K _))
  rw [LinearEquiv.mul_apply, twistedLatticeAut_apply, twistedLatticeAut_apply,
    twistedLatticeAut_apply, galoisRepresentation_comp_normalizingAut, hcoc, hN, map_mul,
    Module.End.mul_apply, Iso.trans_hom, Category.assoc]

/-- **Assembly.** Let the integral twisted coefficient maps be multiplicative with finite
image, and let every cocharacter of `T_K` fixed by all of them come from `S_K` along `f`.
Then every reduced translation fixed by all twisted coefficient maps `v ↦ n_σ · σ(v)` lies
in the image of `V(S_K)`. -/
theorem mem_splitTranslationDirections_of_twistedFixed [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hmul : ∀ σ τ, twistedLatticeAut iT n (σ * τ) =
      twistedLatticeAut iT n σ * twistedLatticeAut iT n τ)
    (hfin : (Set.range (twistedLatticeAut iT n)).Finite)
    (hfix : ∀ lam : cocharacterLattice T_K, (∀ σ, twistedLatticeAut iT n σ lam = lam) →
      ∃ ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S),
        ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k K)).map f = lam)
    (v : TranslationSpace (S := T_K) i_K)
    (hv : ∀ σ, translationAction (S := T_K) i_K (n σ)
      (galoisTranslationAction k K iT σ v) = v) :
    v ∈ splitTranslationDirections k K iT f := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  let W : (K ≃ₐ[k] K) →* (cocharacterLattice T_K ≃ₗ[ℤ] cocharacterLattice T_K) :=
    MonoidHom.mk' (twistedLatticeAut iT n) hmul
  refine LinearAlgebra.FiniteAveraging.mkQ_mem_map_range_baseChange W hfin
    (cocharacterMapInt ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)) ?_ _ w ?_
  · intro lam hlam
    obtain ⟨ν, hν⟩ := hfix lam hlam
    exact ⟨ν, hν⟩
  · intro σ
    have h := hv σ
    change Submodule.Quotient.mk (normalizerAction (T := T_K) i_K (n σ)
      (galoisCocharacterAction k K T σ w)) = Submodule.Quotient.mk w at h
    rw [normalizerAction_galoisCocharacterAction_eq] at h
    exact (Submodule.Quotient.eq _).1 h

/-! ### Finiteness of the twisted coefficient maps -/

omit [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left] in
/-- For a split torus with finite Weyl image, the normalizer acts on cocharacters through
finitely many automorphisms. -/
theorem finite_range_cocharacterAut_normalizingAut {R : Type u} [Field R]
    {T' : CommGroupScheme (Spec (CommRingCat.of R))} {G' : GroupScheme (Spec (CommRingCat.of R))}
    (j : T'.toGrp ⟶ G') [Mono j.hom.hom.left] (hT : IsSplitTorus T'.toGrp)
    [Finite (weylImage j)] :
    (Set.range fun m : normalizerPoints j => cocharacterAut (normalizingAut j m)).Finite := by
  have hW : (Set.range (weylAction j)).Finite := by
    have : Finite (weylAction j).range := ‹Finite (weylImage j)›
    rw [← MonoidHom.coe_range]
    exact Set.toFinite _
  have hA : (Set.range (normalizingAut j)).Finite := by
    refine Set.Finite.of_finite_image (f := characterAut) ?_ ?_
    · rw [← Set.range_comp]
      exact hW
    · intro σ _ τ _ h
      have hinv : σ.inv = τ.inv := hT.hom_ext_characters fun χ => by
        have := LinearEquiv.congr_fun h χ
        simpa only [characterAut_apply] using this
      exact Iso.ext ((Iso.inv_eq_inv σ τ).1 hinv)
  have := hA.image cocharacterAut
  rw [← Set.range_comp] at this
  exact this

omit [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left] in
/-- For a Galois extension `K/k` over which `T` splits, the Galois group acts on the
cocharacters of `T_K` through finitely many automorphisms. -/
theorem finite_range_galoisEquiv [IsGalois k K] (hT : IsSplitTorus (T_K).toGrp) :
    (Set.range fun σ : K ≃ₐ[k] K => cocharacterLattice.galoisEquiv k K T σ).Finite := by
  obtain ⟨L, hL, hfix⟩ := torusLatticeGaloisContinuity k K T hT
  have : L.fixingSubgroup.FiniteIndex := by
    constructor
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hconst : ∀ (σ : K ≃ₐ[k] K) (τ : L.fixingSubgroup),
      cocharacterLattice.galoisEquiv k K T (σ * τ) = cocharacterLattice.galoisEquiv k K T σ := by
    intro σ τ
    have hτ : cocharacterLattice.galoisRepresentation k K T (τ : K ≃ₐ[k] K) = 1 :=
      (hfix τ fun x hx => (mem_fixingSubgroup_iff _).1 τ.2 x hx).2
    apply LinearEquiv.ext
    intro ν
    change cocharacterLattice.galoisRepresentation k K T (σ * τ) ν =
      cocharacterLattice.galoisRepresentation k K T σ ν
    rw [map_mul, hτ, mul_one]
  refine (Set.finite_range fun q : (K ≃ₐ[k] K) ⧸ L.fixingSubgroup =>
    cocharacterLattice.galoisEquiv k K T q.out).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup σ
  exact ⟨σ, by simp only [hτ, hconst]⟩

/-- **Finite range (D).** The integral twisted coefficient maps take finitely many values. -/
theorem finite_range_twistedLatticeAut [IsGalois k K] (hT : IsSplitTorus (T_K).toGrp)
    [Finite (weylImage (T := T_K) i_K)]
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K) :
    (Set.range (twistedLatticeAut iT n)).Finite := by
  refine ((finite_range_cocharacterAut_normalizingAut (T' := T_K) i_K hT).image2 (· * ·)
    (finite_range_galoisEquiv hT)).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact Set.mem_image2_of_mem ⟨n σ, rfl⟩ ⟨σ, rfl⟩

/-- **Twisted-fixed reduced translations are split directions.** Let `K/k` be Galois, `T_K`
a maximal split torus of `G_K`, and `n_σ = h⁻¹ σ(h)` normalizer points of `T_K`. Suppose every
cocharacter `λ` of `T_K` with `n_σ · σ(λ) = λ` for all `σ` comes from `S_K` along `f`. Then
every reduced translation fixed by all twisted coefficient maps `v ↦ n_σ · σ(v)` lies in the
image of `V(S_K)`. -/
theorem mem_splitTranslationDirections_of_inv_mul_conjugate [IsGalois k K]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
    (hiT : IsMaximalSplitTorus (T := T_K) i_K)
    (h : rationalPoints (baseChanged k K G))
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hn : ∀ σ, (n σ : rationalPoints (baseChanged k K G)) =
      h⁻¹ * rationalConjugate k K G σ h)
    (hfix : ∀ lam : cocharacterLattice T_K,
      (∀ σ, cocharacterLattice.galoisRepresentation k K T σ lam ≫
        (normalizingAut (T := T_K) i_K (n σ)).hom = lam) →
      ∃ ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S),
        ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k K)).map f = lam)
    (v : TranslationSpace (S := T_K) i_K)
    (hv : ∀ σ, translationAction (S := T_K) i_K (n σ)
      (galoisTranslationAction k K iT σ v) = v) :
    v ∈ splitTranslationDirections k K iT f := by
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have : IsClosedImmersion (i_K).hom.hom.left := hiT.isSplitSubtorus.2
  have : Finite (weylImage (T := T_K) i_K) :=
    splitTorusWeylImageFinite K _ T_K hiT.isSplitSubtorus.1 i_K hiT.isSplitSubtorus.2
  exact mem_splitTranslationDirections_of_twistedFixed iT f n
    (twistedLatticeAut_mul iT n (cocycle_of_eq_inv_mul_conjugate iT h n hn))
    (finite_range_twistedLatticeAut iT hiT.isSplitSubtorus.1 n) (fun lam hlam => hfix lam hlam)
    v hv

end Langlands.Geometry.Building.TwistedFixedTranslationAveraging
