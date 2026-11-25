import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlacesProof
import Langlands.GaloisCohomology.CompactSupport.Internal.ConeReverse

/-!
# The base case of Poitou–Tate duality: the formal hypotheses

For a number field `K` containing the `n`-th roots of unity, `S` a finite set of finite places
containing the places above `n`, `n` odd or `K` totally complex, this file proves the hypotheses of
the abstract base case (`BaseDualityHypotheses`) that do not involve class field theory:

* `G_S` acts trivially on `μ_n(K_S)` (`dualizingModule_ρ_apply_of_mem`);
* the local traces `localTrace` (the local invariants with values in `ℤ/n`) and the global trace
  `finiteTrace` agree on the local terms (`finiteTrace_ptLocalToCompact`);
* `H³(G_S, ℤ/n) = H³(G_S, μ_n) = 0`, `H¹(G_S, ℤ/n)` and `H_c²(G_S, μ_n)` are finite;
* the two pairings `H_c¹(G_S, μ_n) × H²(G_S, ℤ/n)` and `H_c²(G_S, ℤ/n) × H¹(G_S, μ_n)` agree through
  `H_c → H` (`finiteTrace_compactCupRes_swap`), by the graded commutativity of the cup products with
  compact support (`compactCupRes_eq_neg_one_pow_smul_compactCupRightRes`).
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Swap

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] (hD : ∀ d : D, n • d = 0)

theorem neg_one_pow_one_mul_two_smul {R M : Type*} [Ring R] {_ : AddCommGroup M} {_ : Module R M}
    (x : M) : ((-1 : R) ^ (1 * 2)) • x = x := by
  rw [show (1 * 2 : ℕ) = 2 from rfl, neg_one_sq, one_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep D] in
theorem braiding_comp_zmodMulPairingRight :
    (β_ (zmodRep.{u} G n) D).hom ≫ zmodMulPairingRight n D hD = zmodMulPairing n D hD := by
  rw [zmodMulPairingRight, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

attribute [local instance] isSmoothRep_res_zmodRep_base in
/-- The pairings in degrees `(1, 2)` and `(2, 1)` agree through `H_c → H`, when
`∏_v H²(H_v, D) → H_c³(G, D)` is surjective. -/
theorem compactCupRes_zmodMulPairingRight_swap
    (hsurj : Function.Surjective
      (GaloisCohomology.localToCompact φ D (fun v => Rep.res (φ v : H v →* G) D)
        (fun _ => 𝟙 _) 2).hom)
    (yc : compactSupportCohomologyRes φ D 1)
    (xc : compactSupportCohomologyRes φ (zmodRep.{u} G n) 2) :
    compactCupRes φ (zmodMulPairingRight n D hD) (show 1 + 2 = 3 from rfl) yc
        ((GaloisCohomology.compactToGlobal φ _ (fun v => Rep.res (φ v : H v →* G) (zmodRep.{u} G n))
          (fun _ => 𝟙 _) 2).hom xc) =
      compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc
        ((GaloisCohomology.compactToGlobal φ D (fun v => Rep.res (φ v : H v →* G) D) (fun _ => 𝟙 _) 1).hom yc) := by
  refine (compactCupRes_eq_neg_one_pow_smul_compactCupRightRes φ (zmodMulPairingRight n D hD) hsurj
    (show 1 + 2 = 3 from rfl) (show 2 + 1 = 3 from rfl) le_rfl (by norm_num) yc _).trans ?_
  refine (neg_one_pow_one_mul_two_smul _).trans ?_
  refine (congrArg (fun μ => compactCupRightRes φ μ (show 2 + 1 = 3 from rfl)
    ((GaloisCohomology.compactToGlobal φ _ (fun v => Rep.res (φ v : H v →* G) (zmodRep.{u} G n))
      (fun _ => 𝟙 _) 2).hom xc) yc) (braiding_comp_zmodMulPairingRight D hD)).trans ?_
  exact (compactCup_eq_compactCupRight (Aᵥ := fun v => Rep.res (φ v : H v →* G) (zmodRep.{u} G n))
    (Bᵥ := fun v => Rep.res (φ v : H v →* G) D) (Cᵥ := fun v => Rep.res (φ v : H v →* G) D)
    (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) φ (zmodMulPairing n D hD)
    (fun v => pairingRes (φ v : H v →* G) (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v : H v →* G) (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v : H v →* G) (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) (zmodMulPairing n D hD))
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (show 2 + 1 = 3 from rfl) xc yc).symm

end Swap

section GS

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)

omit [NumberField K] [IsSepClosure K Ω] in
/-- When `K` contains the `n`-th roots of unity, `G_S` acts trivially on `μ_n(K_S)`. -/
theorem dualizingModule_ρ_apply_of_mem (hμ : ∀ ζ : Ω, ζ ^ n = 1 → ζ ∈ (algebraMap K Ω).range)
    (g : GaloisGroupUnramifiedOutside K Ω S) (d : dualizingModule K Ω S n) :
    (dualizingModule K Ω S n).ρ g d = d := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  obtain ⟨a, ha⟩ := hμ ((((Additive.toMul d : rootsOfUnity n (maximalUnramifiedOutside K Ω S)) :
      (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) : Ω) (by
    have hx : (((Additive.toMul d : rootsOfUnity n (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) ^ n = 1 := by
      exact (Units.val_pow_eq_pow_val _ n).symm.trans ((congrArg Units.val
        ((mem_rootsOfUnity n _).1 (Additive.toMul d).2)).trans Units.val_one)
    exact (map_pow (maximalUnramifiedOutside K Ω S).val _ n).symm.trans
      ((congrArg (maximalUnramifiedOutside K Ω S).val hx).trans (map_one _)))
  have hd : (((Additive.toMul d : rootsOfUnity n (maximalUnramifiedOutside K Ω S)) :
      (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) =
        algebraMap K (maximalUnramifiedOutside K Ω S) a := Subtype.ext ha.symm
  change ((g (((Additive.toMul d : rootsOfUnity n (maximalUnramifiedOutside K Ω S)) :
    (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) :
      maximalUnramifiedOutside K Ω S) : Ω) = _
  rw [hd, AlgEquiv.commutes]
  exact congrArg Subtype.val hd.symm

variable [NeZero n]

/-- The local trace `H²(K_v, μ_n) → ℤ/n` (the local invariant). -/
def localTrace (v : HeightOneSpectrum (𝓞 K)) :
    cohomology (localModule ι (dualizingModule K Ω S n) v) 2 →+ ZMod n :=
  zmodOfQZ (invariantAt ι S n v) fun x => by
    have h := nsmul_cohomology_eq_zero (localModule ι (dualizingModule K Ω S n) v)
      (fun d => nsmul_dualizingModule S n d) 2 x
    rw [← map_nsmul, h, map_zero]

theorem zmodToQZ_localTrace (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (localModule ι (dualizingModule K Ω S n) v) 2) :
    zmodToQZ n (localTrace ι S n v x) = invariantAt ι S n v x :=
  zmodToQZ_zmodOfQZ _ _ _

variable [Finite S]

/-- `finiteTrace` is the sum of the local traces on the local terms. -/
theorem finiteTrace_ptLocalToCompact (hK : Odd n ∨ IsTotallyComplex K)
    (ξ : ∀ v : S, cohomology (localModule ι (dualizingModule K Ω S n) v.1) 2) :
    letI : Fintype S := Fintype.ofFinite S
    finiteTrace ι S n hK ((ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S n) 2).hom ξ) =
      ∑ v : S, localTrace ι S n v.1 (ξ v) := by
  let _ : Fintype S := Fintype.ofFinite S
  apply zmodToQZ_injective (n := n)
  rw [isFiniteTrace_finiteTrace ι S n hK ξ, map_sum]
  exact Finset.sum_congr rfl fun v _ => (zmodToQZ_localTrace ι S n v.1 (ξ v)).symm

omit [Finite S] in
theorem subsingleton_cohomology_three_zmodRep
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) :
    Subsingleton (cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 3) :=
  cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S (NeZero.ne n) hS hK
    (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) (nsmul_zmodRep_eq_zero _ n) (le_refl 3)

omit [Finite S] in
theorem subsingleton_cohomology_three_dualizingModule
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) :
    Subsingleton (cohomology (dualizingModule K Ω S n) 3) :=
  cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S (NeZero.ne n) hS hK
    (dualizingModule K Ω S n) (nsmul_dualizingModule S n) (le_refl 3)

theorem finite_cohomology_one_zmodRep
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Finite (cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :=
  finite_cohomology_of_nsmul (NeZero.ne n) hS 1 _ (nsmul_zmodRep_eq_zero _ n)

theorem finite_compactSupportCohomologyRes_two
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Finite (compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2) := by
  have : Finite (dualizingModule K Ω S n) := finite_dualizingModule S n hS
  have hloc : ∀ v : S, Finite (cohomology (localModule ι (dualizingModule K Ω S n) v.1) 1) :=
    fun v => by
      let _ := Langlands.Global.FiniteCompletion.valuativeRel v.1
      have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v.1
      exact Local.finite_cohomology (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))
        (localModule ι (dualizingModule K Ω S n) v.1) (Nat.cast_ne_zero.2 Nat.card_pos.ne') 1
  have hglob : Finite (cohomology (dualizingModule K Ω S n) 2) :=
    finite_cohomology_of_nsmul (NeZero.ne n) hS 2 _ (nsmul_dualizingModule S n)
  have hP : Finite (∀ v : S, cohomology (localModule ι (dualizingModule K Ω S n) v.1) 1) :=
    Pi.finite
  -- `H_c²` sits between the local terms and `H²(G_S, μ_n)`.
  exact finite_of_exact_of_finite
    (ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S n) 1).hom.toAddMonoidHom
    (ptCompactToGlobal (localFamily ι S) (dualizingModule K Ω S n) 2).hom.toAddMonoidHom
    fun b hb => (ptExact_compact (localFamily ι S) (dualizingModule K Ω S n) 1 b).1 hb

end GS

end

end Langlands.GaloisCohomology.PoitouTate.Internal
