import Langlands.GaloisCohomology.Global.RealPlaces.VanishingCriterion

/-!
# Dévissage of the vanishing of `Ĥ_cʳ(G_S, M)` to the modules `Coind_W(ℤ/2)`

**Abstract part.** Let `G` be a compact group with families `(φ_v)` and `(ψ_w)` (the `F_w` finite) and
`n` a degree. If `Ĥ_cⁿ(G, Coind_W^G(ℤ/2)) = 0` for every open subgroup `W` of `G`, then
`Ĥ_cⁿ(G, M) = 0` for every finite smooth `G`-module `M` killed by `2`
(`subsingleton_tateCompactCohomologyRes_of_two_nsmul`). Proof: let `W` be the preimage of a
`2`-Sylow subgroup of the finite quotient of `G` acting faithfully on `M`. Its index is odd, so `M`
is a retract of `Coind_W^G Res_W M` (`coindUnit ≫ coindTrace = [G : W]`, which is `1` on `M`). The group
`W` acts on `Res_W M` through a `2`-group, so a nonzero vector is fixed
(`exists_ne_zero_forall_ρ_eq`, by the congruence `#M ≡ #M^W (mod 2)` for `p`-groups); it spans a
copy of `ℤ/2` and, coinduction being exact, induction on `#M` reduces `Coind_W^G Res_W M` to
`Coind_W^G(ℤ/2)` (`subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul`).

**For `G_S`.** Let `r ≥ 4`.

* `subsingleton_compactCohomology_of_odd`: for a prime `ℓ ≠ 2` with the places above `ℓ` in `S` and a
  finite smooth `M` killed by `ℓ`, `Ĥ_cʳ(G_S, M) = 0`: `Hʳ(G_S, M) = 0` for `r ≥ 3`
  (`cd_ℓ(G_S) ≤ 2`), and the cohomology of the real places vanishes in positive degree.
* `subsingleton_compactCohomology_of_coind`: if `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup
  `W` of `G_S` whenever `S` contains the places above `2`, then `Ĥ_cʳ(G_S, M) = 0` for every finite
  smooth `M` killed by an `n ≠ 0` with the places above `n` in `S`: induction on `n`, through the
  extension `0 → M[ℓ] → M → M/M[ℓ] → 0` for a prime `ℓ ∣ n`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain
open Langlands.GaloisCohomology.PoitouTate

universe u

noncomputable section

section Tate

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- If `Ĥ_cⁿ(G, Coind_W^G(ℤ/2)) = 0`, then `Ĥ_cⁿ(G, Coind_W^G N) = 0` for every finite smooth `W`-module
`N` killed by `2` on which `W` acts through elements of `2`-power order (induction on `#N`). -/
theorem subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul (n : ℕ) (W : OpenSubgroup G)
    (hW : Subsingleton (tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n)) :
    ∀ (d : ℕ) (N : Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) [IsSmoothRep N] [Finite N],
      Nat.card N ≤ d → (∀ m : N, 2 • m = 0) → (∀ w, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) →
      Subsingleton (tateCompactCohomologyRes φ ψ (Rep.coind (W : Subgroup G).subtype N) n) := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hd
    have := Nat.card_pos (α := N)
    omega
  | succ d ih =>
    intro N _ _ hd h2 hN
    by_cases hsub : Subsingleton N
    · have : Subsingleton (Rep.coind (W : Subgroup G).subtype N) :=
        ⟨fun a b => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
      exact subsingleton_tateCompactCohomologyRes φ ψ _ n
    rw [not_subsingleton_iff_nontrivial] at hsub
    obtain ⟨m, hm0, hfix⟩ := exists_ne_zero_forall_ρ_eq N h2 hN
    let f := zmodTwoHom N m (h2 m) hfix
    have hfinj : Function.Injective f.hom := fun a b hab =>
      ULift.ext (zmodTwoAddHom_injective (h2 m) hm0 hab)
    let T : Submodule (ULift.{u} ℤ) N := LinearMap.range f.hom.toLinearMap
    let X := cokerShortComplex f
    have : IsSmoothRep X.X₁ := inferInstanceAs (IsSmoothRep (zmodRep.{u} (W : Subgroup G) 2))
    have : IsSmoothRep X.X₂ := inferInstanceAs (IsSmoothRep N)
    have hX : X.ShortExact := cokerShortComplex_shortExact f hfinj
    have hCX := shortExact_coindShortComplexOf (W : Subgroup G) hX
    have : IsSmoothRep X.X₃ := isSmoothRep_quotient _ _ _
    have : Finite (N ⧸ T) := Finite.of_surjective _ (Submodule.mkQ_surjective T)
    have : Finite X.X₃ := inferInstanceAs (Finite (N ⧸ T))
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup G) X).X₁ := isSmoothRep_coind W _
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup G) X).X₂ := isSmoothRep_coind W _
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup G) X).X₃ := isSmoothRep_coind W _
    have hcardT : 2 ≤ Nat.card T := by
      have hm : m ∈ T :=
        ⟨ULift.up 1, (zmodTwoHom_hom_apply N m (h2 m) hfix _).trans (zmodTwoAddHom_one m (h2 m))⟩
      have : Finite T := Subtype.finite
      exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨0, Submodule.zero_mem _⟩, ⟨m, hm⟩,
        fun h => hm0 (congrArg Subtype.val h).symm⟩⟩
    have hcardQ : Nat.card X.X₃ ≤ d := by
      have hc := Submodule.card_eq_card_quotient_mul_card T
      have hpos : 0 < Nat.card (N ⧸ T) := Nat.card_pos
      change Nat.card (N ⧸ T) ≤ d
      nlinarith
    refine subsingleton_tateCompactCohomologyRes_of_shortExact φ ψ hCX n hW ?_
    refine ih X.X₃ hcardQ ?_ ?_
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
      exact (map_nsmul (Submodule.mkQ _) 2 a).symm.trans
        ((congrArg (Submodule.mkQ _) (h2 a)).trans (map_zero _))
    · intro w
      obtain ⟨k, hk⟩ := hN w
      refine ⟨k, DFunLike.ext _ _ fun y => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
      change Submodule.Quotient.mk (p := LinearMap.range f.hom.toLinearMap) (N.ρ (w ^ 2 ^ k) a) =
        Submodule.Quotient.mk a
      rw [hk]
      rfl

/-- **Reduction to `Coind_W^G(ℤ/2)`.** If `Ĥ_cⁿ(G, Coind_W^G(ℤ/2)) = 0` for every open subgroup `W`,
then `Ĥ_cⁿ(G, M) = 0` for every finite smooth `G`-module `M` killed by `2`. -/
theorem subsingleton_tateCompactCohomologyRes_of_two_nsmul (n : ℕ)
    (hW : ∀ W : OpenSubgroup G, Subsingleton (tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (h2 : ∀ m : M, 2 • m = 0) :
    Subsingleton (tateCompactCohomologyRes φ ψ M n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₀ := fixingOpenSubgroup M
  let K₀ : Subgroup G := M.ρ.asGroupHom.ker
  have hUK : (U₀ : Subgroup G) ≤ K₀ := fun g hg => by
    refine (MonoidHom.mem_ker).2 (Units.ext ?_)
    rw [Representation.asGroupHom_apply]
    exact LinearMap.ext fun m => fixingOpenSubgroup_apply M hg m
  have hK₀ : IsOpen (K₀ : Set G) := Subgroup.isOpen_mono hUK U₀.isOpen
  let K₁ : OpenSubgroup G := ⟨K₀, hK₀⟩
  have : K₀.FiniteIndex := finiteIndex_openSubgroup K₁
  have : Finite (G ⧸ K₀) := Subgroup.finite_quotient_of_finiteIndex
  let P : Sylow 2 (G ⧸ K₀) := Classical.arbitrary _
  let W : OpenSubgroup G := ⟨(P : Subgroup (G ⧸ K₀)).comap (QuotientGroup.mk' K₀),
    Subgroup.isOpen_mono (fun g hg => by
      change QuotientGroup.mk' K₀ g ∈ (P : Subgroup (G ⧸ K₀))
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
      exact one_mem _) hK₀⟩
  have hidx : (W : Subgroup G).index = (P : Subgroup (G ⧸ K₀)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K₀)
  have : (P : Subgroup (G ⧸ K₀)).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hodd : ¬ 2 ∣ (W : Subgroup G).index := hidx ▸ Sylow.not_dvd_index P
  have : (W : Subgroup G).FiniteIndex := finiteIndex_openSubgroup W
  have : IsSmoothRep (Rep.coind (W : Subgroup G).subtype (Rep.res (W : Subgroup G).subtype M)) :=
    isSmoothRep_coind W _
  have hunit : coindUnit (W : Subgroup G) M ≫ coindTrace (W : Subgroup G) M = 𝟙 M := by
    rw [coindUnit_comp_coindTrace]
    obtain ⟨c, hc⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    ext a
    change (W : Subgroup G).index • a = a
    rw [hc, add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul]
  refine subsingleton_tateCompactCohomologyRes_of_retract φ ψ _ _ hunit n ?_
  refine subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul φ ψ n W (hW W) _
    (Rep.res (W : Subgroup G).subtype M) le_rfl (fun m => h2 m) ?_
  intro w
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' K₀ (w : G), w.2⟩
  refine ⟨k, ?_⟩
  have hk' : (w : G) ^ 2 ^ k ∈ K₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  have h1 := congrArg Units.val ((MonoidHom.mem_ker).1 hk')
  rw [Representation.asGroupHom_apply] at h1
  exact h1

end Tate

section GS

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Odd primes.** For a prime `ℓ ≠ 2` with the places above `ℓ` in `S` and a finite smooth
`G_S`-module `M` killed by `ℓ`, `Ĥ_cʳ(G_S, M) = 0` for `r ≥ 4`. -/
theorem subsingleton_compactCohomology_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    (hM : ∀ m : M, ℓ • m = 0) {r : ℕ} (hr : 4 ≤ r) : Subsingleton (compactCohomology ι M r) := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two h2
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  have hglob : ∀ q, 3 ≤ q → Subsingleton (cohomology M q) := fun q hq =>
    cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S hℓ.ne_zero hS
      (Or.inl hodd) M hM hq
  refine subsingleton_compactCohomology_of_surjective_of_injective ι hℓ.ne_zero M hM (by omega)
    (fun t => ⟨0, funext fun w => ?_⟩) ?_
  · exact eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ hodd (fun a => hM a) (by omega) _ |>.trans
      (eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ hodd (fun a => hM a) (by omega) _).symm
  · have := hglob (p + 1) (by omega)
    exact fun a b _ => Subsingleton.elim a b

omit [NumberField K] in
theorem mem_of_natCast_mem_of_dvd {n d : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) : v ∈ S := by
  refine hS v ?_
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

/-- **Dévissage.** Let `r ≥ 4`. If `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup `W` of `G_S`
whenever `S` contains the places above `2`, then `Ĥ_cʳ(G_S, M) = 0` for every finite smooth
`G_S`-module `M` killed by an `n ≠ 0` with the places above `n` in `S`. -/
theorem subsingleton_compactCohomology_of_coind {r : ℕ} (hr : 4 ≤ r)
    (hC : (∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ W : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S),
        Subsingleton (compactCohomology ι
          (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
            (zmodRep.{u} (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2)) r)) :
    ∀ (n : ℕ), n ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
        [Finite M], (∀ m : M, n • m = 0) → Subsingleton (compactCohomology ι M r) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hS M _ _ hM
  by_cases hsub : Subsingleton M
  · exact subsingleton_tateCompactCohomologyRes _ _ M r
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hsub ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨c, hc⟩ := hℓn
  let T : Submodule (ULift.{u} ℤ) M := LinearMap.ker (ℓ • LinearMap.id)
  have hmemT : ∀ m : M, m ∈ T ↔ ℓ • m = 0 := fun m => Iff.rfl
  have hT : ∀ g, T ≤ T.comap (M.ρ g) := fun g m hm => by
    change ℓ • M.ρ g m = 0
    rw [← map_nsmul, (hmemT m).1 hm, map_zero]
  let X := cokerShortComplex (Rep.subtype M T hT)
  have hX : X.ShortExact := cokerShortComplex_shortExact _ Subtype.val_injective
  have : IsSmoothRep X.X₁ := inferInstanceAs (IsSmoothRep (M.subrepresentation T hT))
  have : IsSmoothRep X.X₂ := inferInstanceAs (IsSmoothRep M)
  have : IsSmoothRep X.X₃ := isSmoothRep_quotient _ _ _
  have : Finite X.X₁ := Subtype.finite
  have : Finite X.X₃ := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine subsingleton_tateCompactCohomologyRes_of_shortExact _ _ hX r ?_ ?_
  · have hM₁ : ∀ m : X.X₁, ℓ • m = 0 := fun m => Subtype.ext ((hmemT m.1).1 m.2)
    by_cases h2 : ℓ = 2
    · subst h2
      exact subsingleton_tateCompactCohomologyRes_of_two_nsmul _ _ r
        (hC (mem_of_natCast_mem_of_dvd ⟨c, hc⟩ hS)) X.X₁ hM₁
    · exact subsingleton_compactCohomology_of_odd ι hℓ h2
        (mem_of_natCast_mem_of_dvd ⟨c, hc⟩ hS) X.X₁ hM₁ hr
  · have hc0 : c ≠ 0 := by rintro rfl; exact hn (by rw [hc, mul_zero])
    have hclt : c < n := by
      rw [hc]
      exact lt_mul_left (Nat.pos_of_ne_zero hc0) hℓ.one_lt
    refine ih c hclt hc0 (mem_of_natCast_mem_of_dvd ⟨ℓ, by rw [hc, mul_comm]⟩ hS) X.X₃ ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    refine (map_nsmul (Submodule.mkQ _) c a).symm.trans ((Submodule.Quotient.mk_eq_zero _).2 ?_)
    refine ⟨⟨c • a, ?_⟩, rfl⟩
    rw [hmemT, ← mul_smul, ← hc]
    exact hM a

end GS

end

end Langlands.GaloisCohomology
