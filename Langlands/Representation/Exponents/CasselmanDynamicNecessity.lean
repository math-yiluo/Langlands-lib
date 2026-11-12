import Langlands.Representation.Jacquet.IwahoriSquareIntegrableBound
import Langlands.Representation.Jacquet.IwahoriModulusIndex
import Langlands.BruhatTits.Unipotent.ParabolicPointContraction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.NormalizedIwahoriEigenCoefficient
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof

/-! # Square integrability bounds exponents along weak dynamic contractions

Let `χ` and `λ` be cocharacters of a connected reductive group over a
nonarchimedean local field, with the dynamic radicals of `χ` and `χ⁻¹` contained in
the dynamic parabolics of `λ` and `λ⁻¹`, and with a nonidentity rational point in
both `U(χ)` and `U(λ)`. For a square-integrable representation and a generalized
eigencharacter of the normalized Jacquet module of the dynamic parabolic of `χ`,
pulled back along a homomorphism into the center of the dynamic Levi which sends
two elements to `χ(t)` and `λ(t)` for a unit `t` with `t ^ n → 0`, the
eigencharacter has modulus strictly below one at the preimage of `λ(t)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Jacquet

universe uV

/-- Commuting endomorphisms with a common nonzero generalized eigenvector have a
common eigenvector for the same eigenvalues, inside every submodule stable under
both and containing the generalized eigenvector. -/
theorem exists_common_eigenvector {E : Type uV} [AddCommGroup E] [Module ℂ E]
    (f g : Module.End ℂ E) (hfg : Commute f g) (Y : Submodule ℂ E)
    (hfY : ∀ y ∈ Y, f y ∈ Y) (hgY : ∀ y ∈ Y, g y ∈ Y)
    (α β : ℂ) (d : ℕ) (v : E) (hv : v ≠ 0) (hvY : v ∈ Y)
    (hf : ((f - α • 1) ^ d) v = 0) (hg : ((g - β • 1) ^ d) v = 0) :
    ∃ w : E, w ≠ 0 ∧ w ∈ Y ∧ f w = α • w ∧ g w = β • w := by
  set q := f - α • 1 with hq
  set p := g - β • 1 with hp
  have hpq : Commute p q := by
    rw [hp, hq]
    exact ((hfg.symm.sub_left (Commute.smul_left (Commute.one_left _) β)).sub_right
      (Commute.smul_right (Commute.one_right _) α))
  -- a nonzero vector killed by `q`
  have hex1 : ∃ i, (q ^ (i + 1)) v = 0 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exact absurd (by simpa using hf) hv
    · exact ⟨d - 1, by rwa [Nat.sub_add_cancel hd]⟩
  classical
  let i := Nat.find hex1
  have hi : (q ^ (i + 1)) v = 0 := Nat.find_spec hex1
  have hi' : (q ^ i) v ≠ 0 := by
    intro h0
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, Module.End.one_apply] at h0
      exact hv h0
    · have := Nat.find_min hex1 (Nat.sub_lt hi0 Nat.one_pos)
      rw [Nat.sub_add_cancel hi0] at this
      exact this h0
  set v1 := (q ^ i) v with hv1
  have hqv1 : q v1 = 0 := by
    rw [hv1, ← Module.End.mul_apply, ← pow_succ']
    exact hi
  have hpv1 : (p ^ d) v1 = 0 := by
    rw [hv1, ← Module.End.mul_apply, ((hpq.pow_left d).pow_right i).eq, Module.End.mul_apply,
      hg, map_zero]
  have hex2 : ∃ j, (p ^ (j + 1)) v1 = 0 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exact absurd (by simpa using hpv1) hi'
    · exact ⟨d - 1, by rwa [Nat.sub_add_cancel hd]⟩
  let j := Nat.find hex2
  have hj : (p ^ (j + 1)) v1 = 0 := Nat.find_spec hex2
  have hj' : (p ^ j) v1 ≠ 0 := by
    intro h0
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero, Module.End.one_apply] at h0
      exact hi' h0
    · have := Nat.find_min hex2 (Nat.sub_lt hj0 Nat.one_pos)
      rw [Nat.sub_add_cancel hj0] at this
      exact this h0
  have hqY : ∀ y ∈ Y, q y ∈ Y := fun y hy => by
    rw [hq, LinearMap.sub_apply]
    exact Y.sub_mem (hfY y hy) (by simpa using Y.smul_mem α hy)
  have hpY : ∀ y ∈ Y, p y ∈ Y := fun y hy => by
    rw [hp, LinearMap.sub_apply]
    exact Y.sub_mem (hgY y hy) (by simpa using Y.smul_mem β hy)
  have hpowY : ∀ (h : Module.End ℂ E), (∀ y ∈ Y, h y ∈ Y) → ∀ n : ℕ, ∀ y ∈ Y, (h ^ n) y ∈ Y := by
    intro h hh n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hh _ (ih y hy)
  have hwY : (p ^ j) v1 ∈ Y := hpowY p hpY j v1 (hpowY q hqY i v hvY)
  refine ⟨(p ^ j) v1, hj', hwY, ?_, ?_⟩
  · have h0 : q ((p ^ j) v1) = 0 := by
      rw [← Module.End.mul_apply, ← (hpq.pow_left j).eq, Module.End.mul_apply, hqv1, map_zero]
    have : (f - α • 1) ((p ^ j) v1) = 0 := h0
    rw [LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  · have h0 : p ((p ^ j) v1) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hj
    have : (g - β • 1) ((p ^ j) v1) = 0 := h0
    rw [LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this

end Langlands.Jacquet

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

universe u v

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- **Square integrability along a weak dynamic contraction.** -/
theorem norm_lt_one_of_squareIntegrable_dynamic (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure]
      (χ ξ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (_hUP : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ≤
        (Dynamic.parabolic ξ).carrier (Over.mk (𝟙 _)))
      (_hOP : (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) ≤
        (Dynamic.parabolic (Dynamic.inverseCocharacter ξ)).carrier (Over.mk (𝟙 _)))
      (x : rationalPoints G) (_hx1 : x ≠ 1)
      (_hxU : x ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
      (_hxL : x ∈ (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 _)))
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
      (_hsq : IsSquareIntegrableModCenter π.representation haar)
      {B : Type u} [Group B]
      (incl : B →* (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
      (_hι : ∀ s, incl s ∈ Subgroup.center ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))))
      (χB : B →* ℂˣ)
      (_hχB : IsGeneralizedEigencharacter
        (((normalizedJacquetFunctor ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
          ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
          (isClosed_unipotentPoints χ)
          (Dynamic.centralizer_le_normalizer_unipotent χ _)).obj π).representation.comp incl) χB)
      (a0 b0 : B) (t : kˣ) (_ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
      (_ha0 : ((incl a0 : _) : rationalPoints G) = cocharPoint ξ t)
      (_hb0 : ((incl b0 : _) : rationalPoints G) = cocharPoint χ t),
      ‖(χB a0 : ℂ)‖ < 1 := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ _ _ haar _ χ ξ hUP hOP x hx1 hxU hxL π hsq B _ incl hι χB hχB a0 b0 t ht ha0 hb0
  have := hG.smooth
  have := hG.isSeparated
  have hT2 : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let N := (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let M := (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let O := (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have hNc : IsClosed (N : Set (rationalPoints G)) := isClosed_unipotentPoints χ
  have hOc : IsClosed (O : Set (rationalPoints G)) :=
    isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)
  have hMN : M ≤ Subgroup.normalizer (N : Set (rationalPoints G)) :=
    Dynamic.centralizer_le_normalizer_unipotent χ _
  have hMO : M ≤ Subgroup.normalizer (O : Set (rationalPoints G)) := by
    have h := Dynamic.centralizer_le_normalizer_unipotent (Dynamic.inverseCocharacter χ)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    rwa [Dynamic.centralizer_inverseCocharacter χ] at h
  let b : rationalPoints G := cocharPoint χ t
  let a : rationalPoints G := cocharPoint ξ t
  have hbM : b ∈ M := cocharPoint_mem_centralizer χ t
  have hbcomm : ∀ m ∈ M, m * b = b * m := fun m hm => (commute_cocharPoint χ hm t).eq
  have haM : a ∈ M := by
    change cocharPoint ξ t ∈ M
    rw [← ha0]
    exact (incl a0).2
  have hacomm : ∀ m ∈ M, m * a = a * m := by
    intro m hm
    have h := Subgroup.mem_center_iff.mp (hι a0) ⟨m, hm⟩
    have h' := congrArg Subtype.val h
    change m * cocharPoint ξ t = cocharPoint ξ t * m
    rw [← ha0]
    exact h'
  have hunique := dynamic_opposite_factorization_unique χ
  have hcell : ∀ A ∈ 𝓝 (1 : rationalPoints G), ∀ B' ∈ 𝓝 (1 : rationalPoints G),
      ∀ C ∈ 𝓝 (1 : rationalPoints G),
      {x : rationalPoints G | ∃ a ∈ A ∩ (O : Set (rationalPoints G)),
        ∃ b ∈ B' ∩ (M : Set (rationalPoints G)), ∃ c ∈ C ∩ (N : Set (rationalPoints G)),
          x = a * b * c} ∈ 𝓝 (1 : rationalPoints G) := by
    have htop : (pointTopology : TopologicalSpace (rationalPoints G)) =
        rationalSchemeTopology k G.X :=
      rationalPointTopology_eq_rationalSchemeTopology k G.X
    have h0 := Dynamic.opposite_cell_mem_nhds_one k G χ
    rw [← htop] at h0
    exact h0
  have hcontrU : ∀ C : Set (rationalPoints G), IsCompact C → C ⊆ N →
      ∀ W ∈ 𝓝 (1 : rationalPoints G), ∀ᶠ n in atTop, ∀ c ∈ C, b ^ n * c * (b ^ n)⁻¹ ∈ W :=
    fun C hC hCU W hW => eventually_cocharPoint_pow_conj_mem_ambient χ t ht C hC hCU W hW
  have hcontrO : ∀ C : Set (rationalPoints G), IsCompact C → C ⊆ O →
      ∀ W ∈ 𝓝 (1 : rationalPoints G), ∀ᶠ n in atTop, ∀ c ∈ C, (b ^ n)⁻¹ * c * b ^ n ∈ W := by
    intro C hC hCO W hW
    have h := eventually_cocharPoint_pow_conj_mem_ambient (Dynamic.inverseCocharacter χ)
      t ht C hC hCO W hW
    simpa only [cocharPoint_inverseCocharacter, inv_pow, inv_inv] using h
  let S : Set k := insert 0 (Set.range fun n : ℕ => (t : k) ^ n)
  have hS : IsCompact S := ht.isCompact_insert_range
  have hSmem : ∀ i : ℕ, ((t ^ i : kˣ) : k) ∈ S := fun i =>
    Set.mem_insert_of_mem _ ⟨i, by simp⟩
  have hweakU : ∀ W ∈ 𝓝 (1 : rationalPoints G), ∃ W' ∈ 𝓝 (1 : rationalPoints G),
      ∀ i : ℕ, ∀ y ∈ N, y ∈ W' → a ^ i * y * (a ^ i)⁻¹ ∈ W := by
    intro W hW
    obtain ⟨W', hW', h⟩ := exists_nhds_forall_conj_mem_of_parabolic ξ S hS W hW
    refine ⟨W', hW', fun i y hy hyW => ?_⟩
    change cocharPoint ξ t ^ i * y * (cocharPoint ξ t ^ i)⁻¹ ∈ W
    rw [← cocharPoint_pow]
    exact h (t ^ i) (hSmem i) y (hUP hy) hyW
  have hweakO : ∀ W ∈ 𝓝 (1 : rationalPoints G), ∃ W' ∈ 𝓝 (1 : rationalPoints G),
      ∀ i : ℕ, ∀ y ∈ O, y ∈ W' → (a ^ i)⁻¹ * y * a ^ i ∈ W := by
    intro W hW
    obtain ⟨W', hW', h⟩ := exists_nhds_forall_conj_mem_of_parabolic
      (Dynamic.inverseCocharacter ξ) S hS W hW
    refine ⟨W', hW', fun i y hy hyW => ?_⟩
    have h1 := h (t ^ i) (hSmem i) y (hOP hy) hyW
    rw [cocharPoint_inverseCocharacter, inv_inv, cocharPoint_pow] at h1
    exact h1
  have hbasis := Jacquet.exists_weakIwahoriBasis_of_contraction hOc hNc hbM haM hbcomm hacomm
    hMO hMN hunique hcell hcontrU hcontrO hweakU hweakO
  -- the generalized eigenvector in the ordinary twisted Jacquet module
  let eta := HaarModulus.closedInverseHalfCharacter N hNc M hMN
  let e := normalizedJacquetOrdinaryEquiv N M hNc hMN π
  let eι : Representation.Equiv
      (((normalizedJacquetFunctor N M hNc hMN).obj π).representation.comp incl)
        ((Jacquet.characterTwistedAction π.representation N M hMN eta).comp incl) :=
    Representation.Equiv.mk e.toLinearEquiv (fun s => e.isIntertwining' (incl s))
  have hχ' := (isGeneralizedEigencharacter_iff_of_equiv eι χB).mp hχB
  obtain ⟨d, v, hv0, hvd⟩ := (isGeneralizedEigencharacter_iff _ χB).mp hχ'
  obtain ⟨L, hvL⟩ := Jacquet.isSmooth_action π.representation N M hMN hsq.1.1 v
  obtain ⟨W, hW, hWL⟩ := isOpen_induced_iff.mp L.isOpen
  have h1W : (1 : rationalPoints G) ∈ W := by
    have : (1 : M) ∈ (Subtype.val : M → rationalPoints G) ⁻¹' W := by
      rw [hWL]
      exact L.one_mem
    exact this
  obtain ⟨K, hK, hKW, hKb, hKa⟩ := hbasis W hW h1W
  let H : Subgroup M := K.toSubgroup.comap M.subtype
  have hvK : v ∈ fixedVectors (Jacquet.action π.representation N M hMN) H := by
    intro m
    have hmL : (m : M) ∈ L := by
      change (m : M) ∈ (L : Set M)
      rw [← hWL]
      exact hKW m.property
    exact hvL ⟨m.val, hmL⟩
  -- a common eigenvector of the two central elements
  let za : Subgroup.center M := ⟨incl a0, hι a0⟩
  let zb : Subgroup.center M := ⟨incl b0, hι b0⟩
  let Fa := Jacquet.characterTwistedAction π.representation N M hMN eta (za : M)
  let Fb := Jacquet.characterTwistedAction π.representation N M hMN eta (zb : M)
  have hcommM : incl a0 * incl b0 = incl b0 * incl a0 :=
    Subgroup.mem_center_iff.mp (hι b0) (incl a0)
  have hFab : Commute Fa Fb := by
    change Fa * Fb = Fb * Fa
    have h1 := (map_mul (Jacquet.characterTwistedAction π.representation N M hMN eta)
      (incl a0) (incl b0)).symm
    have h2 := (map_mul (Jacquet.characterTwistedAction π.representation N M hMN eta)
      (incl b0) (incl a0)).symm
    rw [hcommM] at h1
    exact h1.trans h2.symm
  obtain ⟨w, hw0, hwY, hwa, hwb⟩ := Jacquet.exists_common_eigenvector Fa Fb hFab
    (fixedVectors (Jacquet.action π.representation N M hMN) H)
    (fun y hy => Jacquet.characterTwistedAction_mem_fixedVectors_of_mem_center
      π.representation N M hMN eta H za hy)
    (fun y hy => Jacquet.characterTwistedAction_mem_fixedVectors_of_mem_center
      π.representation N M hMN eta H zb hy)
    (χB a0 : ℂ) (χB b0 : ℂ) d v hv0 hvK (hvd a0) (hvd b0)
  -- unnormalized eigenvalues
  have hza : (za : M) = ⟨a, haM⟩ := Subtype.ext ha0
  have hzb : (zb : M) = ⟨b, hbM⟩ := Subtype.ext hb0
  have hunnorm : ∀ (z : M) (c : ℂ),
      Jacquet.characterTwistedAction π.representation N M hMN eta z w = c • w →
        Jacquet.action π.representation N M hMN z w = ((eta z : ℂ)⁻¹ * c) • w := by
    intro z c h
    change (eta z : ℂ) • Jacquet.action π.representation N M hMN z w = c • w at h
    have h' := congrArg (fun y => (eta z : ℂ)⁻¹ • y) h
    simpa only [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] using h'
  have hwa' := hunnorm (za : M) (χB a0) hwa
  have hwb' := hunnorm (zb : M) (χB b0) hwb
  rw [hza] at hwa'
  rw [hzb] at hwb'
  -- the full center lies in the dynamic Levi
  have hZ : Subgroup.center (rationalPoints G) ≤ M := by
    intro z hz
    rw [← (rationalCenterComparison k G hG : schemeCenterPoints G = _)] at hz
    exact SubgroupFunctor.le_def.mp (center_le_dynamicCentralizer χ) _ hz
  -- the Iwahori index of the weak contraction exceeds one
  have hda : 1 < Jacquet.iwahoriIndex K N a := by
    by_contra hle
    have hne := Jacquet.iwahoriIndex_ne_zero hK hNc (hMN haM)
    have h1 : Jacquet.iwahoriIndex K N a = 1 := by omega
    have hle' : K.toSubgroup ⊓ N ≤ Jacquet.conjRadicalPiece K N a :=
      Subgroup.relIndex_eq_one.mp h1
    have hinv : ∀ u ∈ K.toSubgroup ⊓ N, a⁻¹ * u * a ∈ K.toSubgroup ⊓ N := by
      intro u hu
      obtain ⟨v', hv', hvu⟩ := Jacquet.mem_conjRadicalPiece.mp (hle' hu)
      rw [← hvu]
      simpa [mul_assoc] using hv'
    have hinvpow : ∀ n : ℕ, ∀ u ∈ K.toSubgroup ⊓ N, (a ^ n)⁻¹ * u * a ^ n ∈ K.toSubgroup ⊓ N := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih =>
        intro u hu
        have e : (a ^ (n + 1))⁻¹ * u * a ^ (n + 1) = a⁻¹ * ((a ^ n)⁻¹ * u * a ^ n) * a := by
          rw [pow_succ]
          group
        rw [e]
        exact hinv _ (ih u hu)
    let UL := (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have haL : a ∈ (Dynamic.centralizer ξ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      cocharPoint_mem_centralizer ξ t
    have hULn : ∀ n : ℕ, ∀ y ∈ UL, (a ^ n)⁻¹ * y * a ^ n ∈ UL := by
      intro n y hy
      have hn := pow_mem haL n
      exact (Subgroup.mem_normalizer_iff''.mp
        (Dynamic.centralizer_le_normalizer_unipotent ξ _ hn) y).mp hy
    let C : Set (rationalPoints G) :=
      ((K.toSubgroup ⊓ N : Subgroup (rationalPoints G)) : Set (rationalPoints G)) ∩ UL
    have hCc : IsCompact C :=
      (hK.inter_right hNc).inter_right (isClosed_unipotentPoints ξ)
    have hCsub : ∀ n : ℕ, ∀ y ∈ C, (a ^ n)⁻¹ * y * a ^ n ∈ C :=
      fun n y hy => ⟨hinvpow n y hy.1, hULn n y hy.2⟩
    have hC1 : ∀ y ∈ C, y = 1 := by
      intro y hy
      by_contra hy1
      have hW : ({y}ᶜ : Set (rationalPoints G)) ∈ 𝓝 (1 : rationalPoints G) :=
        isOpen_compl_singleton.mem_nhds (Ne.symm hy1)
      obtain ⟨n, hn⟩ := (eventually_cocharPoint_pow_conj_mem_ambient ξ t ht C hCc
        (fun z hz => hz.2) _ hW).exists
      apply hn _ (hCsub n y hy)
      change cocharPoint ξ t ^ n * ((cocharPoint ξ t ^ n)⁻¹ * y * cocharPoint ξ t ^ n) *
        (cocharPoint ξ t ^ n)⁻¹ = y
      group
    obtain ⟨n, hn⟩ := (eventually_cocharPoint_pow_conj_mem_ambient ξ t ht {x}
      isCompact_singleton (Set.singleton_subset_iff.mpr hxL) (K : Set (rationalPoints G))
      K.mem_nhds_one).exists
    have hyN : a ^ n * x * (a ^ n)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hMN (pow_mem haM n)) x).mp hxU
    have hyL : a ^ n * x * (a ^ n)⁻¹ ∈ UL :=
      (Subgroup.mem_normalizer_iff.mp
        (Dynamic.centralizer_le_normalizer_unipotent ξ _ (pow_mem haL n)) x).mp hxL
    have hy := hC1 _ ⟨⟨hn x rfl, hyN⟩, hyL⟩
    apply hx1
    have e : x = (a ^ n)⁻¹ * (a ^ n * x * (a ^ n)⁻¹) * a ^ n := by group
    rw [e, hy]
    group
  obtain ⟨c, hc⟩ := hsq.2
  have hbound := Jacquet.iwahoriIndex_mul_enorm_sq_lt_one haar π.representation hsq.1.1 c K hK
    N M O hNc hMN hMO hunique hZ b a hKb hKa (hbcomm a haM) hbcomm hacomm (hsq.1.2 K)
    ((eta ⟨b, hbM⟩ : ℂ)⁻¹ * χB b0) ((eta ⟨a, haM⟩ : ℂ)⁻¹ * χB a0) w hw0 hwY hwb' hwa' hda hc
  -- the modulus of the normalization is the Iwahori index
  have heta : ‖(eta ⟨a, haM⟩ : ℂ)‖ ^ 2 = (Jacquet.iwahoriIndex K N a : ℝ) :=
    Jacquet.norm_closedInverseHalfCharacter_sq hK hNc M hMN ⟨a, haM⟩
      (fun u hu => hKa.upper u hu)
  have hbound' : (Jacquet.iwahoriIndex K N a : ℝ) *
      ‖(eta ⟨a, haM⟩ : ℂ)⁻¹ * χB a0‖ ^ 2 < 1 := by
    have h2 : ENNReal.ofReal ((Jacquet.iwahoriIndex K N a : ℝ) *
        ‖(eta ⟨a, haM⟩ : ℂ)⁻¹ * χB a0‖ ^ 2) < 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      exact hbound
    exact ENNReal.ofReal_lt_one.mp h2
  have hr : 0 < ‖(eta ⟨a, haM⟩ : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  rw [norm_mul, norm_inv, mul_pow, inv_pow, ← mul_assoc, ← heta,
    mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul] at hbound'
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hbound'

end Langlands.Aubert.General.RationalPointFamily
