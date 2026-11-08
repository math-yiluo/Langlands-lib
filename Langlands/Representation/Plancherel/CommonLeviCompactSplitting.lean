import Langlands.Representation.Plancherel.StandardIntertwiningOppositeCharts
import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.GroupScheme.Dynamic.RationalOpenCell

/-! # Small compact open subgroups splitting along two cocharacters with one Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.StandardIntertwining

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

namespace HasCompactOpenProduct

/-- For a subgroup `Q`, the two factors may be taken in either order. -/
theorem swap {Q : OpenSubgroup Γ} {A B C : Subgroup Γ}
    (h : HasCompactOpenProduct (Q : Set Γ) A B C) :
    HasCompactOpenProduct (Q : Set Γ) B A C := by
  intro g hg hgQ
  obtain ⟨a, ha, haQ, b, hb, hbQ, e⟩ := h g⁻¹ (C.inv_mem hg) (Q.inv_mem hgQ)
  refine ⟨b⁻¹, B.inv_mem hb, Q.inv_mem hbQ, a⁻¹, A.inv_mem ha, Q.inv_mem haQ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

omit [TopologicalSpace Γ] in
/-- The factors may be enlarged. -/
theorem mono {Q : Set Γ} {A B A' B' C : Subgroup Γ}
    (h : HasCompactOpenProduct Q A B C) (hA : A ≤ A') (hB : B ≤ B') :
    HasCompactOpenProduct Q A' B' C := by
  intro g hg hgQ
  obtain ⟨a, ha, haQ, b, hb, hbQ, e⟩ := h g hg hgQ
  exact ⟨a, hA ha, haQ, b, hB hb, hbQ, e⟩

end HasCompactOpenProduct

omit [TopologicalSpace Γ] in
/-- **Splitting by a conjugation cut.** Let `V` factor as `O' M' U'` with unique
factorizations, and let `H = A B` with `A ≤ O'` and `B ≤ U'`. If `K ∩ H` consists
of the elements of `H` whose conjugates by a set `C` normalizing `O'` and `U'`
all lie in `V`, then `K ∩ H = (K ∩ A)(K ∩ B)`. -/
theorem hasCompactOpenProduct_of_conj_mem {K V C : Set Γ} {O' M' U' A B H : Subgroup Γ}
    (hV : ∀ v ∈ V, ∃ o ∈ O', ∃ m ∈ M', ∃ w ∈ U', o ∈ V ∧ w ∈ V ∧ v = o * m * w)
    (huniq : ∀ o ∈ O', ∀ m ∈ M', ∀ w ∈ U', ∀ o' ∈ O', ∀ m' ∈ M', ∀ w' ∈ U',
      o * m * w = o' * m' * w' → o = o' ∧ m = m' ∧ w = w')
    (hAO : A ≤ O') (hBU : B ≤ U') (hAH : A ≤ H) (hBH : B ≤ H)
    (hchart : ∀ x ∈ H, ∃ a ∈ A, ∃ b ∈ B, x = a * b)
    (hCO : ∀ c ∈ C, ∀ x ∈ O', c * x * c⁻¹ ∈ O')
    (hCU : ∀ c ∈ C, ∀ x ∈ U', c * x * c⁻¹ ∈ U')
    (hK : ∀ x ∈ H, x ∈ K ↔ ∀ c ∈ C, c * x * c⁻¹ ∈ V) :
    HasCompactOpenProduct K A B H := by
  intro x hx hxK
  obtain ⟨a, ha, b, hb, rfl⟩ := hchart x hx
  have key : ∀ c ∈ C, c * a * c⁻¹ ∈ V ∧ c * b * c⁻¹ ∈ V := by
    intro c hc
    obtain ⟨o, ho, m, hm, w, hw, hoV, hwV, e⟩ := hV _ ((hK _ hx).1 hxK c hc)
    have e' : (c * a * c⁻¹) * 1 * (c * b * c⁻¹) = o * m * w := by
      rw [← e]
      group
    obtain ⟨h1, -, h3⟩ := huniq _ (hCO c hc a (hAO ha)) 1 M'.one_mem _ (hCU c hc b (hBU hb))
      o ho m hm w hw e'
    exact ⟨h1 ▸ hoV, h3 ▸ hwV⟩
  exact ⟨a, ha, (hK a (hAH ha)).2 fun c hc => (key c hc).1,
    b, hb, (hK b (hBH hb)).2 fun c hc => (key c hc).2, rfl⟩

/-- The elements of `H` all of whose conjugates by the nonnegative powers of `h`
lie in `V`. -/
def stablePiece (V : OpenSubgroup Γ) (H : Subgroup Γ) (h : Γ) : Subgroup Γ :=
  H ⊓ ⨅ k : ℕ, V.toSubgroup.comap (MulAut.conj (h ^ k)).toMonoidHom

theorem mem_stablePiece {V : OpenSubgroup Γ} {H : Subgroup Γ} {h x : Γ} :
    x ∈ stablePiece V H h ↔ x ∈ H ∧ ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ ∈ V := by
  simp only [stablePiece, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OpenSubgroup.mem_toSubgroup]

/-- The stable piece is a compact subgroup of `H ∩ V`, stable under conjugation by
`h`, normalized by `V ∩ M`, and relatively open in `H` when the powers of `h`
contract `H`. This is the published `Jacquet.exists_stable_piece`, for the
explicit subgroup `stablePiece V H h`. -/
theorem stablePiece_spec [IsTopologicalGroup Γ] (V : OpenSubgroup Γ)
    (hVc : IsCompact (V : Set Γ)) (H M : Subgroup Γ) (hH : IsClosed (H : Set Γ))
    {h : Γ} (hh : h ∈ M) (hcomm : ∀ m ∈ M, m * h = h * m)
    (hMH : M ≤ Subgroup.normalizer (H : Set Γ))
    (hcontr : ∀ C : Set Γ, IsCompact C → C ⊆ H → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, h ^ n * c * (h ^ n)⁻¹ ∈ W) :
    stablePiece V H h ≤ H ∧ ((stablePiece V H h : Subgroup Γ) : Set Γ) ⊆ V ∧
      IsCompact ((stablePiece V H h : Subgroup Γ) : Set Γ) ∧
      (∀ x ∈ stablePiece V H h, h * x * h⁻¹ ∈ stablePiece V H h) ∧
      (∀ b ∈ V.toSubgroup ⊓ M, ∀ x ∈ stablePiece V H h,
        b * x * b⁻¹ ∈ stablePiece V H h) ∧
      ∃ Y ∈ 𝓝 (1 : Γ), ∀ x ∈ H, x ∈ Y → x ∈ stablePiece V H h := by
  have hmem : ∀ x, x ∈ stablePiece V H h ↔ x ∈ H ∧ ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ ∈ V :=
    fun x => mem_stablePiece
  have hPV : ((stablePiece V H h : Subgroup Γ) : Set Γ) ⊆ V := fun x hx => by
    simpa using ((hmem x).1 hx).2 0
  have hset : ((stablePiece V H h : Subgroup Γ) : Set Γ) =
      (H : Set Γ) ∩ ⋂ k : ℕ, (fun x => h ^ k * x * (h ^ k)⁻¹) ⁻¹' (V : Set Γ) := by
    ext x
    rw [SetLike.mem_coe, hmem]
    simp
  have hPclosed : IsClosed ((stablePiece V H h : Subgroup Γ) : Set Γ) := by
    rw [hset]
    exact hH.inter (isClosed_iInter fun k => V.isClosed.preimage (by fun_prop))
  refine ⟨fun x hx => ((hmem x).1 hx).1, hPV, hVc.of_isClosed_subset hPclosed hPV, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hh) x).mp hxH, fun k => ?_⟩
    have e : h ^ k * (h * x * h⁻¹) * (h ^ k)⁻¹ = h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ := by
      group
    rw [e]
    exact hxV (k + 1)
  · intro b hb x hx
    obtain ⟨hbV, hbM⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hbM) x).mp hxH, fun k => ?_⟩
    have hbk : Commute (h ^ k) b := (Commute.pow_right (hcomm b hbM) k).symm
    rw [Jacquet.conj_conj_of_commute hbk]
    exact V.mul_mem (V.mul_mem hbV (hxV k)) (V.inv_mem hbV)
  · obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hcontr ((V : Set Γ) ∩ H) (hVc.inter_right hH) Set.inter_subset_right V V.mem_nhds_one)
    refine ⟨{x | ∀ k ∈ Finset.range (N + 1), h ^ k * x * (h ^ k)⁻¹ ∈ V}, ?_, ?_⟩
    · refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
      have hc : Continuous fun x : Γ => h ^ k * x * (h ^ k)⁻¹ := by fun_prop
      exact hc.continuousAt.eventually_mem (by simpa using V.mem_nhds_one)
    · intro x hxH hxY
      refine (hmem x).2 ⟨hxH, fun k => ?_⟩
      rcases le_or_gt k N with hk | hk
      · exact hxY k (Finset.mem_range.mpr (by omega))
      · have hxV : x ∈ V := by
          simpa using hxY 0 (Finset.mem_range.mpr (by omega))
        exact hN k hk.le x ⟨hxV, hxH⟩

/-- **Iwahori subgroup cut out by a given compact open subgroup.** Under the
hypotheses of the published `Jacquet.hasOppositeIwahoriContractionBasis_of_contraction`,
every compact open subgroup `V` contains a compact open subgroup `K` with
`K = (K ∩ O)(K ∩ M)(K ∩ U)`, such that `K ∩ U` is exactly the set of `x ∈ U` with
`g ^ j x g ^ -j ∈ V` for all `j ≥ 0`, and for one `n`, `K ∩ O` is exactly the set of
`x ∈ O` with `(g⁻¹ ^ j g ^ n) x (g⁻¹ ^ j g ^ n)⁻¹ ∈ V` for all `j ≥ 0`. The
construction is the published one, with the two pieces kept explicit. -/
theorem exists_iwahori_stablePieces [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    {U M O : Subgroup Γ} {g : Γ} (V : OpenSubgroup Γ) (hVc : IsCompact (V : Set Γ))
    (hO : IsClosed (O : Set Γ)) (hU : IsClosed (U : Set Γ))
    (hg : g ∈ M) (hcomm : ∀ m ∈ M, m * g = g * m)
    (hMO : M ≤ Subgroup.normalizer (O : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hunique : ∀ o ∈ O, ∀ m ∈ M, ∀ u ∈ U, ∀ o' ∈ O, ∀ m' ∈ M, ∀ u' ∈ U,
      o * m * u = o' * m' * u' → o = o' ∧ m = m' ∧ u = u')
    (hcell : ∀ A ∈ 𝓝 (1 : Γ), ∀ B ∈ 𝓝 (1 : Γ), ∀ C ∈ 𝓝 (1 : Γ),
      {x : Γ | ∃ a ∈ A ∩ (O : Set Γ), ∃ b ∈ B ∩ (M : Set Γ), ∃ c ∈ C ∩ (U : Set Γ),
        x = a * b * c} ∈ 𝓝 (1 : Γ))
    (hcontrU : ∀ C : Set Γ, IsCompact C → C ⊆ U → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, g ^ n * c * (g ^ n)⁻¹ ∈ W)
    (hcontrO : ∀ C : Set Γ, IsCompact C → C ⊆ O → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, (g ^ n)⁻¹ * c * g ^ n ∈ W) :
    ∃ K : OpenSubgroup Γ, IsCompact (K : Set Γ) ∧ (K : Set Γ) ⊆ V ∧
      (∀ k ∈ K, ∃ a ∈ O, ∃ b ∈ M, ∃ c ∈ U, a ∈ K ∧ b ∈ K ∧ c ∈ K ∧ k = a * b * c) ∧
      (∀ x ∈ U, x ∈ K ↔ ∀ j : ℕ, g ^ j * x * (g ^ j)⁻¹ ∈ V) ∧
      ∃ n : ℕ, ∀ x ∈ O, x ∈ K ↔
        ∀ j : ℕ, (g⁻¹ ^ j * g ^ n) * x * (g⁻¹ ^ j * g ^ n)⁻¹ ∈ V := by
  have hgpow : ∀ n : ℕ, g ^ n ∈ M := fun n => pow_mem hg n
  have hOconj : ∀ m ∈ M, ∀ x ∈ O, m * x * m⁻¹ ∈ O :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMO hm) x).mp hx
  have hUconj : ∀ m ∈ M, ∀ x ∈ U, m * x * m⁻¹ ∈ U :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMU hm) x).mp hx
  -- The `O`-piece, stable under conjugation by `g⁻¹`.
  set A0 := stablePiece V O g⁻¹ with hA0def
  obtain ⟨hA0O, hA0V, hA0c, hA0g, hA0B, YA, hYA, hYA0⟩ :=
    stablePiece_spec V hVc O M hO (inv_mem hg)
      (fun m hm => (Commute.inv_right (hcomm m hm)).eq) hMO
      (fun C hC hCO W hW => by simpa only [inv_pow, inv_inv] using hcontrO C hC hCO W hW)
  -- The `U`-piece, stable under conjugation by `g`.
  set C0 := stablePiece V U g with hC0def
  obtain ⟨hC0U, hC0V, hC0c, hC0g, hC0B, YC, hYC, hYC0⟩ :=
    stablePiece_spec V hVc U M hU hg hcomm hMU hcontrU
  have hA0pow : ∀ n : ℕ, ∀ x ∈ A0, (g ^ n)⁻¹ * x * g ^ n ∈ A0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have e : (g ^ (n + 1))⁻¹ * x * g ^ (n + 1) =
          g⁻¹ * ((g ^ n)⁻¹ * x * g ^ n) * g⁻¹⁻¹ := by group
      rw [e]
      exact hA0g _ (ih x hx)
  let B0 : Subgroup Γ := V.toSubgroup ⊓ M
  -- An identity neighborhood made of the three pieces.
  let Z : Set Γ := {x | ∃ a ∈ A0, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c}
  have hZ : Z ∈ 𝓝 (1 : Γ) := by
    refine Filter.mem_of_superset (hcell YA hYA (V : Set Γ) V.mem_nhds_one YC hYC) ?_
    rintro x ⟨a, ⟨haY, haO⟩, b, ⟨hbV, hbM⟩, c, ⟨hcY, hcU⟩, rfl⟩
    exact ⟨a, hYA0 a haO haY, b, Subgroup.mem_inf.mpr ⟨hbV, hbM⟩, c, hYC0 c hcU hcY, rfl⟩
  obtain ⟨Q, hQZ⟩ := NonarchimedeanGroup.is_nonarchimedean Z hZ
  have hQn : (Q : Set Γ) ∈ 𝓝 (1 : Γ) := Q.mem_nhds_one
  -- Choice of the shrinking exponent `n`.
  have hY1 : {y : Γ | ∀ s ∈ (A0 : Set Γ), s * y * s⁻¹ ∈ Q} ∈ 𝓝 (1 : Γ) :=
    Jacquet.eventually_forall_conj_mem hA0c hQn
  have hY2 : {y : Γ | y⁻¹ ∈ Q ∧ ∀ s ∈ (C0 : Set Γ), s * y * s⁻¹ ∈ Q} ∈ 𝓝 (1 : Γ) :=
    (Filter.eventually_of_mem hQn fun y hy => Q.inv_mem hy).and
      (Jacquet.eventually_forall_conj_mem hC0c hQn)
  obtain ⟨n, hn1, hn2⟩ := ((hcontrU C0 hC0c hC0U _ hY1).and
    (hcontrO A0 hA0c hA0O _ hY2)).exists
  -- The shrunken `O`-piece.
  let A : Subgroup Γ := A0.comap (MulAut.conj (g ^ n)).toMonoidHom
  have hAmem : ∀ x, x ∈ A ↔ g ^ n * x * (g ^ n)⁻¹ ∈ A0 := by
    intro x
    simp only [A, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hAA0 : ∀ x ∈ A, x ∈ A0 := by
    intro x hx
    have e : x = (g ^ n)⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * g ^ n := by group
    rw [e]
    exact hA0pow n _ ((hAmem x).1 hx)
  have hAO : ∀ x ∈ A, x ∈ O := fun x hx => hA0O (hAA0 x hx)
  have hAB : ∀ b ∈ B0, ∀ x ∈ A, b * x * b⁻¹ ∈ A := by
    intro b hb x hx
    refine (hAmem _).2 ?_
    have hbn : Commute (g ^ n) b :=
      (Commute.pow_right (hcomm b (Subgroup.mem_inf.mp hb).2) n).symm
    rw [Jacquet.conj_conj_of_commute hbn]
    exact hA0B b hb _ ((hAmem x).1 hx)
  obtain ⟨YA', hYA', hYA'A⟩ : ∃ Y ∈ 𝓝 (1 : Γ), ∀ x ∈ O, x ∈ Y → x ∈ A := by
    have hc : Continuous fun x : Γ => g ^ n * x * (g ^ n)⁻¹ := by fun_prop
    refine ⟨(fun x : Γ => g ^ n * x * (g ^ n)⁻¹) ⁻¹' YA,
      hc.continuousAt.preimage_mem_nhds (by simpa using hYA), fun x hxO hxY => ?_⟩
    exact (hAmem x).2 (hYA0 _ (hOconj _ (hgpow n) x hxO) hxY)
  -- The key commutation `C0 * A ⊆ A * B0 * C0`.
  have hswap : ∀ c ∈ C0, ∀ a ∈ A, ∃ a' ∈ A, ∃ b' ∈ B0, ∃ c' ∈ C0, c * a = a' * b' * c' := by
    intro c hc a ha
    have hã : g ^ n * a * (g ^ n)⁻¹ ∈ A0 := (hAmem a).1 ha
    obtain ⟨hinv, hconj⟩ := hn2 _ hã
    have ea : (g ^ n)⁻¹ * (g ^ n * a * (g ^ n)⁻¹) * g ^ n = a := by group
    rw [ea] at hinv hconj
    have hx : a⁻¹ * (c * a * c⁻¹) ∈ Q := Q.mul_mem hinv (hconj c hc)
    obtain ⟨o1, ho1, m1, hm1, u1, hu1, h1⟩ := hQZ hx
    have hy := hn1 c hc _ (A0.inv_mem hã)
    obtain ⟨o2, ho2, m2, hm2, u2, hu2, h2⟩ := hQZ hy
    have e2 : (g ^ n * a * (g ^ n)⁻¹)⁻¹ * (g ^ n * c * (g ^ n)⁻¹) *
        (g ^ n * a * (g ^ n)⁻¹)⁻¹⁻¹ = g ^ n * (a⁻¹ * (c * a * c⁻¹)) * c * (g ^ n)⁻¹ := by
      group
    rw [e2, h1] at h2
    have e3 : g ^ n * (o1 * m1 * u1) * c * (g ^ n)⁻¹ =
        (g ^ n * o1 * (g ^ n)⁻¹) * (g ^ n * m1 * (g ^ n)⁻¹) *
          (g ^ n * (u1 * c) * (g ^ n)⁻¹) := by
      group
    rw [e3] at h2
    have hu1c : u1 * c ∈ C0 := C0.mul_mem hu1 hc
    obtain ⟨ho, -, -⟩ := hunique _ (hOconj _ (hgpow n) _ (hA0O ho1))
      _ (M.mul_mem (M.mul_mem (hgpow n) (Subgroup.mem_inf.mp hm1).2) (M.inv_mem (hgpow n)))
      _ (hUconj _ (hgpow n) _ (hC0U hu1c))
      _ (hA0O ho2) _ (Subgroup.mem_inf.mp hm2).2 _ (hC0U hu2) h2
    have ho1A : o1 ∈ A := (hAmem o1).2 (ho ▸ ho2)
    refine ⟨a * o1, A.mul_mem ha ho1A, m1, hm1, u1 * c, hu1c, ?_⟩
    calc c * a = a * (a⁻¹ * (c * a * c⁻¹)) * c := by group
      _ = a * (o1 * m1 * u1) * c := by rw [h1]
      _ = a * o1 * m1 * (u1 * c) := by group
  -- The compact open subgroup `A * B0 * C0`.
  let K : Subgroup Γ :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c}
      one_mem' := ⟨1, A.one_mem, 1, B0.one_mem, 1, C0.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, c, hc, rfl⟩ ⟨a', ha', b', hb', c', hc', rfl⟩
        obtain ⟨a'', ha'', b'', hb'', c'', hc'', e⟩ := hswap c hc a' ha'
        refine ⟨a * (b * a'' * b⁻¹), A.mul_mem ha (hAB b hb a'' ha''),
          b * b'' * b', B0.mul_mem (B0.mul_mem hb hb'') hb',
          b'⁻¹ * c'' * b' * c', C0.mul_mem ?_ hc', ?_⟩
        · simpa only [inv_inv] using hC0B b'⁻¹ (B0.inv_mem hb') c'' hc''
        · calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
            _ = a * b * (a'' * b'' * c'') * b' * c' := by rw [e]
            _ = a * (b * a'' * b⁻¹) * (b * b'' * b') * (b'⁻¹ * c'' * b' * c') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
        have ha1 : b⁻¹ * a⁻¹ * b ∈ A := by
          simpa only [inv_inv] using hAB b⁻¹ (B0.inv_mem hb) a⁻¹ (A.inv_mem ha)
        obtain ⟨a'', ha'', b'', hb'', c'', hc'', e⟩ := hswap c⁻¹ (C0.inv_mem hc) _ ha1
        refine ⟨a'', ha'', b'' * b⁻¹, B0.mul_mem hb'' (B0.inv_mem hb),
          b * c'' * b⁻¹, hC0B b hb c'' hc'', ?_⟩
        calc (a * b * c)⁻¹ = c⁻¹ * (b⁻¹ * a⁻¹ * b) * b⁻¹ := by group
          _ = a'' * b'' * c'' * b⁻¹ := by rw [e]
          _ = a'' * (b'' * b⁻¹) * (b * c'' * b⁻¹) := by group }
  have hKmem : ∀ x, x ∈ K ↔ ∃ a ∈ A, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c := fun _ => Iff.rfl
  have hKn : (K : Set Γ) ∈ 𝓝 (1 : Γ) := by
    refine Filter.mem_of_superset (hcell YA' hYA' (V : Set Γ) V.mem_nhds_one YC hYC) ?_
    rintro x ⟨a, ⟨haY, haO⟩, b, ⟨hbV, hbM⟩, c, ⟨hcY, hcU⟩, rfl⟩
    exact ⟨a, hYA'A a haO haY, b, Subgroup.mem_inf.mpr ⟨hbV, hbM⟩, c, hYC0 c hcU hcY, rfl⟩
  let KO : OpenSubgroup Γ := ⟨K, K.isOpen_of_mem_nhds hKn⟩
  have hKOmem : ∀ x, x ∈ KO ↔ x ∈ K := fun _ => Iff.rfl
  have hKV : (KO : Set Γ) ⊆ V := by
    intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 ((hKOmem x).1 hx)
    exact V.mul_mem (V.mul_mem (hA0V (hAA0 a ha)) (Subgroup.mem_inf.mp hb).1) (hC0V hc)
  have hAK : ∀ x ∈ A, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨x, hx, 1, B0.one_mem, 1, C0.one_mem, by simp⟩
  have hBK : ∀ x ∈ B0, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨1, A.one_mem, x, hx, 1, C0.one_mem, by simp⟩
  have hCK : ∀ x ∈ C0, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨1, A.one_mem, 1, B0.one_mem, x, hx, by simp⟩
  have hKU : ∀ x ∈ K, x ∈ U → x ∈ C0 := by
    intro x hx hxU
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 hx
    obtain ⟨-, -, e⟩ := hunique a (hAO a ha) b (Subgroup.mem_inf.mp hb).2 c (hC0U hc)
      1 O.one_mem 1 M.one_mem _ hxU (by simp)
    rw [← e]
    exact hc
  have hKO : ∀ x ∈ K, x ∈ O → x ∈ A := by
    intro x hx hxO
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 hx
    obtain ⟨e, -, -⟩ := hunique a (hAO a ha) b (Subgroup.mem_inf.mp hb).2 c (hC0U hc)
      _ hxO 1 M.one_mem 1 U.one_mem (by simp)
    rw [← e]
    exact ha
  refine ⟨KO, hVc.of_isClosed_subset KO.isClosed hKV, hKV, ?_, ?_, n, ?_⟩
  · intro k hk
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem k).1 ((hKOmem k).1 hk)
    exact ⟨a, hAO a ha, b, (Subgroup.mem_inf.mp hb).2, c, hC0U hc,
      hAK a ha, hBK b hb, hCK c hc, rfl⟩
  · intro x hxU
    constructor
    · intro hx
      exact (mem_stablePiece.1 (hKU x ((hKOmem x).1 hx) hxU)).2
    · intro hx
      exact (hKOmem x).2 (hCK x (mem_stablePiece.2 ⟨hxU, hx⟩))
  · intro x hxO
    have e : ∀ j : ℕ, (g⁻¹ ^ j * g ^ n) * x * (g⁻¹ ^ j * g ^ n)⁻¹ =
        g⁻¹ ^ j * (g ^ n * x * (g ^ n)⁻¹) * (g⁻¹ ^ j)⁻¹ := fun j => by group
    simp_rw [e]
    constructor
    · intro hx
      exact (mem_stablePiece.1 ((hAmem x).1 (hKO x ((hKOmem x).1 hx) hxO))).2
    · intro hx
      exact (hKOmem x).2 (hAK x ((hAmem x).2
        (mem_stablePiece.2 ⟨hOconj _ (hgpow n) x hxO, hx⟩)))

end Generic

namespace CommonLeviSplitting

open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- `Q ∩ U(m)` is the ordered product of its parts in `U(t⁻¹)` and in `U(t)`. -/
def SplitsAlong (Q : OpenSubgroup (RationalPoint F G.X))
    (t m : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop :=
  HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
    (unipotentPoints (Dynamic.inverseCocharacter t) ⊓ unipotentPoints m)
    (unipotentPoints m ⊓ unipotentPoints t) (unipotentPoints m)

variable {t m : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {Q : OpenSubgroup (RationalPoint F G.X)}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- Splitting along `t` is splitting along `t⁻¹`, with the factors exchanged. -/
theorem SplitsAlong.inverse (h : SplitsAlong Q t m) :
    SplitsAlong Q (Dynamic.inverseCocharacter t) m := by
  unfold SplitsAlong at h ⊢
  rw [Dynamic.inverseCocharacter_inverseCocharacter]
  exact h.swap.mono (inf_comm _ _).le (inf_comm _ _).le

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- Splitting of `Q ∩ U(t)` along `m`, in the order of the second ordered chart
of `StandardIntertwining.OppositeCharts` for target `t` and middle `m`. -/
theorem SplitsAlong.second (h : SplitsAlong Q m t) :
    HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (unipotentPoints m ⊓ unipotentPoints t)
      (unipotentPoints (Dynamic.inverseCocharacter m) ⊓ unipotentPoints t)
      (unipotentPoints t) :=
  h.swap.mono (inf_comm _ _).le le_rfl

/-- Under a common Levi, every point of `U(m)` is a product of a point of
`U(t⁻¹) ∩ U(m)` and a point of `U(m) ∩ U(t)`, by the first ordered chart. -/
theorem exists_mul_of_mem
    (hZ : (Dynamic.centralizer t).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer m).carrier (Over.mk (𝟙 _)))
    {x : RationalPoint F G.X} (hx : x ∈ unipotentPoints m) :
    ∃ a ∈ unipotentPoints (Dynamic.inverseCocharacter t) ⊓ unipotentPoints m,
      ∃ b ∈ unipotentPoints m ⊓ unipotentPoints t, x = a * b := by
  obtain ⟨p, hp⟩ := (OppositeCharts.firstChart hZ).surjective ⟨x, hx⟩
  refine ⟨p.1.val.val, ⟨Subgroup.mem_subgroupOf.mp p.1.property, p.1.val.property⟩,
    p.2.val, p.2.property, ?_⟩
  have e : ((OppositeCharts.firstChart hZ p : unipotentPoints m) : RationalPoint F G.X) =
      p.1.val.val * p.2.val := rfl
  rw [← e, hp]

/-- **Splitting from a conjugation cut.** If every point of `V` is `o z w` with
`o ∈ V ∩ U(t⁻¹)`, `z ∈ Z(t)` and `w ∈ V ∩ U(t)` (so `z ∈ V ∩ Z(t)`), and
`Q ∩ U(m)` is cut out of `U(m)` by
`V`-membership of the conjugates by a set of common Levi points, then `Q ∩ U(m)`
splits along `t`. -/
theorem splitsAlong_of_conj_mem {V : OpenSubgroup (RationalPoint F G.X)}
    {C : Set (RationalPoint F G.X)}
    (hZ : (Dynamic.centralizer t).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer m).carrier (Over.mk (𝟙 _)))
    (hV : ∀ v ∈ V, ∃ o ∈ unipotentPoints (Dynamic.inverseCocharacter t),
      ∃ z ∈ (Dynamic.centralizer t).carrier (Over.mk (𝟙 _)), ∃ w ∈ unipotentPoints t,
        o ∈ V ∧ w ∈ V ∧ v = o * z * w)
    (hC : C ⊆ ((Dynamic.centralizer t).carrier (Over.mk (𝟙 _)) : Set (RationalPoint F G.X)))
    (hK : ∀ x ∈ unipotentPoints m, x ∈ Q ↔ ∀ c ∈ C, c * x * c⁻¹ ∈ V) :
    SplitsAlong Q t m :=
  hasCompactOpenProduct_of_conj_mem (V := (V : Set (RationalPoint F G.X))) hV
    (Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique t)
    inf_le_left inf_le_right inf_le_right inf_le_left
    (fun _ hx => exists_mul_of_mem hZ hx)
    (fun c hc x hx => (Subgroup.mem_normalizer_iff.mp
      (Dynamic.centralizer_le_normalizer_unipotent (Dynamic.inverseCocharacter t) _
        (by rw [Dynamic.centralizer_inverseCocharacter]; exact hC hc)) x).mp hx)
    (fun c hc x hx => (Subgroup.mem_normalizer_iff.mp
      (Dynamic.centralizer_le_normalizer_unipotent t _ (hC hc)) x).mp hx)
    hK

/-- **Splitting from an Iwahori factorization.** If `Q` factors as
`(Q ∩ U(t⁻¹)) (Q ∩ Z(t)) (Q ∩ U(t))`, then `Q ∩ U(m)` splits along `t` for every
`m` with the same Levi points. -/
theorem splitsAlong_of_factor
    (hZ : (Dynamic.centralizer t).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer m).carrier (Over.mk (𝟙 _)))
    (hQ : ∀ q ∈ Q, ∃ o ∈ unipotentPoints (Dynamic.inverseCocharacter t),
      ∃ z ∈ (Dynamic.centralizer t).carrier (Over.mk (𝟙 _)), ∃ w ∈ unipotentPoints t,
        o ∈ Q ∧ w ∈ Q ∧ q = o * z * w) :
    SplitsAlong Q t m :=
  splitsAlong_of_conj_mem (V := Q) (C := {1}) hZ hQ
    (by
      rintro c rfl
      exact one_mem _)
    (fun x _ => by simp)

/-- **Common-Levi splitting.** For two cocharacters `χ` and `ψ`, the compact
open subgroup `Q` has the four ordered products `Q ∩ U(ψ^±)` split along `χ` and
`Q ∩ U(χ^±)` split along `ψ`. -/
structure IsCommonLeviSplitting (Q : OpenSubgroup (RationalPoint F G.X))
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop where
  left : SplitsAlong Q χ ψ
  left_inverse : SplitsAlong Q χ (Dynamic.inverseCocharacter ψ)
  right : SplitsAlong Q ψ χ
  right_inverse : SplitsAlong Q ψ (Dynamic.inverseCocharacter χ)

namespace IsCommonLeviSplitting

variable {χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- The two cocharacters may be exchanged. -/
theorem symm (h : IsCommonLeviSplitting Q χ ψ) : IsCommonLeviSplitting Q ψ χ :=
  ⟨h.right, h.right_inverse, h.left, h.left_inverse⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- The first cocharacter may be inverted. -/
theorem inverse_left (h : IsCommonLeviSplitting Q χ ψ) :
    IsCommonLeviSplitting Q (Dynamic.inverseCocharacter χ) ψ := by
  refine ⟨h.left.inverse, h.left_inverse.inverse, h.right_inverse, ?_⟩
  rw [Dynamic.inverseCocharacter_inverseCocharacter]
  exact h.right

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- The second cocharacter may be inverted. -/
theorem inverse_right (h : IsCommonLeviSplitting Q χ ψ) :
    IsCommonLeviSplitting Q χ (Dynamic.inverseCocharacter ψ) :=
  h.symm.inverse_left.symm

end IsCommonLeviSplitting

section Existence

local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance : NonarchimedeanGroup (RationalPoint F G.X) :=
  Aubert.General.RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G

/-- **Iwahori subgroups cut out by a compact open subgroup.** Inside every
compact open subgroup `V` there is a compact open subgroup `K` with
`K = (K ∩ U(χ⁻¹)) (K ∩ Z(χ)) (K ∩ U(χ))`, a point `g` of `Z(χ)` and an exponent
`n` such that `K ∩ U(χ)` consists of the `x ∈ U(χ)` with `g ^ j x g ^ -j ∈ V` for
all `j ≥ 0`, and `K ∩ U(χ⁻¹)` of the `x ∈ U(χ⁻¹)` with
`(g⁻¹ ^ j g ^ n) x (g⁻¹ ^ j g ^ n)⁻¹ ∈ V` for all `j ≥ 0`. -/
theorem exists_iwahoriCut (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (V : OpenSubgroup (RationalPoint F G.X)) (hVc : IsCompact (V : Set (RationalPoint F G.X))) :
    ∃ g ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)),
    ∃ K : OpenSubgroup (RationalPoint F G.X), IsCompact (K : Set (RationalPoint F G.X)) ∧
      (K : Set (RationalPoint F G.X)) ⊆ V ∧
      (∀ k ∈ K, ∃ o ∈ unipotentPoints (Dynamic.inverseCocharacter χ),
        ∃ z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), ∃ w ∈ unipotentPoints χ,
          o ∈ K ∧ w ∈ K ∧ k = o * z * w) ∧
      (∀ x ∈ unipotentPoints χ, x ∈ K ↔ ∀ j : ℕ, g ^ j * x * (g ^ j)⁻¹ ∈ V) ∧
      ∃ n : ℕ, ∀ x ∈ unipotentPoints (Dynamic.inverseCocharacter χ), x ∈ K ↔
        ∀ j : ℕ, (g⁻¹ ^ j * g ^ n) * x * (g⁻¹ ^ j * g ^ n)⁻¹ ∈ V := by
  obtain ⟨g, hgM, hcomm, hcontrU, hcontrO⟩ := exists_central_contractingPoint (F := F) χ
  have hcell : ∀ A ∈ 𝓝 (1 : RationalPoint F G.X), ∀ B ∈ 𝓝 (1 : RationalPoint F G.X),
      ∀ C ∈ 𝓝 (1 : RationalPoint F G.X),
      {x : RationalPoint F G.X |
        ∃ a ∈ A ∩ (unipotentPoints (Dynamic.inverseCocharacter χ) :
          Set (RationalPoint F G.X)),
        ∃ b ∈ B ∩ ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) :
          Set (RationalPoint F G.X)),
        ∃ c ∈ C ∩ (unipotentPoints χ : Set (RationalPoint F G.X)), x = a * b * c} ∈
        𝓝 (1 : RationalPoint F G.X) := by
    have h := Dynamic.opposite_cell_mem_nhds_one F G χ
    rw [← rationalPointTopology_eq_rationalSchemeTopology F G.X] at h
    exact h
  obtain ⟨K, hKc, hKV, hfac, hU, n, hO⟩ := exists_iwahori_stablePieces V hVc
    (isClosed_unipotentPoints _) (isClosed_unipotentPoints χ) hgM hcomm
    (by
      rw [← Dynamic.centralizer_inverseCocharacter χ]
      exact Dynamic.centralizer_le_normalizer_unipotent _ _)
    (Dynamic.centralizer_le_normalizer_unipotent _ _)
    (Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique χ)
    hcell hcontrU hcontrO
  refine ⟨g, hgM, K, hKc, hKV, fun k hk => ?_, hU, n, hO⟩
  obtain ⟨o, ho, z, hz, w, hw, hoK, -, hwK, e⟩ := hfac k hk
  exact ⟨o, ho, z, hz, w, hw, hoK, hwK, e⟩

/-- **Existence of common-Levi splittings.** If `χ` and `ψ` have the same Levi
points, every identity neighborhood contains a compact open subgroup `Q` with a
common-Levi splitting for `χ` and `ψ`. Here `Q` is a `χ`-Iwahori subgroup inside
a `ψ`-Iwahori subgroup `V`, whose radical parts are cut out by `V`. -/
theorem exists_isCommonLeviSplitting {χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hZ : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)))
    {W : Set (RationalPoint F G.X)} (hW : W ∈ 𝓝 (1 : RationalPoint F G.X)) :
    ∃ Q : OpenSubgroup (RationalPoint F G.X), IsCompact (Q : Set (RationalPoint F G.X)) ∧
      (Q : Set (RationalPoint F G.X)) ⊆ W ∧ IsCommonLeviSplitting Q χ ψ := by
  obtain ⟨V₀, hV₀c, hV₀W⟩ := Jacquet.exists_isCompact_openSubgroup_subset hW
  obtain ⟨-, -, V, hVc, hVV₀, hVfac, -, -⟩ := exists_iwahoriCut ψ V₀ hV₀c
  obtain ⟨g, hg, Q, hQc, hQV, hQfac, hQU, n, hQO⟩ := exists_iwahoriCut χ V hVc
  refine ⟨Q, hQc, hQV.trans (hVV₀.trans hV₀W), ?_⟩
  have hZψ : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer (Dynamic.inverseCocharacter ψ)).carrier (Over.mk (𝟙 _)) := by
    rw [Dynamic.centralizer_inverseCocharacter]
    exact hZ
  have hZχ : (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
    rw [Dynamic.centralizer_inverseCocharacter]
    exact hZ.symm
  have hgψ : g ∈ (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) := hZ ▸ hg
  refine ⟨splitsAlong_of_factor hZ hQfac, splitsAlong_of_factor hZψ hQfac,
    splitsAlong_of_conj_mem (V := V) (C := Set.range fun j : ℕ => g ^ j) hZ.symm hVfac
      ?_ ?_,
    splitsAlong_of_conj_mem (V := V) (C := Set.range fun j : ℕ => g⁻¹ ^ j * g ^ n) hZχ hVfac
      ?_ ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact pow_mem hgψ j
  · intro x hx
    rw [hQU x hx, Set.forall_mem_range]
  · rintro _ ⟨j, rfl⟩
    exact mul_mem (pow_mem (inv_mem hgψ) j) (pow_mem hgψ n)
  · intro x hx
    rw [hQO x hx, Set.forall_mem_range]

end Existence

section Integral

open Aubert.General QuotientIntegration Haar OrderedSubgroupFactorization Induction

local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance : SecondCountableTopology F := localField_secondCountableTopology F
local instance : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G

variable {χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  (hZ : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) =
    (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)))
  (hQ : IsCompact (Q : Set (RationalPoint F G.X)))
variable
  [MeasurableSpace (unipotentPoints ψ)] [BorelSpace (unipotentPoints ψ)]
  [MeasurableSpace (unipotentPoints χ)] [BorelSpace (unipotentPoints χ)]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints ψ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints ψ))]
  [MeasurableSpace ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ))]
  [MeasurableSpace (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X))]
  [BorelSpace (unipotentPoints ψ ⊓ unipotentPoints χ : Subgroup (RationalPoint F G.X))]
  [MeasurableSpace (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X))]
  [BorelSpace (unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X))]
  [MeasurableSpace ((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ))]
  [BorelSpace ((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints ψ))]
  [MeasurableSpace (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [BorelSpace (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
    (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [MeasurableSpace (((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)).subgroupOf
      ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [BorelSpace (((unipotentPoints ψ ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ)).subgroupOf
      ((unipotentPoints ψ).subgroupOf (unipotentPoints χ)))]
  [MeasurableSpace ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ))]
  [BorelSpace ((unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ :
    Subgroup (RationalPoint F G.X)).subgroupOf (unipotentPoints χ))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
      (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints (Dynamic.inverseCocharacter χ)).subgroupOf
      (unipotentPoints χ)).subgroupOf ((unipotentPoints ψ).subgroupOf (unipotentPoints χ))))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints ψ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints ψ))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints ψ) (unipotentPoints χ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints ψ) (unipotentPoints χ))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints χ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints (Dynamic.inverseCocharacter χ))
    (unipotentPoints χ))]
  {P₀ P₁ M : Subgroup (RationalPoint F G.X)}
  (h₀ : IsSemidirectDecomposition P₀ M (unipotentPoints (Dynamic.inverseCocharacter χ)))
  (h₁ : IsSemidirectDecomposition P₁ M (unipotentPoints ψ))
  (A : Langlands.SmoothRep.{0, u, uV} ℂ M)

include hZ in
/-- **Standard-integral composition for a common-Levi splitting.** If `Q` has a
common-Levi splitting for `χ` and `ψ`, then at the source quotient measures
normalized by `Q`, an integral from the opposite of `P(χ)` to `P(ψ)` followed by
one from `P(ψ)` to `P(χ)` is the direct integral from the opposite of `P(χ)` to
`P(χ)`. Ordered absolute convergence and both integral witnesses remain inputs. -/
theorem comp_hasIntegral_of_isCommonLeviSplitting (hs : IsCommonLeviSplitting Q χ ψ)
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀
      (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))).obj A}
    {Φ : (DynamicNormalization.leviTwistedInductionFunctor h₁
      (isClosed_unipotentPoints ψ)).obj A}
    {J : RationalPoint F G.X → A}
    (hf : HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints ψ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) ψ) f
      (eval P₁ (leviInflatedInducingRepresentation h₁ (isClosed_unipotentPoints ψ) A) Φ))
    (hΦ : HasIntegral h₁ (isClosed_unipotentPoints ψ) (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ ψ χ) Φ J)
    (ha : OrderedScalarIntegrable h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)) A
      (subgroupCompactOpenHaar Q hQ _ (OppositeCharts.firstComplement_isClosed χ ψ))
      (subgroupCompactOpenHaar Q hQ _ (OppositeCharts.secondComplement_isClosed χ ψ)) f) :
    HasIntegral h₀ (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ))
      (unipotentPoints χ) A
      (DynamicSource.quotientMeasure Q hQ (Dynamic.inverseCocharacter χ) χ) f J :=
  OppositeCharts.comp_hasIntegral_of_hasCompactOpenProduct hZ Q hQ h₀ h₁ A
    hs.left hs.right.second hf hΦ ha

end Integral

end CommonLeviSplitting

end Langlands.Plancherel.StandardIntertwining
