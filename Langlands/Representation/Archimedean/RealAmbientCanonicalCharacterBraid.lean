import Langlands.Representation.Archimedean.RealCanonicalCharacterBraid
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Canonical character braids inside arbitrary ambient blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealAmbientCanonicalCharacterBraid

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealStandardFiltration
  RealCharacterPair RealGenericCompactCharacter RealCanonicalCharacterBraid
  InductionStages RealKTypeCount

/-- Normalized actual slices commute with a Frobenius multiplier in the sliced block. -/
theorem sliceK_frob {n a r p : ℕ} {pre post ds es : List RealBlock}
    {ε : ℤ} {τ : ℂ} {μ : ℤ → ℂ} (h : a + r ≤ n)
    (ha : realRank pre = a) (hd : realRank ds = r) (he : realRank es = r)
    (hlocal : IsBlockFrobData r ds es p ε τ μ)
    (hglobal : IsBlockFrobData n (pre ++ ds ++ post) (pre ++ es ++ post) (a + p) ε τ μ)
    (κ : unitaryCompact ℝ n) (F : KF n (pre ++ ds ++ post)) :
    sliceK h ha he κ (blockFrobMap hglobal F) =
      blockFrobMap hlocal (sliceK h ha hd κ F) := by
  apply eq_of_blockFourierCoefficient_eq hlocal.lt
  intro j g hg
  change blockFourierCoefficient r p j
    (slice h (κ : Langlands.GeneralLinear n ℝ) (blockFrobMap hglobal F)) g = _
  rw [blockFourierCoefficient_slice h hlocal.lt j,
    sliceFactor_of_mem_unitaryCompact hg, one_mul,
    blockFourierCoefficient_blockFrobMap hglobal F
      ((unitaryCompact ℝ n).mul_mem (blockEmb_mem_unitaryCompact h hg) κ.2),
    blockFourierCoefficient_blockFrobMap hlocal (sliceK h ha hd κ F) hg]
  change μ j * blockFourierCoefficient n (a + p) j F (blockEmb h g * κ) =
    μ j * blockFourierCoefficient r p j (slice h (κ : Langlands.GeneralLinear n ℝ) F) g
  rw [blockFourierCoefficient_slice h hlocal.lt j, sliceFactor_of_mem_unitaryCompact hg,
    one_mul]

def ambient (pre post : List RealBlock) (a b c : RealCharacterData) : List RealBlock :=
  pre ++ source a b c ++ post

theorem ambient_rank {n : ℕ} {pre post : List RealBlock} {a b c : RealCharacterData}
    (hn : realRank (ambient pre post a b c) = n) (x y z : RealCharacterData) :
    realRank (ambient pre post x y z) = n := by
  simpa only [ambient, source, realRank, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] using hn

theorem triple_le {n : ℕ} {pre post : List RealBlock} {a b c : RealCharacterData}
    (hn : realRank (ambient pre post a b c) = n) : realRank pre + 3 ≤ n := by
  simp only [ambient, source, realRank, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hn ⊢
  omega

section Adjacent

variable {n : ℕ} {pre post : List RealBlock} {a b c : RealCharacterData}

theorem data0 (hn : realRank (ambient pre post a b c) = n)
    (A : Choice (pairParity a b)) :
    IsBlockFrobData n (ambient pre post a b c) (ambient pre post b a c)
      (realRank pre + 0) (pairParity a b) ((-1 : ℂ) ^ (pairParity a b).natAbs) A.multiplier := by
  have hn' : realRank (pre ++ .character a :: .character b :: .character c :: post) = n := by
    simpa only [ambient, source, List.append_assoc, List.cons_append, List.nil_append] using hn
  have hh := RealCanonicalCharacterBraid.data (n := n) (pre := pre)
    (post := .character c :: post) hn' A
  simpa only [ambient, source, List.append_assoc, List.cons_append, List.nil_append, Nat.add_zero] using hh

theorem data1 (hn : realRank (ambient pre post a b c) = n)
    (B : Choice (pairParity b c)) :
    IsBlockFrobData n (ambient pre post a b c) (ambient pre post a c b)
      (realRank pre + 1) (pairParity b c) ((-1 : ℂ) ^ (pairParity b c).natAbs) B.multiplier := by
  have hn' : realRank ((pre ++ [.character a]) ++ .character b :: .character c :: post) = n := by
    simpa only [ambient, source, List.append_assoc, List.cons_append, List.nil_append] using hn
  have hh := RealCanonicalCharacterBraid.data (n := n) (pre := pre ++ [.character a])
    (post := post) hn' B
  simpa only [ambient, source, List.append_assoc, List.cons_append, List.nil_append,
    realRank_append', realRank, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    RealBlock.rank, Nat.add_zero] using hh

def swap0 (hn : realRank (ambient pre post a b c) = n) (A : Choice (pairParity a b)) :
    KF n (ambient pre post a b c) →ₗ[ℂ] KF n (ambient pre post b a c) :=
  blockFrobMap (data0 hn A)

def swap1 (hn : realRank (ambient pre post a b c) = n) (B : Choice (pairParity b c)) :
    KF n (ambient pre post a b c) →ₗ[ℂ] KF n (ambient pre post a c b) :=
  blockFrobMap (data1 hn B)

def sliceTriple (h : realRank pre + 3 ≤ n) (κ : unitaryCompact ℝ n) :
    KF n (ambient pre post a b c) →ₗ[ℂ] KF 3 (source a b c) :=
  sliceK h rfl rfl κ

theorem slice_swap0 (hn : realRank (ambient pre post a b c) = n)
    (A : Choice (pairParity a b)) (h : realRank pre + 3 ≤ n)
    (κ : unitaryCompact ℝ n) (F : KF n (ambient pre post a b c)) :
    sliceTriple h κ (swap0 hn A F) =
      RealCanonicalCharacterBraid.swap0 a b c A (sliceTriple h κ F) :=
  sliceK_frob h rfl rfl rfl
    (RealCanonicalCharacterBraid.data (n := 3) (pre := []) (post := [.character c])
      (a := a) (b := b) rfl A) (data0 hn A) κ F

theorem slice_swap1 (hn : realRank (ambient pre post a b c) = n)
    (B : Choice (pairParity b c)) (h : realRank pre + 3 ≤ n)
    (κ : unitaryCompact ℝ n) (F : KF n (ambient pre post a b c)) :
    sliceTriple h κ (swap1 hn B F) =
      RealCanonicalCharacterBraid.swap1 a b c B (sliceTriple h κ F) :=
  sliceK_frob h rfl rfl rfl
    (RealCanonicalCharacterBraid.data (n := 3) (pre := [.character a]) (post := [])
      (a := b) (b := c) rfl B) (data1 hn B) κ F

end Adjacent

section Words

variable {n : ℕ} {pre post : List RealBlock} {a b c : RealCharacterData}

def leftWord (hn : realRank (ambient pre post a b c) = n) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    KF n (ambient pre post a b c) →ₗ[ℂ] KF n (ambient pre post c b a) :=
  ((swap0 (ambient_rank hn b c a) B).comp (swap1 (ambient_rank hn b a c) C)).comp (swap0 hn A)

def rightWord (hn : realRank (ambient pre post a b c) = n) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    KF n (ambient pre post a b c) →ₗ[ℂ] KF n (ambient pre post c b a) :=
  ((swap1 (ambient_rank hn c a b) A).comp (swap0 (ambient_rank hn a c b) C)).comp (swap1 hn B)

theorem slice_leftWord (hn : realRank (ambient pre post a b c) = n)
    (A : Choice (pairParity a b)) (B : Choice (pairParity b c)) (C : Choice (pairParity a c))
    (h : realRank pre + 3 ≤ n) (κ : unitaryCompact ℝ n) (F : KF n (ambient pre post a b c)) :
    sliceTriple h κ (leftWord hn A B C F) =
      RealCanonicalCharacterBraid.leftWord a b c A B C (sliceTriple h κ F) := by
  simp only [leftWord, LinearMap.comp_apply]
  rw [slice_swap0, slice_swap1, slice_swap0]
  rfl

theorem slice_rightWord (hn : realRank (ambient pre post a b c) = n)
    (A : Choice (pairParity a b)) (B : Choice (pairParity b c)) (C : Choice (pairParity a c))
    (h : realRank pre + 3 ≤ n) (κ : unitaryCompact ℝ n) (F : KF n (ambient pre post a b c)) :
    sliceTriple h κ (rightWord hn A B C F) =
      RealCanonicalCharacterBraid.rightWord a b c A B C (sliceTriple h κ F) := by
  simp only [rightWord, LinearMap.comp_apply]
  rw [slice_swap1, slice_swap0, slice_swap1]
  rfl

theorem braid_of_polynomial
    (hPoly : ∀ N n m, RealGenericCharacterBraidReduction.PolynomialBraid N n m)
    (hn : realRank (ambient pre post a b c) = n) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c))
    (hparam : C.parameter = A.parameter + B.parameter) :
    leftWord hn A B C = rightWord hn A B C := by
  have hlocal := RealCanonicalCharacterBraid.braid_of_polynomial hPoly a b c A B C hparam
  apply LinearMap.ext
  intro F
  apply restrict_injective (realStandardModule_le_principalSeries _ _)
  funext x
  change (leftWord hn A B C F : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits x) =
    (rightWord hn A B C F : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits x)
  let κ : unitaryCompact ℝ n := ⟨Unitary.toUnits x, x.2⟩
  have hh := (slice_leftWord hn A B C (triple_le hn) κ F).trans
    ((LinearMap.congr_fun hlocal (sliceTriple (triple_le hn) κ F)).trans
      (slice_rightWord hn A B C (triple_le hn) κ F).symm)
  have he := congrFun (congrArg Subtype.val hh) 1
  change slice (triple_le hn) (Unitary.toUnits x) (leftWord hn A B C F) 1 =
    slice (triple_le hn) (Unitary.toUnits x) (rightWord hn A B C F) 1 at he
  simpa only [slice_apply, sliceFactor_one, map_one, one_mul] using he

end Words

section FourierInterface

open RealBlockFourierFinite

theorem fourier_eqOn {n p : ℕ} {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hfg : Set.EqOn f g (unitaryCompact ℝ n)) (j : ℤ)
    {x : Langlands.GeneralLinear n ℝ} (hx : x ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p j f x = blockFourierCoefficient n p j g x := by
  unfold blockFourierCoefficient
  apply intervalIntegral.integral_congr
  intro θ _
  change f (blockRotation n p θ * x) * _ = g (blockRotation n p θ * x) * _
  rw [hfg ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hx)]

theorem eqOn_of_fourier {n p : ℕ} (hp : p + 1 < n)
    {f g : Langlands.GeneralLinear n ℝ → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (heq : ∀ j, ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j f x = blockFourierCoefficient n p j g x) :
    Set.EqOn f g (unitaryCompact ℝ n) := by
  intro x hx
  rw [eq_finsum_blockFourierCoefficient hp hfc hfK hx,
    eq_finsum_blockFourierCoefficient hp hgc hgK hx]
  congr 2
  funext j
  exact heq j x hx

def FourierStep {n : ℕ} (p : ℕ) (μ : ℤ → ℂ)
    (f g : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
  ∀ j, ∀ x ∈ unitaryCompact ℝ n,
    blockFourierCoefficient n p j g x = μ j * blockFourierCoefficient n p j f x

theorem step_eqOn {n p : ℕ} {ds es : List RealBlock} {ε : ℤ} {τ : ℂ} {μ : ℤ → ℂ}
    (hdata : IsBlockFrobData n ds es p ε τ μ) (f : KF n ds)
    (u g : Langlands.GeneralLinear n ℝ → ℂ)
    (hgc : Continuous g)
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hu : Set.EqOn u f (unitaryCompact ℝ n)) (hstep : FourierStep p μ u g) :
    Set.EqOn g (blockFrobMap hdata f) (unitaryCompact ℝ n) :=
  eqOn_of_fourier hdata.lt hgc (RealBlockJacquet.continuous_coe _) hgK (blockFrobMap hdata f).2.2
    (fun j x hx => by
      rw [hstep j x hx, fourier_eqOn hu j hx,
        blockFourierCoefficient_blockFrobMap hdata f hx])

/-- Only the starting function needs to be in the indicated ambient character module. -/
theorem functional_braid {n : ℕ} {pre post : List RealBlock} {a b c : RealCharacterData}
    (hPoly : ∀ N n m, RealGenericCharacterBraidReduction.PolynomialBraid N n m)
    (hn : realRank (ambient pre post a b c) = n)
    (A : Choice (pairParity a b)) (B : Choice (pairParity b c)) (C : Choice (pairParity a c))
    (hparam : C.parameter = A.parameter + B.parameter)
    (fs : Fin 7 → Langlands.GeneralLinear n ℝ → ℂ)
    (hsource : fs 0 ∈ KF n (ambient pre post a b c))
    (hc : ∀ i, Continuous (fs i))
    (hK : ∀ i, fs i ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)) (unitaryCompact ℝ n))
    (h01 : FourierStep (realRank pre + 0) A.multiplier (fs 0) (fs 1))
    (h12 : FourierStep (realRank pre + 1) C.multiplier (fs 1) (fs 2))
    (h23 : FourierStep (realRank pre + 0) B.multiplier (fs 2) (fs 3))
    (h04 : FourierStep (realRank pre + 1) B.multiplier (fs 0) (fs 4))
    (h45 : FourierStep (realRank pre + 0) C.multiplier (fs 4) (fs 5))
    (h56 : FourierStep (realRank pre + 1) A.multiplier (fs 5) (fs 6)) :
    Set.EqOn (fs 3) (fs 6) (unitaryCompact ℝ n) := by
  let f : KF n (ambient pre post a b c) := ⟨fs 0, hsource⟩
  let f1 := swap0 hn A f
  let f2 := swap1 (ambient_rank hn b a c) C f1
  let f3 := swap0 (ambient_rank hn b c a) B f2
  let g1 := swap1 hn B f
  let g2 := swap0 (ambient_rank hn a c b) C g1
  let g3 := swap1 (ambient_rank hn c a b) A g2
  have h1 : Set.EqOn (fs 1) f1 (unitaryCompact ℝ n) :=
    step_eqOn (data0 hn A) f (fs 0) (fs 1) (hc 1) (hK 1) (fun _ _ => rfl) h01
  have h2 : Set.EqOn (fs 2) f2 (unitaryCompact ℝ n) :=
    step_eqOn (data1 (ambient_rank hn b a c) C) f1 (fs 1) (fs 2) (hc 2) (hK 2) h1 h12
  have h3 : Set.EqOn (fs 3) f3 (unitaryCompact ℝ n) :=
    step_eqOn (data0 (ambient_rank hn b c a) B) f2 (fs 2) (fs 3) (hc 3) (hK 3) h2 h23
  have h4 : Set.EqOn (fs 4) g1 (unitaryCompact ℝ n) :=
    step_eqOn (data1 hn B) f (fs 0) (fs 4) (hc 4) (hK 4) (fun _ _ => rfl) h04
  have h5 : Set.EqOn (fs 5) g2 (unitaryCompact ℝ n) :=
    step_eqOn (data0 (ambient_rank hn a c b) C) g1 (fs 4) (fs 5) (hc 5) (hK 5) h4 h45
  have h6 : Set.EqOn (fs 6) g3 (unitaryCompact ℝ n) :=
    step_eqOn (data1 (ambient_rank hn c a b) A) g2 (fs 5) (fs 6) (hc 6) (hK 6) h5 h56
  have heq : f3 = g3 := LinearMap.congr_fun (braid_of_polynomial hPoly hn A B C hparam) f
  intro x hx
  rw [h3 hx, h6 hx, heq]

end FourierInterface

end Langlands.Archimedean.RealAmbientCanonicalCharacterBraid

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealCharacterPair RealCanonicalCharacterBraid
  RealAmbientCanonicalCharacterBraid

/-- The conditional canonical mixed braid in every surrounding standard module. -/
def RealAmbientCanonicalCharacterBraidStatement : Prop :=
  (∀ N n m, RealGenericCharacterBraidReduction.PolynomialBraid N n m) →
    ∀ (n : ℕ) (pre post : List RealBlock) (a b c : RealCharacterData)
      (hn : realRank (ambient pre post a b c) = n)
      (A : Choice (pairParity a b)) (B : Choice (pairParity b c)) (C : Choice (pairParity a c)),
      C.parameter = A.parameter + B.parameter →
        leftWord hn A B C = rightWord hn A B C

theorem realAmbientCanonicalCharacterBraid : RealAmbientCanonicalCharacterBraidStatement :=
  fun hPoly _ _ _ _ _ _ hn A B C hparam => braid_of_polynomial hPoly hn A B C hparam

end Langlands.Archimedean
