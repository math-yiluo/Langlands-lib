import Langlands.Representation.Hecke.NormalQuotientPseudo
import Langlands.Representation.Hecke.NormalQuotientStatements
import Langlands.Representation.Hecke.CompactTensorFiniteCosets

/-! # Normal-quotient coinvariants as the Hecke tensor induction

Renard III.2.10, (III.2.10.2), printed pp.80–82 / PDF pp.86–88.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uP v w

variable {P : Type uP} [Group P] [TopologicalSpace P] [T2Space P]
  [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  (N : Subgroup P) [N.Normal] [IsClosed (N : Set P)]
  [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)]
  (μP : Measure P) [μP.IsHaarMeasure]
  (μM : Measure (P ⧸ N)) [μM.IsHaarMeasure]
  (W : SmoothRep.{0, uP, w} ℂ P)

/-- The coinvariant projection intertwines `W` with the pulled-back quotient action. -/
def coinvariantIntertwiner :
    W.representation.IntertwiningMap
      ((normalQuotientAction N W.representation).comp (QuotientGroup.mk' N)) where
  toLinearMap := Jacquet.mk W.representation N
  isIntertwining' _ := LinearMap.ext fun _ => rfl

omit [T2Space P] [LocallyCompactSpace P] [IsClosed (N : Set P)] [MeasurableSpace (P ⧸ N)]
  [BorelSpace (P ⧸ N)] in
/-- The coinvariant projection carries the `H(P)`-action of `W` to the
pulled-back action on the coinvariants. -/
theorem heckeAction_coinvariant (a : HeckeAlgebra μP) (v : W) :
    heckeAction μP ((normalQuotientAction N W.representation).comp (QuotientGroup.mk' N))
        (isSmooth_comp _ (continuous_quotientMk' N)
          (isSmooth_normalQuotientAction N W.representation W.isSmooth)) a
        (Jacquet.mk W.representation N v) =
      Jacquet.mk W.representation N (heckeAction μP W.representation W.isSmooth a v) :=
  (integratedAction_intertwiner μP W.isSmooth _ (coinvariantIntertwiner N W)
    (HeckeAlgebra.toTestFunction μP a) v).symm

/-- The balance `(T·a)·[v] = T·[a·v]` on the coinvariants. -/
theorem heckeAction_rightModule_coinvariant (a : HeckeAlgebra μP) (T : HeckeAlgebra μM)
    (v : W) :
    heckeAction μM (normalQuotientAction N W.representation)
        (isSmooth_normalQuotientAction N W.representation W.isSmooth)
        (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
         op a • T) (Jacquet.mk W.representation N v) =
      heckeAction μM (normalQuotientAction N W.representation)
        (isSmooth_normalQuotientAction N W.representation W.isSmooth) T
        (Jacquet.mk W.representation N (heckeAction μP W.representation W.isSmooth a v)) := by
  have h := heckeAction_rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    (normalQuotientAction N W.representation)
    (isSmooth_normalQuotientAction N W.representation W.isSmooth) a T
    (Jacquet.mk W.representation N v)
  rw [heckeAction_coinvariant] at h
  exact h

omit [T2Space P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  [IsClosed (N : Set P)] [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)] in
/-- Every `K`-fixed vector has a `q(K)`-fixed coinvariant class. -/
theorem coinvariant_mem_fixedVectors (K : OpenSubgroup P) {v : W}
    (hv : v ∈ fixedVectors W.representation K.toSubgroup) :
    Jacquet.mk W.representation N v ∈
      fixedVectors (normalQuotientAction N W.representation)
        (quotientOpenSubgroup N K).toSubgroup := by
  apply Representation.mem_invariants _ _ |>.mpr
  rintro ⟨m, hm⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  change Jacquet.mk W.representation N (W.representation k v) = Jacquet.mk W.representation N v
  have hkv : W.representation k v = v := (Representation.mem_invariants _ _).mp hv ⟨k, hk⟩
  rw [hkv]

omit [T2Space P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  [IsClosed (N : Set P)] in
/-- The normalized indicator of `q(K)` fixes the class of a `K`-fixed vector. -/
theorem heckeAction_coinvariant_of_fixed (K : OpenSubgroup P) (hK : IsCompact (K : Set P))
    {v : W} (hv : v ∈ fixedVectors W.representation K.toSubgroup) :
    heckeAction μM (normalQuotientAction N W.representation)
        (isSmooth_normalQuotientAction N W.representation W.isSmooth)
        (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
          (isCompact_quotientOpenSubgroup N K hK)) (Jacquet.mk W.representation N v) =
      Jacquet.mk W.representation N v :=
  heckeAction_normalizedIndicator_of_fixed μM _ _ _ _ (coinvariant_mem_fixedVectors N W K hv)

/-- The integrated quotient action on the actual coinvariants. -/
abbrev coinvariantAction :
    HeckeAlgebra μM →ₙₐ[ℂ] Module.End ℂ (Jacquet.Coinvariants W.representation N) :=
  heckeAction μM (normalQuotientAction N W.representation)
    (isSmooth_normalQuotientAction N W.representation W.isSmooth)

/-- The pairing `(T, v) ↦ T·[v]`. -/
def coinvariantPairing : HeckeAlgebra μM →+ W →+ Jacquet.Coinvariants W.representation N where
  toFun T :=
    { toFun := fun v => coinvariantAction N μM W T (Jacquet.mk W.representation N v)
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun v v' => by rw [map_add, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro v
    show coinvariantAction N μM W 0 (Jacquet.mk W.representation N v) = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' T T' := by
    apply AddMonoidHom.ext
    intro v
    show coinvariantAction N μM W (T + T') (Jacquet.mk W.representation N v) =
      coinvariantAction N μM W T (Jacquet.mk W.representation N v) +
        coinvariantAction N μM W T' (Jacquet.mk W.representation N v)
    rw [map_add, LinearMap.add_apply]

/-- The comparison map `H(M) ⊗_{H(P)} W → W_N`, `T ⊗ v ↦ T·[v]`. -/
def tensorToCoinvariants :
    letI := NonUnitalModule.regular (HeckeAlgebra μM)
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    letI := NonUnitalBimoduleTensor.leftModule
      (regular_commutes_right μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)) W
    letI := heckeNonUnitalModule μM (normalQuotientAction N W.representation)
      (isSmooth_normalQuotientAction N W.representation W.isSmooth)
    NonUnitalModuleHom (HeckeAlgebra μM)
      (NonUnitalModuleTensor.Tensor (HeckeAlgebra μP) (HeckeAlgebra μM) W)
      (Jacquet.Coinvariants W.representation N) :=
  letI := NonUnitalModule.regular (HeckeAlgebra μM)
  letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  letI := heckeNonUnitalModule μP W.representation W.isSmooth
  letI := heckeNonUnitalModule μM (normalQuotientAction N W.representation)
    (isSmooth_normalQuotientAction N W.representation W.isSmooth)
  NonUnitalBimoduleTensor.leftLift
    (regular_commutes_right μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N))
    (coinvariantPairing N μM W)
    (fun a T v => heckeAction_rightModule_coinvariant N μP μM W a T v)
    (fun c T v => by
      show coinvariantAction N μM W (c * T) (Jacquet.mk W.representation N v) =
        coinvariantAction N μM W c (coinvariantAction N μM W T (Jacquet.mk W.representation N v))
      rw [map_mul, Module.End.mul_apply])

theorem tensorToCoinvariants_tmul (T : HeckeAlgebra μM) (v : W) :
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    tensorToCoinvariants N μP μM W
        (NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T v) =
      coinvariantAction N μM W T (Jacquet.mk W.representation N v) := rfl

/-- The forward formula: `T ⊗ v ↦ [v]` when `T` is the normalized indicator of
`q(K)` and `v` is `K`-fixed. -/
theorem tensorToCoinvariants_normalizedIndicator (K : OpenSubgroup P) (hK : IsCompact (K : Set P))
    {v : W} (hv : v ∈ fixedVectors W.representation K.toSubgroup) :
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    tensorToCoinvariants N μP μM W
        (NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W
          (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
            (isCompact_quotientOpenSubgroup N K hK)) v) =
      Jacquet.mk W.representation N v :=
  heckeAction_coinvariant_of_fixed N μM W K hK hv

omit [MeasurableSpace P] [BorelSpace P] [IsClosed (N : Set P)] [MeasurableSpace (P ⧸ N)]
  [BorelSpace (P ⧸ N)] in
/-- Every smooth vector is fixed by a compact open subgroup. -/
theorem exists_compact_fixed (v : W) :
    ∃ (K : OpenSubgroup P) (_ : IsCompact (K : Set P)),
      v ∈ fixedVectors W.representation K.toSubgroup := by
  obtain ⟨U, hU⟩ := W.isSmooth v
  obtain ⟨K, hKU, hK, _⟩ := TestFunction.commonCompactOpenBiInvariance P ∅ U
  exact ⟨K, hK, fun k => hU ⟨k, hKU k.property⟩⟩

/-- A right coset indicator is a scalar multiple of a right translate of the
normalized indicator. -/
theorem rightCosetIndicator_eq_smul (KM : OpenSubgroup (P ⧸ N))
    (hKM : IsCompact (KM : Set (P ⧸ N))) (p : P) :
    HeckeAlgebra.rightCosetIndicator μM KM hKM (QuotientGroup.mk' N p) =
      ((haarScale (QuotientGroup.mk' N p))⁻¹ * (μM.real (KM : Set (P ⧸ N)) : ℂ)) •
        rightRepresentation μM (QuotientGroup.mk' N) p⁻¹
          (HeckeAlgebra.normalizedIndicator μM KM hKM) := by
  set g := QuotientGroup.mk' N p
  have hs : haarScale g ≠ 0 := by
    intro h
    have h1 := haarScale_mul_inverse g
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hm := HeckeAlgebra.compactOpen_complex_mass_ne_zero μM KM hKM
  have hinv : QuotientGroup.mk' N p⁻¹ = g⁻¹ := map_inv _ _
  apply HeckeAlgebra.ext
  intro x
  rw [HeckeAlgebra.rightCosetIndicator_apply]
  change _ = ((haarScale g)⁻¹ * (μM.real (KM : Set (P ⧸ N)) : ℂ)) *
    rightRepresentation μM (QuotientGroup.mk' N) p⁻¹
      (HeckeAlgebra.normalizedIndicator μM KM hKM) x
  rw [rightRepresentation_apply, HeckeAlgebra.normalizedIndicator_apply, hinv, inv_inv]
  calc
    (KM : Set (P ⧸ N)).indicator (fun _ => (1 : ℂ)) (x * g⁻¹) =
        ((haarScale g)⁻¹ * haarScale g) *
          ((μM.real (KM : Set (P ⧸ N)) : ℂ) * (μM.real (KM : Set (P ⧸ N)) : ℂ)⁻¹) *
          (KM : Set (P ⧸ N)).indicator (fun _ => (1 : ℂ)) (x * g⁻¹) := by
      rw [inv_mul_cancel₀ hs, mul_inv_cancel₀ hm, one_mul, one_mul]
    _ = _ := by ring

/-- A coset indicator tensor is a tensor of the normalized indicator. -/
theorem tmul_rightCosetIndicator (KM : OpenSubgroup (P ⧸ N))
    (hKM : IsCompact (KM : Set (P ⧸ N))) (p : P) (v : W) :
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W
        (HeckeAlgebra.rightCosetIndicator μM KM hKM (QuotientGroup.mk' N p)) v =
      NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W
        (HeckeAlgebra.normalizedIndicator μM KM hKM)
        (W.representation p (((haarScale (QuotientGroup.mk' N p))⁻¹ *
          (μM.real (KM : Set (P ⧸ N)) : ℂ)) • v)) := by
  rw [rightCosetIndicator_eq_smul,
    tensor_scalar_balanced μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      W.representation W.isSmooth,
    tensor_group_balanced μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      W.representation W.isSmooth]

/-- Normal form: every tensor is `eKM ⊗ u` with `KM = q(K)` for a compact open `K`. -/
theorem tensor_eq_tmul_normalizedIndicator
    (t : letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      letI := heckeNonUnitalModule μP W.representation W.isSmooth
      NonUnitalModuleTensor.Tensor (HeckeAlgebra μP) (HeckeAlgebra μM) W) :
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    ∃ (K : OpenSubgroup P) (hK : IsCompact (K : Set P)) (u : W),
      t = NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W
        (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
          (isCompact_quotientOpenSubgroup N K hK)) u := by
  classical
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  let _ := heckeNonUnitalModule μP W.representation W.isSmooth
  obtain ⟨z, rfl⟩ := NonUnitalModuleTensor.projection_surjective
    (HeckeAlgebra μP) (HeckeAlgebra μM) W t
  obtain ⟨n, T, v, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  obtain ⟨KM, _, _, hfix⟩ := TestFunction.commonCompactOpenBiInvariance (P ⧸ N)
    (Finset.univ.image (fun i : Fin n => HeckeAlgebra.toTestFunction μM (T i))) ⊤
  obtain ⟨K, hKU, hK, _⟩ := TestFunction.commonCompactOpenBiInvariance P ∅
    (OpenSubgroup.comap (QuotientGroup.mk' N) (continuous_quotientMk' N) KM)
  have hKM := isCompact_quotientOpenSubgroup N K hK
  have hT (i : Fin n) : ∀ k : quotientOpenSubgroup N K, ∀ x,
      T i ((k : P ⧸ N) * x) = T i x := by
    rintro ⟨m, hm⟩ x
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
    exact (hfix (HeckeAlgebra.toTestFunction μM (T i))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).1
      ⟨QuotientGroup.mk' N k, hKU hk⟩ x
  choose s hs using fun i =>
    finite_leftCoset_expansion μM (quotientOpenSubgroup N K) hKM (T i) (hT i)
  let σ := Function.surjInv (QuotientGroup.mk'_surjective N)
  have hσ (m : P ⧸ N) : QuotientGroup.mk' N (σ m) = m :=
    Function.surjInv_eq (QuotientGroup.mk'_surjective N) m
  let eM := HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K) hKM
  let u (i : Fin n) (r : Induction.LeftQuotient (quotientOpenSubgroup N K).toSubgroup) : W :=
    W.representation (σ r.out) (((haarScale (QuotientGroup.mk' N (σ r.out)))⁻¹ *
      (μM.real ((quotientOpenSubgroup N K : OpenSubgroup (P ⧸ N)) : Set (P ⧸ N)) : ℂ)) •
        (T i r.out • v i))
  have key (i : Fin n) :
      NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W (T i) (v i) =
        ∑ r ∈ s i, NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W eM (u i r) := by
    let b : HeckeAlgebra μM →+
        NonUnitalModuleTensor.Tensor (HeckeAlgebra μP) (HeckeAlgebra μM) W :=
      { toFun := fun a => NonUnitalModuleTensor.tmul
          (HeckeAlgebra μP) (HeckeAlgebra μM) W a (v i)
        map_zero' := NonUnitalModuleTensor.zero_tmul _ _ _ _
        map_add' := fun a a' => NonUnitalModuleTensor.add_tmul _ _ _ a a' (v i) }
    calc
      NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W (T i) (v i) =
          b (∑ r ∈ s i, T i r.out •
            HeckeAlgebra.rightCosetIndicator μM (quotientOpenSubgroup N K) hKM r.out) :=
        congrArg b (hs i)
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro r _
        have h1 : HeckeAlgebra.rightCosetIndicator μM (quotientOpenSubgroup N K) hKM r.out =
            HeckeAlgebra.rightCosetIndicator μM (quotientOpenSubgroup N K) hKM
              (QuotientGroup.mk' N (σ r.out)) := by rw [hσ]
        change NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W
          (T i r.out • HeckeAlgebra.rightCosetIndicator μM (quotientOpenSubgroup N K) hKM r.out)
          (v i) = _
        rw [tensor_scalar_balanced μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
          W.representation W.isSmooth, h1, tmul_rightCosetIndicator]
  let L := NonUnitalModuleTensor.biadditive (HeckeAlgebra μP) (HeckeAlgebra μM) W eM
  refine ⟨K, hK, ∑ i, ∑ r ∈ s i, u i r, ?_⟩
  calc
    NonUnitalModuleTensor.projection (HeckeAlgebra μP) (HeckeAlgebra μM) W z =
        ∑ i, NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W (T i) (v i) :=
      (congrArg _ hz).trans (map_sum _ _ _)
    _ = ∑ i, ∑ r ∈ s i, L (u i r) := Finset.sum_congr rfl fun i _ => key i
    _ = L (∑ i, ∑ r ∈ s i, u i r) := by simp only [map_sum]

/-- Right translation by an element of `N` is trivial on `H(P ⧸ N)`. -/
theorem rightRepresentation_of_mem {n : P} (hn : n ∈ N) (T : HeckeAlgebra μM) :
    rightRepresentation μM (QuotientGroup.mk' N) n T = T := by
  have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  apply HeckeAlgebra.ext
  intro x
  rw [rightRepresentation_apply, h1, inv_one, map_one, mul_one, one_mul]

/-- Every tensor against a coinvariant relation vanishes. -/
theorem tmul_relations {x : W} (hx : x ∈ Jacquet.relations W.representation N) :
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    ∀ T : HeckeAlgebra μM,
      NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T x = 0 := by
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  let _ := heckeNonUnitalModule μP W.representation W.isSmooth
  rw [Jacquet.relations_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨n, v⟩, rfl⟩ := hy
    intro T
    have hsub := map_sub (NonUnitalModuleTensor.biadditive (HeckeAlgebra μP)
      (HeckeAlgebra μM) W T) (W.representation (n : P) v) v
    change NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T
      (W.representation (n : P) v - v) =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T
          (W.representation (n : P) v) -
        NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T v at hsub
    rw [hsub, ← tensor_group_balanced μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      W.representation W.isSmooth, rightRepresentation_of_mem N μM (N.inv_mem n.property),
      sub_self]
  | zero =>
    intro T
    exact NonUnitalModuleTensor.tmul_zero _ _ _ T
  | add y z _ _ hy hz =>
    intro T
    rw [NonUnitalModuleTensor.tmul_add, hy T, hz T, add_zero]
  | smul c y _ hy =>
    intro T
    rw [← tensor_scalar_balanced μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      W.representation W.isSmooth, hy]

/-- The comparison map is bijective. -/
theorem tensorToCoinvariants_bijective :
    letI := NonUnitalModule.regular (HeckeAlgebra μM)
    letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    letI := heckeNonUnitalModule μP W.representation W.isSmooth
    letI := NonUnitalBimoduleTensor.leftModule
      (regular_commutes_right μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)) W
    letI := heckeNonUnitalModule μM (normalQuotientAction N W.representation)
      (isSmooth_normalQuotientAction N W.representation W.isSmooth)
    Function.Bijective (tensorToCoinvariants N μP μM W).toAddMonoidHom := by
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  let _ := heckeNonUnitalModule μP W.representation W.isSmooth
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro t ht
    obtain ⟨K, hK, u, rfl⟩ := tensor_eq_tmul_normalizedIndicator N μP μM W t
    set eM := HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
      (isCompact_quotientOpenSubgroup N K hK)
    set eP := HeckeAlgebra.normalizedIndicator μP K hK
    have h1 : NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W eM u =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W eM (eP • u) := by
      rw [← NonUnitalModuleTensor.tmul_balanced, rightModule_normalizedIndicator,
        HeckeAlgebra.normalizedIndicator_idempotent]
    have hfix : eP • u ∈ fixedVectors W.representation K.toSubgroup :=
      heckeAction_normalizedIndicator_mem μP W.representation W.isSmooth K hK u
    rw [h1] at ht ⊢
    have h2 := tensorToCoinvariants_normalizedIndicator N μP μM W K hK hfix
    change tensorToCoinvariants N μP μM W _ = 0 at ht
    rw [h2] at ht
    exact tmul_relations N μP μM W ((Jacquet.mk_eq_zero _ _ _).mp ht) eM
  · intro x
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective W.representation N x
    obtain ⟨K, hK, hv⟩ := exists_compact_fixed W v
    exact ⟨_, tensorToCoinvariants_normalizedIndicator N μP μM W K hK hv⟩

/-- The comparison as a morphism of the two functor values. -/
def tensorToCoinvariantsHom (W : SmoothRep.{0, uP, max uP v} ℂ P) :
    (quotientTensorHeckeFunctor.{uP, v} N μP μM).obj W ⟶
      (coinvariantHeckeFunctor.{uP, v} N μM).obj W :=
  ObjectProperty.homMk (tensorToCoinvariants N μP μM W)

/-- Naturality of the comparison in the smooth representation. -/
theorem tensorToCoinvariantsHom_naturality {W W' : SmoothRep.{0, uP, max uP v} ℂ P}
    (f : W ⟶ W') :
    (quotientTensorHeckeFunctor.{uP, v} N μP μM).map f ≫ tensorToCoinvariantsHom N μP μM W' =
      tensorToCoinvariantsHom N μP μM W ≫ (coinvariantHeckeFunctor.{uP, v} N μM).map f := by
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  let _ := heckeNonUnitalModule μP W.representation W.isSmooth
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext (HeckeAlgebra μP)
    (fun T v => (integratedAction_intertwiner μM
      (isSmooth_normalQuotientAction N W.representation W.isSmooth)
      (isSmooth_normalQuotientAction N W'.representation W'.isSmooth)
      (SmoothRep.hom ((normalCoinvariantFunctor N).map f))
      (HeckeAlgebra.toTestFunction μM T) (Jacquet.mk W.representation N v)).symm))

/-- III.2.10, (III.2.10.2): `j_N` is naturally isomorphic to the actual Hecke
tensor induction along the quotient projection. -/
def coinvariantTensorIso :
    coinvariantHeckeFunctor.{uP, v} N μM ≅ quotientTensorHeckeFunctor N μP μM :=
  (NatIso.ofComponents
    (fun W => nondegenerateIsoOfBijective (tensorToCoinvariantsHom N μP μM W)
      (tensorToCoinvariants_bijective N μP μM W))
    (fun f => tensorToCoinvariantsHom_naturality N μP μM f)).symm

/-- The inverse map on original elementary tensors: `T ⊗ w ↦ T·[w]`. -/
theorem coinvariantTensorIso_inv_tmul (W : SmoothRep.{0, uP, max uP v} ℂ P)
    (T : HeckeAlgebra μM) (v : W) :
    ((coinvariantTensorIso N μP μM).inv.app W).hom.toAddMonoidHom
        (quotientTensorTmul N μP μM W T v) =
      heckeAction μM (normalQuotientAction N W.representation)
        (isSmooth_normalQuotientAction N W.representation W.isSmooth) T
        (Jacquet.mk W.representation N v) := rfl

/-- The forward map (III.2.10.2): a `K`-fixed `w` goes to `e_{q(K)} ⊗ w`. -/
theorem coinvariantTensorIso_hom_mk (W : SmoothRep.{0, uP, max uP v} ℂ P) (v : W)
    (K : OpenSubgroup P) (hK : IsCompact (K : Set P))
    (hv : v ∈ fixedVectors W.representation K.toSubgroup) :
    ((coinvariantTensorIso N μP μM).hom.app W).hom.toAddMonoidHom
        (Jacquet.mk W.representation N v) =
      quotientTensorTmul N μP μM W
        (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
          (isCompact_quotientOpenSubgroup N K hK)) v := by
  apply (tensorToCoinvariants_bijective N μP μM W).1
  have h := congrArg (fun g => g.hom.toAddMonoidHom (Jacquet.mk W.representation N v))
    ((coinvariantTensorIso N μP μM).hom_inv_id_app W)
  exact h.trans (tensorToCoinvariants_normalizedIndicator N μP μM W K hK hv).symm

end Langlands.Hecke.Homomorphism
