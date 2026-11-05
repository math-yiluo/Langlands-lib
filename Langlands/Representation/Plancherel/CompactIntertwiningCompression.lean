import Langlands.Representation.Plancherel.CompactIntertwiningParameterContinuity
import Langlands.Representation.Plancherel.StandardIntertwiningTruncation
import Langlands.Representation.Plancherel.UnramifiedStableLimit
import Langlands.Representation.Plancherel.RationalUnramifiedVectorCancellation

/-! # Compact-picture compression families of the actual standard operator -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Topology Polynomial
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uG uI uV

section CosetMean

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The compact average of a vector is the finite mean over cosets of any
subgroup fixing it. -/
theorem averageMap_eq_finiteMean_cosets (ρ : Representation ℂ Γ V) (hρ : IsSmooth ρ)
    (H : OpenSubgroup Γ) (hH : IsCompact (H : Set Γ)) (L : Subgroup H)
    [Fintype (H ⧸ L)] (v : V) (hL : ∀ l : L, ρ ((l : H) : Γ) v = v) :
    Compact.averageMap ρ hρ H hH v =
      Compact.finiteMean (fun q : H ⧸ L => ρ ((q.out : H) : Γ) v) := by
  classical
  let τ := ρ.comp H.toSubgroup.subtype
  have := Compact.finite_orbit_of_smooth ρ hρ H hH v
  let := Fintype.ofFinite (Compact.orbit τ v)
  change Compact.orbitMean τ v = _
  rw [Compact.orbitMean_eq_finiteMean]
  let f : (H ⧸ L) →[H] Compact.orbit τ v :=
    { toFun := Quotient.lift (fun k : H => (⟨τ k v, ⟨k, rfl⟩⟩ : Compact.orbit τ v)) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp hab
        apply Subtype.ext
        change τ a v = τ b v
        have hb : b = a * (a⁻¹ * b) := by simp
        rw [hb, map_mul, Module.End.mul_apply]
        exact (congrArg (τ a) (hL ⟨a⁻¹ * b, hab'⟩)).symm)
      map_smul' := by
        intro k q
        induction q using Quotient.inductionOn with
        | h x =>
          apply Subtype.ext
          change τ (k * x) v = τ k (τ x v)
          rw [map_mul, Module.End.mul_apply] }
  have hf := Compact.finiteMean_comp f (fun x : Compact.orbit τ v => x.val)
  rw [← hf]
  congr 1
  funext q
  change (f q).val = _
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

/-- The compact average is invariant under the averaging subgroup. -/
theorem averageMap_apply_subgroup' (ρ : Representation ℂ Γ V) (hρ : IsSmooth ρ)
    (H : OpenSubgroup Γ) (hH : IsCompact (H : Set Γ)) (k : H) (v : V) :
    Compact.averageMap ρ hρ H hH (ρ k.val v) = Compact.averageMap ρ hρ H hH v := by
  let τ := ρ.comp H.toSubgroup.subtype
  have ho : Compact.orbit τ (τ k v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g * k, by simp⟩
    · rintro ⟨g, rfl⟩
      refine ⟨g * k⁻¹, ?_⟩
      simp [map_mul, Module.End.mul_apply]
  change Compact.orbitMean τ (τ k v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

end CosetMean

section PolynomialHelpers

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)} {Ω : Set (unramifiedCharacters ν)}

/-- A family in a finite product is polynomial when each coordinate is. -/
theorem isPolynomialOn_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type uV}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (f : Ω → ∀ i, E i)
    (hf : ∀ i, IsPolynomialOn Ω (fun χ => f χ i)) : IsPolynomialOn Ω f := by
  have heq : f = fun χ => ∑ i, LinearMap.single ℂ E i (f χ i) := by
    funext χ
    exact (Finset.univ_sum_single (f χ)).symm
  rw [heq]
  exact isPolynomialOn_finset_sum _ _ fun i _ => (hf i).linearMap (LinearMap.single ℂ E i)

/-- A constant multiple of a polynomial family is polynomial. -/
theorem IsPolynomialOn.const_smul {E : Type uV} [AddCommGroup E] [Module ℂ E] {f : Ω → E}
    (hf : IsPolynomialOn Ω f) (c : ℂ) : IsPolynomialOn Ω (fun χ => c • f χ) :=
  hf.linearMap (c • LinearMap.id)

/-- An endomorphism family of a finite-dimensional space is polynomial when it
is polynomial on every vector. -/
theorem isPolynomialOn_end_of_apply {E : Type uV} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (T : Ω → Module.End ℂ E)
    (hT : ∀ v, IsPolynomialOn Ω (fun χ => T χ v)) : IsPolynomialOn Ω T := by
  let b := Module.finBasis ℂ E
  have heq : T = fun χ => ∑ j, (b.coord j).smulRight (T χ (b j)) := by
    funext χ
    apply LinearMap.ext
    intro x
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    conv_lhs => rw [← b.sum_repr x]
    rw [_root_.map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [heq]
  refine isPolynomialOn_finset_sum _ _ fun j _ => ?_
  exact (hT (b j)).linearMap ((LinearMap.smulRightₗ (b.coord j)))

end PolynomialHelpers

section CompactFixed

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- The fixed right action of the compact subgroup on the compact picture. -/
abbrev compactPictureAction :=
  smoothInduced (P.comap K.toSubgroup.subtype) (compactPictureInducingRepresentation h K A)

/-- The compact-picture identification intertwines right translation by `K`. -/
theorem unramifiedLeviInductionCompactEquiv_translate (χ : unramifiedCharacters ν) (k : K)
    (F : UnramifiedLeviInduction h hU ν χ A) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A
        ((UnramifiedLeviInduction h hU ν χ A).representation (k : G) F) =
      compactPictureAction h K A k
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k'
  rfl

/-- The subgroup of `K` cut out by an open subgroup of the ambient group. -/
abbrev compactFixedSubgroup (H : OpenSubgroup G) : Subgroup K :=
  H.toSubgroup.comap K.toSubgroup.subtype

/-- Compact-picture vectors fixed by `H ∩ K`. -/
abbrev CompactFixedVectors (H : OpenSubgroup G) :=
  fixedVectors (compactPictureAction h K A) (compactFixedSubgroup K H)

omit [LocallyCompactSpace G] in
theorem eval_mul_of_mem_compactFixed (H : OpenSubgroup G) (w : CompactFixedVectors h K A H)
    (k x : K) (hx : (x : G) ∈ H) : eval _ _ w.val (k * x) = eval _ _ w.val k := by
  have hw := w.property ⟨x, hx⟩
  exact congrArg (fun f => eval _ _ f k) hw

/-- For `H ≤ K`, the identification restricts to fixed vectors at every parameter. -/
def compactFixedEquiv (χ : unramifiedCharacters ν) (H : OpenSubgroup G) (hHK : H ≤ K) :
    CompactFixedVectors h K A H ≃ₗ[ℂ]
      fixedVectors (UnramifiedLeviInduction h hU ν χ A).representation H.toSubgroup where
  toFun w := ⟨(unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val,
    fun x => by
      apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).injective
      have ht := unramifiedLeviInductionCompactEquiv_translate h hU hδ K hP hK hPK ν hν hr A χ
        ⟨x, hHK x.property⟩
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val)
      rw [LinearEquiv.apply_symm_apply] at ht
      rw [LinearEquiv.apply_symm_apply]
      exact ht.trans (w.property ⟨⟨x, hHK x.property⟩, x.property⟩)⟩
  invFun F := ⟨unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A F.val,
    fun x => by
      have ht := unramifiedLeviInductionCompactEquiv_translate h hU hδ K hP hK hPK ν hν hr A χ
        x.val F.val
      change compactPictureAction h K A x.val _ = _
      rw [← ht]
      exact congrArg _ (F.property ⟨x.val, x.property⟩)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  left_inv w := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  right_inv F := Subtype.ext (LinearEquiv.symm_apply_apply _ _)

@[simp]
theorem compactFixedEquiv_symm_apply (χ : unramifiedCharacters ν) (H : OpenSubgroup G)
    (hHK : H ≤ K)
    (F : fixedVectors (UnramifiedLeviInduction h hU ν χ A).representation H.toSubgroup) :
    ((compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK).symm F :
        CompactInductionPicture h K A) =
      unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A F.val := rfl

@[simp]
theorem compactFixedEquiv_apply (χ : unramifiedCharacters ν) (H : OpenSubgroup G) (hHK : H ≤ K)
    (w : CompactFixedVectors h K A H) :
    (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w : UnramifiedLeviInduction h hU ν χ A) =
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val := rfl

/-- The open Levi subgroup `M ∩ x H x⁻¹`. -/
def leviConjSubgroup (H : OpenSubgroup G) (x : G) : OpenSubgroup M :=
  (H.comap (MulAut.conj x⁻¹).toMonoidHom (by
    change Continuous fun g : G => x⁻¹ * g * x⁻¹⁻¹
    fun_prop)).comap M.subtype continuous_subtype_val

omit [LocallyCompactSpace G] in
theorem mem_leviConjSubgroup (H : OpenSubgroup G) (x : G) (m : M) :
    m ∈ leviConjSubgroup H x ↔ x⁻¹ * (m : G) * x ∈ H := by
  change x⁻¹ * (m : G) * x⁻¹⁻¹ ∈ H ↔ _
  rw [inv_inv]

omit [LocallyCompactSpace G] in
/-- Values of fixed compact-picture vectors are fixed by the corresponding
conjugated Levi subgroup. -/
theorem eval_mem_fixedVectors_leviConj (H : OpenSubgroup G) (hHK : H ≤ K)
    (w : CompactFixedVectors h K A H) (x : K) :
    eval _ _ w.val x ∈ fixedVectors A.representation (leviConjSubgroup H (x : G)).toSubgroup := by
  intro m
  have hy : x⁻¹ * (m.val : G) * x ∈ H := (mem_leviConjSubgroup H (x : G) m.val).mp m.property
  have hmK : (m.val : G) ∈ K := by
    have e : (m.val : G) = x * (x⁻¹ * (m.val : G) * x) * x⁻¹ := by simp [mul_assoc]
    rw [e]
    exact K.mul_mem (K.mul_mem x.property (hHK hy)) (K.inv_mem x.property)
  let p : P.comap K.toSubgroup.subtype := ⟨⟨m.val, hmK⟩, h.levi_le m.val.property⟩
  have hcov := w.val.1.2 p x
  have hproj : h.projection ⟨m.val, h.levi_le m.val.property⟩ = m.val :=
    h.projection_levi m.val
  have hmul : (p : K) * x = x * ⟨x⁻¹ * (m.val : G) * x, hHK hy⟩ := by
    apply Subtype.ext
    change (m.val : G) * x = x * (x⁻¹ * (m.val : G) * x)
    simp [mul_assoc]
  change A.representation (m.val) (eval _ _ w.val x) = eval _ _ w.val x
  have h1 : eval _ _ w.val ((p : K) * x) = A.representation (m.val) (eval _ _ w.val x) := by
    change w.val.1.1 ((Subgroup.comap K.toSubgroup.subtype P).subtype p * x) = _
    rw [hcov]
    change A.representation (h.projection ⟨m.val, h.levi_le m.val.property⟩) _ = _
    rw [hproj]
    rfl
  rw [← h1, hmul, eval_mul_of_mem_compactFixed h K A H w x _ hy]

omit [LocallyCompactSpace G] in
include hK in
/-- Fixed compact-picture vectors of an admissible representation form a
finite-dimensional space. -/
theorem finiteDimensional_compactFixedVectors (hadm : A.IsAdmissible) (H : OpenSubgroup G)
    (hHK : H ≤ K) : FiniteDimensional ℂ (CompactFixedVectors h K A H) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  have hopen : IsOpen (compactFixedSubgroup K H : Set K) :=
    H.isOpen.preimage continuous_subtype_val
  have : Finite (K ⧸ compactFixedSubgroup K H) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have : Fintype (K ⧸ compactFixedSubgroup K H) := Fintype.ofFinite _
  have hfin : ∀ q : K ⧸ compactFixedSubgroup K H,
      Module.Finite ℂ (fixedVectors A.representation
        (leviConjSubgroup H ((q.out : K) : G)).toSubgroup) :=
    fun q => hadm.2 _
  let φ : CompactFixedVectors h K A H →ₗ[ℂ] ∀ q : K ⧸ compactFixedSubgroup K H,
      fixedVectors A.representation (leviConjSubgroup H ((q.out : K) : G)).toSubgroup :=
    { toFun := fun w q => ⟨eval _ _ w.val q.out,
        eval_mem_fixedVectors_leviConj h K A H hHK w q.out⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (compactFixedSubgroup K H) k
    have hk : k = (QuotientGroup.mk k : K ⧸ compactFixedSubgroup K H).out * y⁻¹ := by
      rw [hy]
      simp [mul_assoc]
    have h0 := congrArg Subtype.val (congrFun hw (QuotientGroup.mk k))
    change eval _ _ w.val _ = 0 at h0
    change eval _ _ w.val k = 0
    rw [hk, eval_mul_of_mem_compactFixed h K A H w _
      ((y⁻¹ : compactFixedSubgroup K H) : K) (y⁻¹).property]
    exact h0
  exact Module.Finite.of_injective φ hinj

/-- Evaluation of fixed compact-picture vectors at chosen coset representatives. -/
def compactFixedEval (H : OpenSubgroup G) :
    CompactFixedVectors h K A H →ₗ[ℂ] (K ⧸ compactFixedSubgroup K H → A) where
  toFun w q := eval _ _ w.val q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] in
theorem compactFixedEval_injective (H : OpenSubgroup G) :
    Function.Injective (compactFixedEval h K A H) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (compactFixedSubgroup K H) k
  have hk : k = (QuotientGroup.mk k : K ⧸ compactFixedSubgroup K H).out * y⁻¹ := by
    rw [hy]
    simp [mul_assoc]
  have h0 := congrFun hw (QuotientGroup.mk k)
  change eval _ _ w.val _ = 0 at h0
  change eval _ _ w.val k = 0
  rw [hk, eval_mul_of_mem_compactFixed h K A H w _
    ((y⁻¹ : compactFixedSubgroup K H) : K) (y⁻¹).property]
  exact h0

include hK in
omit [LocallyCompactSpace G] in
/-- A family of fixed compact-picture vectors is polynomial when each value is. -/
theorem isPolynomialOn_compactFixed_of_eval (H : OpenSubgroup G)
    {Ω : Set (unramifiedCharacters ν)} (X : Ω → CompactFixedVectors h K A H)
    (hX : ∀ k : K, IsPolynomialOn Ω (fun χ => eval _ _ (X χ).val k)) :
    IsPolynomialOn Ω X := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  have hopen : IsOpen (compactFixedSubgroup K H : Set K) :=
    H.isOpen.preimage continuous_subtype_val
  have : Finite (K ⧸ compactFixedSubgroup K H) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have : Fintype (K ⧸ compactFixedSubgroup K H) := Fintype.ofFinite _
  apply isPolynomialOn_of_linearMap_injective (compactFixedEval h K A H)
    (compactFixedEval_injective h K A H)
  exact isPolynomialOn_pi _ fun q => hX q.out

end CompactFixed

section Compression

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {H : OpenSubgroup G} (hH : IsCompact (H : Set G)) (hHK : H ≤ K) (a : G)

/-- The elements of `H` whose conjugate by `a⁻¹` stays in `H`. -/
def compressionStabilizer (H : OpenSubgroup G) (a : G) : Subgroup H :=
  (H.toSubgroup.comap (MulAut.conj a⁻¹).toMonoidHom).subgroupOf H.toSubgroup

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem mem_compressionStabilizer (x : H) :
    x ∈ compressionStabilizer H a ↔ a⁻¹ * (x : G) * a ∈ H := by
  change a⁻¹ * (x : G) * a⁻¹⁻¹ ∈ H ↔ _
  rw [inv_inv]

omit [LocallyCompactSpace G] in
include hH in
theorem finite_compressionStabilizer : Finite (H ⧸ compressionStabilizer H a) := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  apply Subgroup.quotient_finite_of_isOpen
  have hc : Continuous fun x : H => a⁻¹ * (x : G) * a := by fun_prop
  have := H.isOpen.preimage hc
  convert this using 1
  ext x
  exact mem_compressionStabilizer a x

/-- The Casselman compression by `a`, transported to the fixed compact picture. -/
def compactCompression (χ : unramifiedCharacters ν) :
    Module.End ℂ (CompactFixedVectors h K A H) :=
  (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK).symm.toLinearMap ∘ₗ
    (Jacquet.compressedAction (UnramifiedLeviInduction h hU ν χ A).representation
      (UnramifiedLeviInduction h hU ν χ A).isSmooth H hH a ∘ₗ
    (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK).toLinearMap)

/-- Values of the transported compression are finite coset means of the actual
covariant extension. -/
theorem eval_compactCompression (χ : unramifiedCharacters ν)
    (w : CompactFixedVectors h K A H) (k : K) :
    letI := finite_compressionStabilizer hH a
    letI := Fintype.ofFinite (H ⧸ compressionStabilizer H a)
    eval _ _ (compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ w).val k =
      Compact.finiteMean (fun q : H ⧸ compressionStabilizer H a =>
        eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm
          w.val) ((k : G) * ((q.out : H) : G) * a)) := by
  let := finite_compressionStabilizer hH a
  let := Fintype.ofFinite (H ⧸ compressionStabilizer H a)
  have hL : ∀ l : compressionStabilizer H a,
      (UnramifiedLeviInduction h hU ν χ A).representation ((l : H) : G)
        ((UnramifiedLeviInduction h hU ν χ A).representation a
          (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w).val) =
      (UnramifiedLeviInduction h hU ν χ A).representation a
        (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w).val := by
    intro l
    have hl : a⁻¹ * ((l : H) : G) * a ∈ H := (mem_compressionStabilizer a l.val).mp l.property
    have e : ((l : H) : G) * a = a * (a⁻¹ * ((l : H) : G) * a) := by simp [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    exact congrArg _ ((compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w).property
      ⟨_, hl⟩)
  simp only [compactCompression, LinearMap.comp_apply, LinearEquiv.coe_coe,
    compactFixedEquiv_symm_apply, Jacquet.compressedAction_apply,
    unramifiedLeviInductionCompactEquiv_eval]
  rw [averageMap_eq_finiteMean_cosets _ _ H hH (compressionStabilizer H a) _ hL]
  unfold Compact.finiteMean
  let evk : UnramifiedLeviInduction h hU ν χ A →ₗ[ℂ] A :=
    { toFun := fun F => eval P (leviInflatedInducingRepresentation h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) F (k : G)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change evk ((Fintype.card (H ⧸ compressionStabilizer H a) : ℂ)⁻¹ •
    ∑ q : H ⧸ compressionStabilizer H a,
      (UnramifiedLeviInduction h hU ν χ A).representation ((q.out : H) : G)
        ((UnramifiedLeviInduction h hU ν χ A).representation a
          (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w).val)) = _
  rw [map_smul, _root_.map_sum]
  rfl

/-- The transported compression is a polynomial endomorphism family on the
finite-dimensional fixed compact picture. -/
theorem isPolynomialOn_compactCompression (hadm : A.IsAdmissible)
    (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOn Ω (fun χ : Ω =>
      compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ.val) := by
  have := finiteDimensional_compactFixedVectors h K hK A hadm H hHK
  apply isPolynomialOn_end_of_apply
  intro w
  apply isPolynomialOn_compactFixed_of_eval h K hK ν A H
  intro k
  let := finite_compressionStabilizer hH a
  let := Fintype.ofFinite (H ⧸ compressionStabilizer H a)
  have heq : (fun χ : Ω => eval _ _
      (compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ.val w).val k) =
      fun χ : Ω => (Fintype.card (H ⧸ compressionStabilizer H a) : ℂ)⁻¹ •
        ∑ q : H ⧸ compressionStabilizer H a,
          eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ.val
            A).symm w.val) ((k : G) * ((q.out : H) : G) * a) := by
    funext χ
    exact eval_compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ.val w k
  rw [heq]
  refine IsPolynomialOn.const_smul ?_ _
  exact isPolynomialOn_finset_sum _ _ fun q _ =>
    unramifiedCompactExtension_eval_isPolynomialOn h hU hδ K hP hK hPK ν hν hr A Ω w.val _

end Compression

section Dual

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {H : OpenSubgroup G}

/-- The Levi part `H ∩ M`, as an open subgroup of `M`. -/
def leviPartOpen (H : OpenSubgroup G) : OpenSubgroup M :=
  H.comap M.subtype continuous_subtype_val

/-- Algebraic functionals fixed by the Levi part of `H`. -/
abbrev LeviFixedDual (H : OpenSubgroup G) :=
  fixedVectors A.representation.dual (leviPartOpen (M := M) H).toSubgroup

include hP hν hr hK in
omit [LocallyCompactSpace G] in
/-- Unramified characters are trivial on Levi elements of the compact subgroup. -/
theorem unramified_eq_one_of_mem_compact (χ : unramifiedCharacters ν) (m : M)
    (hm : (m : G) ∈ K) : χ.val m = 1 := by
  have hp : (⟨m, h.levi_le m.property⟩ : P) ∈ conjOpenSubgroup P K 1 := by
    apply mem_conjOpenSubgroup.mpr
    simpa using hm
  have := unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν h.projection hr χ K hK 1 hp
  rwa [h.projection_levi] at this

include hP hν hr hK in
omit [LocallyCompactSpace G] in
/-- A Levi-fixed algebraic functional is smooth for every unramified twist. -/
theorem leviFixedDual_mem_smoothVectors (hHK : H ≤ K) (χ : unramifiedCharacters ν)
    (y : LeviFixedDual A H) :
    y.val ∈ smoothVectors
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation.dual := by
  refine ⟨leviPartOpen H, fun k => ?_⟩
  have hk : ((k : M) : G) ∈ K := hHK k.property
  have hχ : χ.val (k : M)⁻¹ = 1 := by
    rw [map_inv, unramified_eq_one_of_mem_compact h K hP hK ν hν hr χ (k : M) hk, inv_one]
  apply LinearMap.ext
  intro v
  have hy := congrArg (fun ℓ : Module.Dual ℂ A => ℓ v) (y.property k)
  change y.val ((χ.val (k : M)⁻¹ : ℂ) • A.representation (k : M)⁻¹ v) = y.val v
  rw [hχ, Units.val_one, one_smul]
  exact hy

/-- Levi-fixed functionals as smooth functionals of each unramified twist. -/
def leviFixedDualSmooth (hHK : H ≤ K) (χ : unramifiedCharacters ν) :
    LeviFixedDual A H →ₗ[ℂ]
      SmoothDual (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation where
  toFun y := ⟨y.val, leviFixedDual_mem_smoothVectors h K hP hK ν hν hr A hHK χ y⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] in
/-- Levi-fixed functionals form a finite-dimensional space for admissible
representations of a closed Levi. -/
theorem finiteDimensional_leviFixedDual (hadm : A.IsAdmissible) (hM : IsClosed (M : Set G))
    (hH : IsCompact (H : Set G)) : FiniteDimensional ℂ (LeviFixedDual A H) := by
  have hHM : IsCompact ((leviPartOpen (M := M) H : Set M)) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  have hfin : Module.Finite ℂ (fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup) :=
    hadm.2 _
  let r : LeviFixedDual A H →ₗ[ℂ]
      Module.Dual ℂ (fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup) :=
    { toFun := fun y => y.val.comp (Submodule.subtype _)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective r := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hfix : ∀ k : leviPartOpen (M := M) H, y.val (A.representation (k : M) v) = y.val v := by
      intro k
      have hk := congrArg (fun ℓ : Module.Dual ℂ A => ℓ (A.representation (k : M) v))
        (y.property k)
      change y.val (A.representation ((k : M)⁻¹) (A.representation (k : M) v)) =
        y.val (A.representation (k : M) v) at hk
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at hk
      exact hk.symm
    have havg := Jacquet.map_averageMap_of_forall_eq A.representation A.isSmooth
      (leviPartOpen H) hHM y.val v (y.val v) hfix
    rw [← havg]
    exact LinearMap.congr_fun hy
      ⟨_, Compact.averageMap_mem_fixedVectors A.representation A.isSmooth _ hHM v⟩
  exact Module.Finite.of_injective r hinj

/-- The contragredient action of a Levi element normalizing `H ∩ M`, restricted
to Levi-fixed functionals. -/
def leviDualShift (b : M)
    (hb : ∀ m : M, (m : G) ∈ H → ((b⁻¹ * m * b : M) : G) ∈ H) :
    Module.End ℂ (LeviFixedDual A H) :=
  (A.representation.dual b).restrict (fun y hy k => by
    have hk : ((b⁻¹ * (k : M) * b : M) : G) ∈ H := hb (k : M) k.property
    change A.representation.dual (k : M) (A.representation.dual b y) = A.representation.dual b y
    rw [← Module.End.mul_apply, ← map_mul,
      show (k : M) * b = b * (b⁻¹ * (k : M) * b) by group, map_mul, Module.End.mul_apply]
    exact congrArg _ (hy ⟨b⁻¹ * (k : M) * b, hk⟩))

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem leviDualShift_apply (b : M)
    (hb : ∀ m : M, (m : G) ∈ H → ((b⁻¹ * m * b : M) : G) ∈ H) (y : LeviFixedDual A H) (v : A) :
    (leviDualShift A b hb y).val v = y.val (A.representation b⁻¹ v) := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A scalar multiple of the Levi dual shift by a constant times an
evaluation is a polynomial family. -/
theorem isPolynomialOn_leviDualShift (b : M)
    (hb : ∀ m : M, (m : G) ∈ H → ((b⁻¹ * m * b : M) : G) ∈ H) (c : ℂ)
    (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOn Ω (fun χ : Ω =>
      (c * (χ.val.val b⁻¹ : ℂ)) • leviDualShift A b hb) := by
  refine ⟨1, fun _ => c • unramifiedEvaluationRegular ν b⁻¹, fun _ => leviDualShift A b hb, ?_⟩
  intro χ
  simp only [Fin.sum_univ_one]
  rfl

omit [LocallyCompactSpace G] in
/-- Levi-fixed functionals separate Levi-fixed vectors. -/
theorem leviFixedPairing_injective (hM : IsClosed (M : Set G)) (hH : IsCompact (H : Set G))
    (v : fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup)
    (hv : ∀ y : LeviFixedDual A H, y.val v.val = 0) : v = 0 := by
  have hHM : IsCompact ((leviPartOpen (M := M) H : Set M)) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  apply Subtype.ext
  change v.val = 0
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  let y : Module.Dual ℂ A :=
    φ.comp (Compact.averageMap A.representation A.isSmooth (leviPartOpen H) hHM)
  have hy : y ∈ fixedVectors A.representation.dual (leviPartOpen (M := M) H).toSubgroup := by
    intro k
    apply LinearMap.ext
    intro x
    change φ (Compact.averageMap A.representation A.isSmooth (leviPartOpen H) hHM
      (A.representation ((k : M)⁻¹) x)) = φ (Compact.averageMap A.representation A.isSmooth
        (leviPartOpen H) hHM x)
    exact congrArg φ (averageMap_apply_subgroup' A.representation A.isSmooth (leviPartOpen H) hHM
      k⁻¹ x)
  have h0 := hv ⟨y, hy⟩
  change φ (Compact.averageMap A.representation A.isSmooth (leviPartOpen H) hHM v.val) = 0 at h0
  rwa [Compact.averageMap_id A.representation A.isSmooth (leviPartOpen H) hHM v.val v.property]
    at h0

end Dual

section Numerator

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (U' : Subgroup G)
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))
  (hM : IsClosed (M : Set G))

/-- The value at the identity of the actual standard integral of a compact
section, as a linear map, at a parameter of full convergence. -/
def compactIdentityValue (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤) :
    CompactInductionPicture h K A →ₗ[ℂ] A :=
  (LinearMap.proj (1 : G)).comp
    ((operator h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν hM).comp
      ((sourceToDomain h hU _ qν hfull).toLinearMap.comp
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm.toLinearMap))

omit [BorelSpace (QuotientSpace (U := U) U')] in
theorem truncatedIntegral_add_functional' (A' : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (C : Set (QuotientSpace (U := U) U')) (g : G)
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A'}
    (hf : f ∈ domain h hU U' A' qν) (ℓ ℓ' : SmoothDual A'.representation) :
    truncatedIntegral h hU U' A' qν C g f (ℓ + ℓ') =
      truncatedIntegral h hU U' A' qν C g f ℓ + truncatedIntegral h hU U' A' qν C g f ℓ' := by
  unfold truncatedIntegral
  rw [← integral_add (integrable_scalar_of_mem_domain h hU U' A' qν hf g ℓ).integrableOn
    (integrable_scalar_of_mem_domain h hU U' A' qν hf g ℓ').integrableOn]
  rfl

/-- The pairing of the identity value with Levi-fixed functionals. -/
def compactLimitForm (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (H : OpenSubgroup G) :
    CompactFixedVectors h K A H →ₗ[ℂ] LeviFixedDual A H →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun w y => y.val (compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ hfull w.val))
    (fun w w' y => by simp only [Submodule.coe_add, map_add])
    (fun c w y => by simp only [SetLike.val_smul, map_smul, smul_eq_mul])
    (fun w y y' => by simp only [Submodule.coe_add, LinearMap.add_apply])
    (fun c w y => by simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul])

/-- The truncated integral over the compact radical piece, paired with
Levi-fixed functionals, at one parameter of full convergence. -/
def compactTruncationForm (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    {H : OpenSubgroup G} (hHK : H ≤ K) :
    CompactFixedVectors h K A H →ₗ[ℂ] LeviFixedDual A H →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun w y => truncatedIntegral h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
      (compactRadicalPiece U' H) 1
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val)
      (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y))
    (fun w w' y => by
      have := map_add ((truncatedFunctional h hU U'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
        (compactRadicalPiece U' H) 1 (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y)).comp
        ((sourceToDomain h hU _ qν hfull).toLinearMap.comp
          (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm.toLinearMap))
        w.val w'.val
      exact this)
    (fun c w y => by
      have := map_smul ((truncatedFunctional h hU U'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
        (compactRadicalPiece U' H) 1 (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y)).comp
        ((sourceToDomain h hU _ qν hfull).toLinearMap.comp
          (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm.toLinearMap))
        c w.val
      exact this)
    (fun w y y' => by
      rw [map_add]
      exact truncatedIntegral_add_functional' h hU U' qν _ _ 1
        (hfull ▸ Submodule.mem_top) _ _)
    (fun c w y => by
      rw [map_smul]
      exact truncatedIntegral_smul_functional h hU U' _ qν _ 1 _ c _)

/-- On the compact radical piece the truncated integrand of a compact section
does not depend on the unramified parameter. -/
theorem truncatedIntegral_compactRadicalPiece_eq {H : OpenSubgroup G} (hHK : H ≤ K)
    (χ χ' : unramifiedCharacters ν) (w : CompactFixedVectors h K A H)
    (y : LeviFixedDual A H) :
    truncatedIntegral h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
        (compactRadicalPiece U' H) 1
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val)
        (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y) =
      truncatedIntegral h hU U'
        (A.twist χ'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ')) qν
        (compactRadicalPiece U' H) 1
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ' A).symm w.val)
        (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ' y) := by
  have hval : ∀ (ψ : unramifiedCharacters ν) (x : U') (hx : (x : G) ∈ H),
      eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr ψ A).symm w.val)
        ((x : G) * 1) = eval _ _ w.val ⟨x, hHK hx⟩ := by
    intro ψ x hx
    rw [mul_one]
    have := unramifiedLeviInductionCompactEquiv_eval h hU hδ K hP hK hPK ν hν hr ψ A
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr ψ A).symm w.val)
      ⟨x, hHK hx⟩
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  unfold truncatedIntegral
  apply setIntegral_congr_fun (isOpen_compactRadicalPiece U' H).measurableSet
  rintro _ ⟨x, hx, rfl⟩
  simp only [Induction.quotientMap, integrand_mk]
  erw [hval χ x hx, hval χ' x hx]
  rfl

end Numerator

section Convergence

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (U' : Subgroup G) (hMU' : M ≤ Subgroup.normalizer (U' : Set G))
  [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G))
  {H : OpenSubgroup G} (hH : IsCompact (H : Set G)) (hHK : H ≤ K)
  {O : Subgroup G} {a : G} (hI : Jacquet.IsIwahoriContraction H U' M O a)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [LocallyCompactSpace U'] [MeasurableSpace U']
  [BorelSpace U'] [T2Space G] in
/-- Conjugation by the contracting Levi element preserves `H ∩ M`. -/
theorem contractionLevi_conj_mem (m : M) (hm : (m : G) ∈ H) :
    (((contractionLevi U' hI)⁻¹ * m * contractionLevi U' hI : M) : G) ∈ H :=
  (hI.levi (m : G) ⟨hm, m.property⟩).1

/-- The parameter family on Levi-fixed functionals matching the dual
compression shift. -/
def compactDualShift (χ : unramifiedCharacters ν) : Module.End ℂ (LeviFixedDual A H) :=
  (((leviShiftFactor h hU U' hMU' (contractionLevi U' hI))⁻¹ : ℂ) *
      (χ.val (contractionLevi U' hI)⁻¹ : ℂ)) •
    leviDualShift A (contractionLevi U' hI) (contractionLevi_conj_mem U' hI)

omit [T2Space G] [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] in
theorem isPolynomialOn_compactDualShift (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOn Ω (fun χ : Ω => compactDualShift h hU ν A U' hMU' hI χ.val) :=
  isPolynomialOn_leviDualShift ν A _ _ _ Ω

omit [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  [T2Space G] in
theorem leviFixedDualSmooth_compactDualShift (χ : unramifiedCharacters ν)
    (y : LeviFixedDual A H) :
    leviFixedDualSmooth h K hP hK ν hν hr A hHK χ (compactDualShift h hU ν A U' hMU' hI χ y) =
      dualCompressionShift h hU U'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hMU' hI
        (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ((((leviShiftFactor h hU U' hMU' (contractionLevi U' hI))⁻¹ : ℂ) *
      (χ.val (contractionLevi U' hI)⁻¹ : ℂ)) •
      y.val (A.representation (contractionLevi U' hI)⁻¹ v)) =
    ((leviShiftFactor h hU U' hMU' (contractionLevi U' hI))⁻¹ : ℂ) •
      y.val ((χ.val (contractionLevi U' hI)⁻¹ : ℂ) •
        A.representation (contractionLevi U' hI)⁻¹ v)
  rw [map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_assoc]

omit [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  [T2Space G] in
theorem leviFixedDualSmooth_compactDualShift_pow (χ : unramifiedCharacters ν)
    (y : LeviFixedDual A H) (n : ℕ) :
    leviFixedDualSmooth h K hP hK ν hν hr A hHK χ
        ((compactDualShift h hU ν A U' hMU' hI χ ^ n) y) =
      (dualCompressionShift h hU U'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hMU' hI ^ n)
        (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, leviFixedDualSmooth_compactDualShift, ih,
      pow_succ', Module.End.mul_apply]

omit [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU'] [IsHaarMeasure μI]
  [μI.Regular] [IsMulRightInvariant μI] in
theorem compactFixedEquiv_compactCompression_pow (χ : unramifiedCharacters ν)
    (w : CompactFixedVectors h K A H) (n : ℕ) :
    compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK
        ((compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ ^ n) w) =
      (Jacquet.compressedAction (UnramifiedLeviInduction h hU ν χ A).representation
        (UnramifiedLeviInduction h hU ν χ A).isSmooth H hH a ^ n)
        (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    change compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK
      ((compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

include hqν in
/-- Iterated compact compression and dual shifts converge pointwise to the
pairing of the actual identity value. -/
theorem tendsto_compactTruncationForm (χ₁ χ : unramifiedCharacters ν)
    (hfull₁ : domain h hU U'
      (A.twist χ₁.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ₁)) qν = ⊤)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (w : CompactFixedVectors h K A H) (y : LeviFixedDual A H) :
    Tendsto (fun n => compactTruncationForm h hU hδ K hP hK hPK ν hν hr A U' qν χ₁ hfull₁ hHK
        ((compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ ^ n) w)
        ((compactDualShift h hU ν A U' hMU' hI χ ^ n) y)) atTop
      (𝓝 (compactLimitForm h hU hδ K hP hK hPK ν hν hr A U' qν hM χ hfull H w y)) := by
  have heq : ∀ n : ℕ, compactTruncationForm h hU hδ K hP hK hPK ν hν hr A U' qν χ₁ hfull₁ hHK
      ((compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a χ ^ n) w)
      ((compactDualShift h hU ν A U' hMU' hI χ ^ n) y) =
      truncatedIntegral h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
        (compactRadicalPiece U' H) 1
        (((Jacquet.compressedAction (UnramifiedLeviInduction h hU ν χ A).representation
          (UnramifiedLeviInduction h hU ν χ A).isSmooth H hH a) ^ n)
          (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w) :
            UnramifiedLeviInduction h hU ν χ A)
        ((dualCompressionShift h hU U'
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hMU' hI ^ n)
          (leviFixedDualSmooth h K hP hK ν hν hr A hHK χ y)) := by
    intro n
    change truncatedIntegral h hU U' _ qν _ 1 _ _ = _
    rw [truncatedIntegral_compactRadicalPiece_eq h hU hδ K hP hK hPK ν hν hr A U' qν hHK χ₁ χ,
      leviFixedDualSmooth_compactDualShift_pow, ← compactFixedEquiv_compactCompression_pow]
    rfl
  simp_rw [heq]
  exact tendsto_compressedTruncation h hU U'
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hMU' qν μU' μI hqν hfull hH
    (UnramifiedLeviInduction h hU ν χ A).isSmooth hM hI _ _

omit [T2Space G] [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] in
/-- The actual Levi factor is a positive real number. -/
theorem exists_pos_leviShiftFactor_eq (m : M) :
    ∃ r : ℝ, 0 < r ∧ leviShiftFactor h hU U' hMU' m = (r : ℂ) := by
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  refine ⟨((Jacquet.positiveHalfCharacter
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) m : ℝ≥0) : ℝ) *
      (quotientConjugationModulus h hU U' hMU' m : ℝ), ?_, ?_⟩
  · apply mul_pos
    · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    · exact_mod_cast quotientConjugationModulus_pos h hU U' hMU' m
  · unfold leviShiftFactor
    change (((Jacquet.positiveHalfCharacter
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) m : ℝ≥0) : ℝ) : ℂ) *
        ((quotientConjugationModulus h hU U' hMU' m : ℝ) : ℂ) = _
    push_cast
    rfl

include hqν hP hν hr hK hH hHK hMU' in
/-- The identity value of a fixed compact section is fixed by the Levi part of
`H`. -/
theorem compactIdentityValue_mem_fixedVectors (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (w : CompactFixedVectors h K A H) :
    compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ hfull w.val ∈
      fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup := by
  intro m
  set A' := A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)
  set F := sourceToDomain h hU A' qν hfull
    ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm w.val)
  have hF : ∀ k : H, (UnramifiedLeviInduction h hU ν χ A).representation (k : G) F.val = F.val :=
    fun k => (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A χ H hHK w).property k
  set x := operator h hU U' A' qν hM F 1
  have hx : compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ hfull w.val = x := rfl
  rw [hx]
  have hmH : ((m : M) : G) ∈ H := m.property
  have hstab := operator_preserves_stabilizer h hU U' A' qν hM F H hF ⟨(m : M), hmH⟩ 1
  have hlevi := operator_levi_mul h hU U' hMU' A' qν μU' μI hqν hM F (m : M) 1
  rw [one_mul] at hstab
  rw [mul_one, hstab] at hlevi
  have hχ : χ.val (m : M) = 1 :=
    unramified_eq_one_of_mem_compact h K hP hK ν hν hr χ (m : M) (hHK hmH)
  have hA' : A'.representation (m : M) x = A.representation (m : M) x := by
    change (χ.val (m : M) : ℂ) • A.representation (m : M) x = _
    rw [hχ, Units.val_one, one_smul]
  rw [hA'] at hlevi
  change x = leviShiftFactor h hU U' hMU' (m : M) • A.representation (m : M) x at hlevi
  obtain ⟨r, hr0, hγ⟩ := exists_pos_leviShiftFactor_eq h hU U' hMU' (m : M)
  have hγ0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [hγ] at hlevi
  have hstep : A.representation (m : M) x = (r : ℂ)⁻¹ • x := by
    calc A.representation (m : M) x =
        (r : ℂ)⁻¹ • ((r : ℂ) • A.representation (m : M) x) := by
          rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
      _ = (r : ℂ)⁻¹ • x := by rw [← hlevi]
  have hpow : ∀ n : ℕ, A.representation ((m : M) ^ n) x = ((r : ℂ)⁻¹) ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_smul, hstep, smul_smul, pow_succ]
  by_cases hx0 : x = 0
  · change A.representation (m : M) x = x
    rw [hx0, map_zero]
  obtain ⟨O, hO⟩ := A.isSmooth x
  have hHM : IsCompact ((leviPartOpen (M := M) H : Set M)) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  have : CompactSpace (leviPartOpen (M := M) H) := isCompact_iff_compactSpace.mp hHM
  have : IsTopologicalGroup (leviPartOpen (M := M) H) :=
    inferInstanceAs (IsTopologicalGroup (leviPartOpen (M := M) H).toSubgroup)
  have hopen : IsOpen ((O.toSubgroup.subgroupOf (leviPartOpen (M := M) H).toSubgroup :
      Subgroup (leviPartOpen (M := M) H)) : Set (leviPartOpen (M := M) H)) :=
    O.isOpen.preimage continuous_subtype_val
  have : Finite ((leviPartOpen (M := M) H) ⧸
      O.toSubgroup.subgroupOf (leviPartOpen (M := M) H).toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : O.toSubgroup.relIndex (leviPartOpen (M := M) H).toSubgroup ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  obtain ⟨n, hn, -, hmem⟩ :=
    Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx m.property
  have hfixn : A.representation ((m : M) ^ n) x = x := hO ⟨_, hmem.1⟩
  rw [hpow n] at hfixn
  have hone : ((r : ℂ)⁻¹) ^ n = 1 := by
    by_contra hne
    apply hx0
    have : (((r : ℂ)⁻¹) ^ n - 1) • x = 0 := by rw [sub_smul, hfixn, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hrn : r ^ n = 1 := by
    have : ((r ^ n : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_pow, ← inv_inv ((r : ℂ) ^ n), ← inv_pow, hone, inv_one]
    exact_mod_cast this
  have hr1 : r = 1 := (pow_eq_one_iff_of_nonneg hr0.le hn.ne').mp hrn
  change A.representation (m : M) x = x
  rw [hstep, hr1, Complex.ofReal_one, inv_one, one_smul]

include hqν hP hν hr hK hH hHK hMU' hI in
/-- For an Iwahori contraction `H ≤ K`, one nonzero regular scalar makes the
identity value of the actual standard integral polynomial on every `H`-fixed
compact section, over any set of parameters of full convergence. -/
theorem exists_regular_compactIdentityValue_numerator (hadm : A.IsAdmissible)
    (Ω : Set (unramifiedCharacters ν))
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) :
    ∃ b : unramifiedRegularFunctions ν, b ≠ 0 ∧ ∀ w : CompactFixedVectors h K A H,
      IsPolynomialOn Ω (fun χ : Ω => b.val χ.val •
        compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val (hfull χ) w.val) := by
  have := finiteDimensional_compactFixedVectors h K hK A hadm H hHK
  have := finiteDimensional_leviFixedDual A hadm hM hH
  obtain ⟨b, hb, hpoly⟩ := exists_regular_bilinear_stableLimit_numerator
    (isPolynomialOn_compactCompression h hU hδ K hP hK hPK ν hν hr A hH hHK a hadm Ω)
    (isPolynomialOn_compactDualShift h hU ν A U' hMU' hI Ω)
  refine ⟨b, hb, fun w => ?_⟩
  rcases Ω.eq_empty_or_nonempty with hΩ | ⟨χ₁, hχ₁⟩
  · refine ⟨0, Fin.elim0, Fin.elim0, fun χ => ?_⟩
    have hχ : χ.val ∈ (∅ : Set (unramifiedCharacters ν)) := hΩ ▸ χ.property
    exact hχ.elim
  have hB := hpoly
    (compactTruncationForm h hU hδ K hP hK hPK ν hν hr A U' qν χ₁ (hfull ⟨χ₁, hχ₁⟩) hHK)
    (fun χ : Ω => compactLimitForm h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val (hfull χ) H)
    (fun χ w y => tendsto_compactTruncationForm h hU hδ K hP hK hPK ν hν hr A U' hMU' qν μU' μI
      hqν hM hH hHK hI χ₁ χ.val (hfull ⟨χ₁, hχ₁⟩) (hfull χ) w y)
  let j : fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup →ₗ[ℂ]
      Module.Dual ℂ (LeviFixedDual A H) :=
    { toFun := fun v =>
        { toFun := fun y => y.val v.val
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := fun _ _ => by
        ext y
        exact map_add y.val _ _
      map_smul' := fun _ _ => by
        ext y
        exact map_smul y.val _ _ }
  have hj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact leviFixedPairing_injective A hM hH v fun y => LinearMap.congr_fun hv y
  let Z : Ω → fixedVectors A.representation (leviPartOpen (M := M) H).toSubgroup := fun χ =>
    b.val χ.val • ⟨compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val (hfull χ)
      w.val, compactIdentityValue_mem_fixedVectors h hU hδ K hP hK hPK ν hν hr A U' hMU' qν μU' μI
        hqν hM hH hHK χ.val (hfull χ) w⟩
  have hZ : IsPolynomialOn Ω Z := by
    apply isPolynomialOn_of_linearMap_injective j hj
    have hw := hB.linearMap (LinearMap.applyₗ w)
    convert hw using 2 with χ
    ext y
    change y.val (b.val χ.val • compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val
      (hfull χ) w.val) = b.val χ.val * y.val (compactIdentityValue h hU hδ K hP hK hPK ν hν hr A
        U' qν hM χ.val (hfull χ) w.val)
    rw [map_smul, smul_eq_mul]
  exact hZ.linearMap (Submodule.subtype _)

end Convergence

end Langlands.Plancherel
