import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.Weil.Representation.CharacterLine
import Mathlib.LinearAlgebra.Trace
import Langlands.LocalFactor.CommonClosure

/-! # Trace characters of exact virtual representations and induced lines -/

noncomputable section

universe uG uV uA uB uC uF

namespace Langlands.LocalFactor.BrauerKernel

/-- The trace of a block upper-triangular matrix is the sum of the diagonal traces. -/
theorem matrix_trace_fromBlocks {R m n : Type*} [AddCommMonoid R] [Fintype m] [Fintype n]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

section Invariant

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Module.Basis in
/-- Trace additivity along an invariant subspace and its quotient. -/
theorem trace_eq_trace_restrict_add_trace_mapQ (W : Submodule K V) (e : V →ₗ[K] V)
    (he : W ≤ W.comap e) :
    LinearMap.trace K V e =
      LinearMap.trace K W (e.restrict he) + LinearMap.trace K (V ⧸ W) (W.mapQ W e he) := by
  let m := Module.Free.ChooseBasisIndex K W
  let bW : Module.Basis m K W := Module.Free.chooseBasis K W
  let n := Module.Free.ChooseBasisIndex K (V ⧸ W)
  let bQ : Module.Basis n K (V ⧸ W) := Module.Free.chooseBasis K (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m K := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n K := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n K := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [LinearMap.trace_eq_matrix_trace K b, this, matrix_trace_fromBlocks,
      ← LinearMap.trace_eq_matrix_trace K bW, ← LinearMap.trace_eq_matrix_trace K bQ]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

end Invariant

section Exact

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {U : Type uB} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  {T : Type uC} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G U} {τ : Representation ℂ G T}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ T] in
/-- Trace additivity for an actual short exact sequence of representations. -/
theorem exactSequence_trace
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (w : G) :
    LinearMap.trace ℂ U (σ w) = LinearMap.trace ℂ V (ρ w) + LinearMap.trace ℂ T (τ w) := by
  let W := LinearMap.ker g.toLinearMap
  have hW : W ≤ W.comap (σ w) := by
    intro u hu
    change g (σ w u) = 0
    change g u = 0 at hu
    rw [g.isIntertwining, hu, map_zero]
  let eV : V ≃ₗ[ℂ] W := (LinearEquiv.ofInjective f.toLinearMap hf).trans
    (LinearEquiv.ofEq _ _ hfg)
  have eV_apply (v : V) : (eV v : U) = f v := rfl
  have hconjV : eV.conj (ρ w) = (σ w).restrict hW := by
    ext x
    change (eV (ρ w (eV.symm x)) : U) = σ w (x : U)
    rw [eV_apply, f.isIntertwining, ← eV_apply, eV.apply_symm_apply]
  have htrV : LinearMap.trace ℂ W ((σ w).restrict hW) = LinearMap.trace ℂ V (ρ w) := by
    rw [← hconjV, LinearMap.trace_conj']
  let eT : (U ⧸ W) ≃ₗ[ℂ] T := g.toLinearMap.quotKerEquivOfSurjective hg
  have hconjT : eT.conj (W.mapQ W (σ w) hW) = τ w := by
    ext t
    obtain ⟨u, rfl⟩ := hg t
    change eT (W.mapQ W (σ w) hW (eT.symm (g u))) = τ w (g u)
    have heT : eT.symm (g u) = W.mkQ u :=
      g.toLinearMap.quotKerEquivOfSurjective_symm_apply hg u
    rw [heT]
    exact Representation.IntertwiningMap.isIntertwining σ τ g w u
  have htrT : LinearMap.trace ℂ (U ⧸ W) (W.mapQ W (σ w) hW) = LinearMap.trace ℂ T (τ w) := by
    rw [← hconjT, LinearMap.trace_conj']
  rw [trace_eq_trace_restrict_add_trace_mapQ W (σ w) hW, htrV, htrT]

end Exact

section Monomial

variable {K M Q : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [Fintype Q] [DecidableEq Q]

/-- The trace of a monomial operator on functions on a finite set. -/
theorem trace_monomial (σ : Q → Q) (B : Q → Module.End K M) (T : Module.End K (Q → M))
    (hT : ∀ v q, T v q = B q (v (σ q))) :
    LinearMap.trace K (Q → M) T = ∑ q, if σ q = q then LinearMap.trace K M (B q) else 0 := by
  have hT' : T = ∑ q, T ∘ₗ (LinearMap.single K (fun _ => M) q ∘ₗ LinearMap.proj q) := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval]
    rw [← map_sum]
    congr 1
    simp only [LinearMap.coe_single]
    exact (Finset.univ_sum_single v).symm
  rw [hT', map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  have hblock : (LinearMap.proj q : (Q → M) →ₗ[K] M) ∘ₗ T ∘ₗ
      LinearMap.single K (fun _ => M) q = if σ q = q then B q else 0 := by
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single, hT]
    split_ifs with h
    · rw [h, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero, LinearMap.zero_apply]
  rw [hblock]
  split_ifs <;> simp

end Monomial

end Langlands.LocalFactor.BrauerKernel

namespace Langlands.FiniteRepresentation

open LocalFactor.BrauerKernel

variable {G : Type uG} [Group G]

/-- The actual trace character of a finite-dimensional complex representation. -/
def traceFunction (A : FiniteRepresentation.{0, uG, uV} ℂ G) : G → ℂ :=
  fun g => LinearMap.trace ℂ A (A.representation g)

theorem traceFunction_apply (A : FiniteRepresentation.{0, uG, uV} ℂ G) (g : G) :
    traceFunction A g = LinearMap.trace ℂ A (A.representation g) := rfl

/-- Genuine equivalence preserves the trace character. -/
theorem traceFunction_eq_of_equiv {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G} (e : Equiv A B) :
    traceFunction A = traceFunction B := by
  funext g
  change LinearMap.trace ℂ A (A.representation g) = LinearMap.trace ℂ B (B.representation g)
  have hc : e.toLinearMap ∘ₗ A.representation g ∘ₗ e.symm.toLinearMap =
      B.representation g := by
    ext b
    simpa using Representation.IntertwiningMap.isIntertwining _ _
      e.toIntertwiningMap g (e.symm b)
  rw [← hc]
  exact (LinearMap.trace_conj' (A.representation g) e.toLinearEquiv).symm

/-- The trace character on genuine isomorphism classes. -/
def traceFunctionClass : IsomorphismClasses.{0, uG, uV} ℂ G → (G → ℂ) :=
  Quotient.lift traceFunction (fun _ _ ⟨e⟩ => traceFunction_eq_of_equiv e)

/-- Trace characters are additive in actual short exact sequences. -/
theorem traceFunction_shortExact
    {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    {C : FiniteRepresentation.{0, uG, uC} ℂ G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) :
    traceFunction B = traceFunction A + traceFunction C := by
  funext w
  exact exactSequence_trace f g h.1 h.2.1 h.2.2 w

/-- The trace character of a character line is the character. -/
theorem traceFunction_characterLine (χ : G →* ℂˣ) :
    traceFunction (characterLine.{uG, uV} χ) = fun g => (χ g : ℂ) := by
  funext g
  change LinearMap.trace ℂ (ULift.{uV} ℂ) ((χ g : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- Restriction precomposes the trace character. -/
theorem traceFunction_restrict {H : Type uB} [Group H] (φ : H →* G)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    traceFunction (restrict φ A) = traceFunction A ∘ φ := rfl

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Classical in
/-- The Frobenius formula for the trace of actual finite-index induction. The sum is
over right cosets `S q.out` fixed by right multiplication by `g`. -/
theorem traceFunction_induce (S : Subgroup G) [S.FiniteIndex]
    (A : FiniteRepresentation.{0, uG, uV} ℂ S) (g : G) :
    traceFunction (induce S A) g =
      ∑ q : Induction.Cosets S,
        if Induction.coset S (q.out * g) = q then
          traceFunction A (Induction.factor S (q.out * g))
        else 0 := by
  let e := Induction.coordinates S A
  have hT : ∀ v q, e.conj ((induce S A).representation g) v q =
      A.representation (Induction.factor S (q.out * g)) (v (Induction.coset S (q.out * g))) := by
    intro v q
    rfl
  calc traceFunction (induce S A) g
      = LinearMap.trace ℂ (Induction.Cosets S → A) (e.conj ((induce S A).representation g)) :=
        (LinearMap.trace_conj' ((induce S A).representation g) e).symm
    _ = _ := trace_monomial _ _ _ hT

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

section General

variable {G : Type uG} [Group G] (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)

/-- The trace character of a genuine class with the supplied property. -/
def classTrace (c : IsomorphismClassesWith P) : G → ℂ :=
  traceFunctionClass (forgetPropertyClass P c)

theorem classTrace_isExactAdditive : IsExactAdditive P (classTrace P) := by
  intro A B C f g h
  exact traceFunction_shortExact h

/-- The trace character on the actual exact virtual group. -/
def trace : ExactGrothendieckGroup P →ₗ[ℤ] (G → ℂ) :=
  lift P (classTrace P) (classTrace_isExactAdditive P)

@[simp]
theorem trace_ofRepresentation (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    trace P (ofRepresentation P A) = traceFunction A.val :=
  lift_ofRepresentation P _ _ A

end General

section Continuous

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The trace character of a continuous character line is the character. -/
@[simp]
theorem trace_characterClass (χ : G →ₜ* ℂˣ) :
    trace (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
        (characterClass.{uG, uV} χ) = fun g => (χ g : ℂ) := by
  rw [characterClass, trace_ofRepresentation, traceFunction_characterLine]
  rfl

end Continuous

section Restriction

variable {G : Type uG} {H : Type uB} [Group G] [Group H]
  (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)
  (Q : FiniteRepresentation.{0, uB, uV} ℂ H → Prop)

/-- Restriction precomposes the trace character. -/
theorem trace_restrict (φ : H →* G)
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A))
    (x : ExactGrothendieckGroup P) :
    trace Q (restrict φ P Q hPQ x) = trace P x ∘ φ := by
  have hl : (trace Q).comp (restrict φ P Q hPQ) =
      (LinearMap.funLeft ℤ ℂ φ).comp (trace P) := by
    apply hom_ext P
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change trace Q (restrict φ P Q hPQ (ofRepresentation P A)) =
        trace P (ofRepresentation P A) ∘ φ
      rw [restrict_ofRepresentation, trace_ofRepresentation, trace_ofRepresentation]
      rfl
  exact LinearMap.congr_fun hl x

end Restriction

section Induction

variable {G : Type uG} [Group G] (S : Subgroup G) [S.FiniteIndex]
  (P : FiniteRepresentation.{0, uG, uV} ℂ S → Prop)
  (Q : FiniteRepresentation.{0, uG, max uG uV} ℂ G → Prop)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Classical in
/-- The Frobenius sum at `g`, as an integer-linear functional on functions on `S`. -/
def frobeniusFunctional (g : G) : (S → ℂ) →ₗ[ℤ] ℂ :=
  ∑ q : FiniteRepresentation.Induction.Cosets S,
    if FiniteRepresentation.Induction.coset S (q.out * g) = q then
      (LinearMap.proj (FiniteRepresentation.Induction.factor S (q.out * g)) :
        (S → ℂ) →ₗ[ℤ] ℂ)
    else 0

open Classical in
theorem frobeniusFunctional_apply (g : G) (f : S → ℂ) :
    frobeniusFunctional S g f =
      ∑ q : FiniteRepresentation.Induction.Cosets S,
        if FiniteRepresentation.Induction.coset S (q.out * g) = q then
          f (FiniteRepresentation.Induction.factor S (q.out * g))
        else 0 := by
  rw [frobeniusFunctional, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> rfl

/-- The Frobenius formula on the actual exact virtual group. -/
theorem trace_induce (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (x : ExactGrothendieckGroup P) (g : G) :
    trace Q (induce S P Q hPQ x) g = frobeniusFunctional S g (trace P x) := by
  have hl : (LinearMap.proj g : (G → ℂ) →ₗ[ℤ] ℂ).comp ((trace Q).comp (induce S P Q hPQ)) =
      (frobeniusFunctional S g).comp (trace P) := by
    apply hom_ext P
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change trace Q (induce S P Q hPQ (ofRepresentation P A)) g =
        frobeniusFunctional S g (trace P (ofRepresentation P A))
      rw [induce_ofRepresentation, trace_ofRepresentation, trace_ofRepresentation,
        frobeniusFunctional_apply, traceFunction_induce]
  exact LinearMap.congr_fun hl x

end Induction

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The Frobenius formula for actual common-closure induction. -/
theorem trace_induce (E L : Extension F) (h : E.field ≤ L.field)
    (x : Virtual.{uF, uV} F L) (w : weilSubgroup F E) :
    ExactGrothendieckGroup.trace (ContinuousPredicate F E) (induce F E L h x) w =
      ExactGrothendieckGroup.frobeniusFunctional
        ((weilSubgroup F L).subgroupOf (weilSubgroup F E)) w
        (ExactGrothendieckGroup.trace (ContinuousPredicate F L) x ∘
          (nestedWeilEquiv F E L h)) := by
  rw [induce, LinearMap.comp_apply, ExactGrothendieckGroup.trace_induce,
    ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.trace_restrict]
  rfl

end Langlands.LocalFactor.CommonClosure
