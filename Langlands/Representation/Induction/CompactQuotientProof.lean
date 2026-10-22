import Langlands.Representation.Induction.StructuralStatement

/-!
# Smooth induction from a subgroup with compact coset space

When `P \ G` is compact, every smooth induced function has compact projected
support, so compact and smooth induction coincide. The vectors fixed by an open
subgroup `K` embed, by evaluation at finitely many double-coset
representatives, into a finite product of fixed-vector spaces of the inducing
representation.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uV

section General

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

omit [IsTopologicalGroup G] in
/-- Covariance of a smooth induced function under left multiplication by `P`. -/
theorem eval_covariant (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) (p : P) (x : G) :
    eval P σ f ((p : G) * x) = σ p (eval P σ f x) :=
  f.1.2 p x

/-- A vector of smooth induction fixed by `K` is right-`K`-invariant as a function. -/
theorem eval_mul_of_mem_fixedVectors (P : Subgroup G) (σ : Representation R P V)
    (K : Subgroup G) {f : SmoothFunctions P σ}
    (hf : f ∈ fixedVectors (smoothInduced P σ) K) (k : K) (x : G) :
    eval P σ f (x * (k : G)) = eval P σ f x :=
  congrArg (fun F : SmoothFunctions P σ => eval P σ F x) (hf k)

/-- Smooth induced functions are locally constant. -/
theorem eval_isLocallyConstant (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) : IsLocallyConstant (eval P σ f) := by
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set G),
    isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (fun F : EquivariantFunctions P σ => F.1 x) (hK ⟨k, hk⟩)

omit [IsTopologicalGroup G] in
/-- By covariance, the projected support pulls back to the actual support. -/
theorem quotientMap_preimage_quotientSupport (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) :
    quotientMap P ⁻¹' quotientSupport P (eval P σ f) = Function.support (eval P σ f) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩ hx
    have hp : y * x⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
    have h := eval_covariant P σ f ⟨y * x⁻¹, hp⟩ x
    rw [hx, map_zero] at h
    exact hy (by simpa using h)
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The projected support of a smooth induced function is closed in `P \ G`. -/
theorem isClosed_quotientSupport (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) : IsClosed (quotientSupport P (eval P σ f)) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
  change IsClosed (quotientMap P ⁻¹' quotientSupport P (eval P σ f))
  rw [quotientMap_preimage_quotientSupport]
  exact (eval_isLocallyConstant P σ f).isOpen_fiber 0 |>.isClosed_compl

/-- With a compact coset space, the inclusion of compact induction into smooth
induction is bijective. -/
theorem compactInclusion_bijective_of_compactSpace (P : Subgroup G)
    (σ : Representation R P V) [CompactSpace (LeftQuotient P)] :
    Function.Bijective (compactInclusion P σ) :=
  ⟨Subtype.val_injective,
    fun f => ⟨⟨f, (isClosed_quotientSupport P σ f).isCompact⟩, rfl⟩⟩

/-- A compact coset space `P \ G` is covered by finitely many double cosets
`P * i * K` of an open subgroup `K`. -/
theorem exists_finset_doubleCoset_cover (P : Subgroup G) [CompactSpace (LeftQuotient P)]
    (K : OpenSubgroup G) :
    ∃ t : Finset G, ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k := by
  have hopen : IsOpenMap (quotientMap P) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : G => quotientMap P '' ((fun k => i * k) '' (K : Set G)))
    (fun i => hopen _ (isOpenMap_mul_left i _ K.isOpen))
    (by
      intro y _
      induction y using Quotient.inductionOn with
      | h x => exact Set.mem_iUnion.mpr ⟨x, x, ⟨1, K.one_mem, mul_one x⟩, rfl⟩)
  refine ⟨t, fun x => ?_⟩
  have hx := ht (Set.mem_univ (quotientMap P x))
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _, ⟨k, hk, rfl⟩, hy⟩ := hx
  have hp : x * (i * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hy)
  exact ⟨i, hi, _, hp, k, hk, by simp [mul_assoc]⟩

/-- The open subgroup `P ∩ i K i⁻¹` of `P`, consisting of the `p` with
`i⁻¹ * p * i ∈ K`. -/
def conjOpenSubgroup (P : Subgroup G) (K : OpenSubgroup G) (i : G) : OpenSubgroup P :=
  K.comap ((MulAut.conj i⁻¹).toMonoidHom.comp P.subtype)
    ((IsTopologicalGroup.continuous_conj i⁻¹).comp continuous_subtype_val)

theorem mem_conjOpenSubgroup {P : Subgroup G} {K : OpenSubgroup G} {i : G} {p : P} :
    p ∈ conjOpenSubgroup P K i ↔ i⁻¹ * (p : G) * i ∈ K := by
  simp [conjOpenSubgroup]

/-- The value at `i` of a `K`-fixed smooth induced function is fixed by `P ∩ i K i⁻¹`. -/
theorem eval_mem_fixedVectors (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (i : G) {f : SmoothFunctions P σ}
    (hf : f ∈ fixedVectors (smoothInduced P σ) K.toSubgroup) :
    eval P σ f i ∈ fixedVectors σ (conjOpenSubgroup P K i).toSubgroup := by
  intro p
  have hp : i⁻¹ * ((p : P) : G) * i ∈ K := mem_conjOpenSubgroup.mp p.property
  change σ (p : P) (eval P σ f i) = eval P σ f i
  rw [← eval_covariant]
  calc eval P σ f (((p : P) : G) * i) = eval P σ f (i * (i⁻¹ * ((p : P) : G) * i)) := by
        simp [mul_assoc]
    _ = eval P σ f i := eval_mul_of_mem_fixedVectors P σ K.toSubgroup hf ⟨_, hp⟩ i

/-- Evaluation of `K`-fixed smooth induced functions at the points of `t`. -/
def fixedEvaluation (P : Subgroup G) (σ : Representation R P V) (K : OpenSubgroup G)
    (t : Finset G) :
    fixedVectors (smoothInduced P σ) K.toSubgroup →ₗ[R]
      ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) where
  toFun f i := ⟨eval P σ f.1 i, eval_mem_fixedVectors P σ K i f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation at representatives of a finite double-coset cover is injective on
`K`-fixed functions. -/
theorem fixedEvaluation_injective (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (t : Finset G)
    (ht : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k) :
    Function.Injective (fixedEvaluation P σ K t) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨i, hi, p, hp, k, hk, rfl⟩ := ht x
  have h0 : eval P σ f.1 i = 0 := congrArg Subtype.val (congrFun hf ⟨i, hi⟩)
  change eval P σ f.1 (p * i * k) = 0
  rw [eval_mul_of_mem_fixedVectors P σ K.toSubgroup f.2 ⟨k, hk⟩,
    eval_covariant P σ f.1 ⟨p, hp⟩, h0, map_zero]

/-- Over a Noetherian ring, smooth induction of an admissible representation
from a subgroup with compact coset space is admissible. -/
theorem smoothInduced_isAdmissible_of_compactSpace [IsNoetherianRing R] (P : Subgroup G)
    (σ : Representation R P V) [CompactSpace (LeftQuotient P)] (hσ : IsAdmissible σ) :
    IsAdmissible (smoothInduced P σ) := by
  refine ⟨smoothInduced_smooth P σ, fun K => ?_⟩
  obtain ⟨t, ht⟩ := exists_finset_doubleCoset_cover P K
  have : ∀ i : t, Module.Finite R (fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :=
    fun i => hσ.2 _
  exact Module.Finite.of_injective (fixedEvaluation P σ K t)
    (fixedEvaluation_injective P σ K t ht)

end General

/-- The compact-quotient clause: with `H \ G` compact and `sigma` admissible,
compact and smooth induction coincide and smooth induction is admissible. -/
theorem compactQuotientClause_holds {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [IsTopologicalGroup G] (H : Subgroup G) :
    CompactQuotientClause (V := V) H := by
  intro sigma _ hsigma
  exact ⟨compactInclusion_bijective_of_compactSpace H sigma,
    smoothInduced_isAdmissible_of_compactSpace H sigma hsigma⟩

end Langlands.Induction
