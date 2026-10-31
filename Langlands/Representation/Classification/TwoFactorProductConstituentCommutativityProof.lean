import Langlands.Representation.Filtration.FactorMatchingPullback
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Filtration.JordanHolderComparisonProof
import Langlands.Representation.Filtration.JordanHolderTransportProof
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.LocalField.Normalization.Proof

/-!
# Constituent commutativity of a product of two irreducible GL factors

Zelevinsky (1980), Theorem 1.9, for two irreducible factors. Pulling `π₁ × π₂`
back by the inverse transpose gives `θ*π₂ × θ*π₁`; Gelfand–Kazhdan and smooth
duality of normalized induction identify it with the smooth dual of `π₂ × π₁`.
The annihilator series of a composition series of `π₂ × π₁` and Gelfand–Kazhdan
on its factors then match its smooth dual with its own inverse-transpose
pullback, and pulling back once more gives the conclusion.
-/

noncomputable section

namespace Langlands.Classification.TwoFactorCommutativity

open LengthCriterionProof

universe uF uG uH uV uW

section FirstIso

variable {k : Type*} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- The first isomorphism theorem for the successive quotient `T / S`: an
intertwiner from `T` onto `σ` whose kernel is `S ∩ T` identifies `T / S` with `σ`. -/
def quotientRepEquiv (S T : Subrepresentation ρ)
    (α : T.toRepresentation.IntertwiningMap σ)
    (hker : ∀ x : T.toSubmodule, α x = 0 ↔ (x : V) ∈ S.toSubmodule)
    (hsurj : Function.Surjective α) :
    (quotientRep S T).Equiv σ := by
  have hle : lower S T ≤ LinearMap.ker α.toLinearMap := fun x hx =>
    LinearMap.mem_ker.mpr ((hker x).mpr hx)
  let Φ := (lower S T).liftQ α.toLinearMap hle
  have hΦ (x : T.toSubmodule) : Φ (Submodule.Quotient.mk x) = α x := rfl
  let Ψ : (quotientRep S T).IntertwiningMap σ :=
    { toLinearMap := Φ
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        change Φ (Submodule.Quotient.mk (T.toRepresentation g x)) =
          σ g (Φ (Submodule.Quotient.mk x))
        rw [hΦ, hΦ]
        exact Representation.IntertwiningMap.isIntertwining _ _ α g x }
  refine Ψ.ofBijective ⟨?_, ?_⟩
  · intro q r hqr
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ r
    change Φ (Submodule.Quotient.mk x) = Φ (Submodule.Quotient.mk y) at hqr
    rw [hΦ, hΦ] at hqr
    rw [Submodule.Quotient.eq]
    change ((x - y : T.toSubmodule) : V) ∈ S.toSubmodule
    apply (hker (x - y)).mp
    rw [map_sub, hqr, sub_self]
  · intro w
    obtain ⟨x, rfl⟩ := hsurj w
    exact ⟨Submodule.Quotient.mk x, rfl⟩

end FirstIso

section Dual

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- The smooth functionals vanishing on an invariant subspace. -/
def annihilator (S : Subrepresentation ρ) : Subrepresentation (smoothContragredient ρ) where
  toSubmodule :=
    { carrier := {ℓ | ∀ v ∈ S.toSubmodule, (ℓ : Module.Dual ℂ V) v = 0}
      add_mem' := by
        intro ℓ m hℓ hm v hv
        change (ℓ : Module.Dual ℂ V) v + (m : Module.Dual ℂ V) v = 0
        rw [hℓ v hv, hm v hv, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c ℓ hℓ v hv
        change c • (ℓ : Module.Dual ℂ V) v = 0
        rw [hℓ v hv, smul_zero] }
  apply_mem_toSubmodule g ℓ hℓ v hv := by
    change (ℓ : Module.Dual ℂ V) (ρ g⁻¹ v) = 0
    exact hℓ _ (S.apply_mem_toSubmodule g⁻¹ hv)

theorem mem_annihilator {S : Subrepresentation ρ} {ℓ : SmoothDual ρ} :
    ℓ ∈ (annihilator S).toSubmodule ↔ ∀ v ∈ S.toSubmodule, (ℓ : Module.Dual ℂ V) v = 0 :=
  Iff.rfl

theorem annihilator_antitone : Antitone (annihilator (ρ := ρ)) := by
  intro S T hST ℓ hℓ v hv
  exact hℓ v (hST hv)

theorem annihilator_bot : annihilator (⊥ : Subrepresentation ρ) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  ext ℓ
  refine ⟨fun _ => Submodule.mem_top, fun _ v hv => ?_⟩
  have hv0 : v = 0 := (Submodule.mem_bot ℂ).mp hv
  rw [hv0, map_zero]

theorem annihilator_top : annihilator (⊤ : Subrepresentation ρ) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  ext ℓ
  refine ⟨fun hℓ => ?_, fun hℓ => ?_⟩
  · change ℓ ∈ (⊥ : Submodule ℂ (SmoothDual ρ))
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact hℓ v Submodule.mem_top
  · change ℓ ∈ (⊥ : Submodule ℂ (SmoothDual ρ)) at hℓ
    rw [Submodule.mem_bot] at hℓ
    intro v _
    rw [hℓ]
    rfl

/-- The inclusion of an invariant subspace, as an intertwiner. -/
def subrepInclusion (T : Subrepresentation ρ) : T.toRepresentation.IntertwiningMap ρ where
  toLinearMap := T.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- The projection onto a successive quotient, as an intertwiner. -/
def quotientProjection (S T : Subrepresentation ρ) :
    T.toRepresentation.IntertwiningMap (quotientRep S T) where
  toLinearMap := (lower S T).mkQ
  isIntertwining' _ := rfl

omit [IsTopologicalGroup G] in
theorem isSmooth_toRepresentation (hρ : IsSmooth ρ) (T : Subrepresentation ρ) :
    IsSmooth T.toRepresentation := by
  intro x
  obtain ⟨K, hK⟩ := hρ x
  exact ⟨K, fun k => Subtype.ext (hK k)⟩

omit [IsTopologicalGroup G] in
theorem isSmooth_quotientRep (hρ : IsSmooth ρ) (S T : Subrepresentation ρ) :
    IsSmooth (quotientRep S T) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨K, hK⟩ := hρ x
  refine ⟨K, fun k => ?_⟩
  change Submodule.Quotient.mk (T.toRepresentation (k : G) x) = Submodule.Quotient.mk x
  congr 1
  exact Subtype.ext (hK k)

/-- Restriction of a smooth functional vanishing on `S` to the successive
quotient `T / S`; the result is again smooth. -/
def annihilatorRestrict (S T : Subrepresentation ρ) :
    (annihilator S).toRepresentation.IntertwiningMap
      (smoothContragredient (quotientRep S T)) where
  toFun ℓ :=
    ⟨(lower S T).liftQ (((ℓ : SmoothDual ρ) : Module.Dual ℂ V) ∘ₗ T.toSubmodule.subtype)
        (fun x hx => LinearMap.mem_ker.mpr (ℓ.property x hx)), by
      obtain ⟨K, hK⟩ := (ℓ : SmoothDual ρ).property
      refine ⟨K, fun k => ?_⟩
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (hK k) (x : V)⟩
  map_add' ℓ m := by
    apply Subtype.ext
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' c ℓ := by
    apply Subtype.ext
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    rfl
  isIntertwining' g := by
    apply LinearMap.ext
    intro ℓ
    apply Subtype.ext
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    rfl

theorem annihilatorRestrict_apply_mk (S T : Subrepresentation ρ)
    (ℓ : (annihilator S).toSubmodule) (x : T.toSubmodule) :
    ((annihilatorRestrict S T ℓ : SmoothDual (quotientRep S T)) :
        Module.Dual ℂ (T.toSubmodule ⧸ lower S T)) (Submodule.Quotient.mk x) =
      ((ℓ : SmoothDual ρ) : Module.Dual ℂ V) x := rfl

theorem annihilatorRestrict_eq_zero_iff (S T : Subrepresentation ρ)
    (ℓ : (annihilator S).toSubmodule) :
    annihilatorRestrict S T ℓ = 0 ↔ (ℓ : SmoothDual ρ) ∈ (annihilator T).toSubmodule := by
  constructor
  · intro h v hv
    have := congrArg (fun m : SmoothDual (quotientRep S T) =>
      (m : Module.Dual ℂ (T.toSubmodule ⧸ lower S T))
        (Submodule.Quotient.mk ⟨v, hv⟩)) h
    exact this
  · intro h
    apply Subtype.ext
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    exact h x x.property

theorem annihilatorRestrict_surjective (hcof : CompactOpenCofinal G) (hρ : IsSmooth ρ)
    {S T : Subrepresentation ρ} (hST : S ≤ T) :
    Function.Surjective (annihilatorRestrict S T) := by
  intro lam
  let μ := contragredientMap (quotientProjection S T) lam
  obtain ⟨ℓ, hℓ⟩ := contragredientMap_surjective_of_injective_of_compact_cofinal hcof
    (isSmooth_toRepresentation hρ T) hρ (subrepInclusion T) Subtype.val_injective μ
  have hval (x : T.toSubmodule) : (ℓ : Module.Dual ℂ V) x =
      (lam : Module.Dual ℂ (T.toSubmodule ⧸ lower S T)) (Submodule.Quotient.mk x) :=
    LinearMap.congr_fun (congrArg Subtype.val hℓ) x
  have hmem : ℓ ∈ (annihilator S).toSubmodule := by
    intro v hv
    rw [show v = ((⟨v, hST hv⟩ : T.toSubmodule) : V) from rfl, hval]
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (show (⟨v, hST hv⟩ : T.toSubmodule) ∈
      lower S T from hv), map_zero]
  refine ⟨⟨ℓ, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  exact hval x

/-- For `S ≤ T`, the successive quotient of annihilators is the smooth dual of
the successive quotient. -/
def annihilatorQuotientEquiv (hcof : CompactOpenCofinal G) (hρ : IsSmooth ρ)
    {S T : Subrepresentation ρ} (hST : S ≤ T) :
    (quotientRep (annihilator T) (annihilator S)).Equiv
      (smoothContragredient (quotientRep S T)) :=
  quotientRepEquiv (annihilator T) (annihilator S) (annihilatorRestrict S T)
    (annihilatorRestrict_eq_zero_iff S T) (annihilatorRestrict_surjective hcof hρ hST)

end Dual

section DualSeries

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Rep.{uV} ℂ G} {m : ℕ}

/-- The annihilator series of a finite filtration, indexed in reverse order. -/
def dualSeries (s : ObjectRepFiltration A m) :
    ObjectRepFiltration (Rep.of (smoothContragredient A.ρ)) m :=
  ObjectRepFiltration.ofSubrepresentations
    (fun j => annihilator (s.subrepresentation j.rev))
    (fun _ _ hij => annihilator_antitone
      (s.monotone_subrepresentation (Fin.rev_le_rev.mpr hij)))
    (by
      change annihilator (s.subrepresentation (Fin.last m)) = ⊥
      rw [s.subrepresentation_last]
      exact annihilator_top)
    (by
      change annihilator (s.subrepresentation (Fin.last m).rev) = ⊤
      rw [Fin.rev_last, s.subrepresentation_zero]
      exact annihilator_bot)

/-- The graded pieces of the annihilator series are the smooth duals of the
original graded pieces, in reverse order. -/
theorem dualSeries_graded (hcof : CompactOpenCofinal G) (hA : IsSmooth A.ρ)
    (s : ObjectRepFiltration A m) (j : Fin m) :
    Nonempty (((dualSeries s).gradedRepresentation j).ρ.Equiv
      (smoothContragredient (s.gradedRepresentation j.rev).ρ)) := by
  change Nonempty ((quotientRep (annihilator (s.subrepresentation j.castSucc.rev))
      (annihilator (s.subrepresentation j.succ.rev))).Equiv
    (smoothContragredient (quotientRep (s.subrepresentation j.rev.castSucc)
      (s.subrepresentation j.rev.succ))))
  rw [Fin.rev_castSucc, Fin.rev_succ]
  exact ⟨annihilatorQuotientEquiv hcof hA
    (s.monotone_subrepresentation (Fin.castSucc_lt_succ (i := j.rev)).le)⟩

end DualSeries

section Pullback

variable {k : Type*} [Field k] {G : Type uG} [Monoid G] {H : Type uH} [Monoid H]

/-- Pull back an equivalence of representations along a monoid homomorphism. -/
def equivComp {V : Type uV} [AddCommGroup V] [Module k V]
    {W : Type uW} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Langlands.FiniteTensor.FactorMatchingProof.equivComp e f

/-- Pulling back along `e` and then along `e.symm` returns the original action. -/
def compSymmEquiv {V : Type uV} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (e : G ≃* H) :
    Representation.Equiv ((ρ.comp e.symm.toMonoidHom).comp e.toMonoidHom) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl k V) (fun g => by
    apply LinearMap.ext
    intro v
    change ρ (e.symm (e g)) v = ρ g v
    rw [MulEquiv.symm_apply_apply])

/-- Matching composition factors survive pullback along a surjective homomorphism. -/
theorem haveSameJordanHolderFactors_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (f : H →* G) (hf : Function.Surjective f) (h : HaveSameJordanHolderFactors A B) :
    HaveSameJordanHolderFactors (Rep.of (A.ρ.comp f)) (Rep.of (B.ρ.comp f)) :=
  Langlands.FiniteTensor.FactorMatchingProof.matching_comp h f hf

/-- Matching composition factors can be detected after pullback along a group
automorphism. -/
theorem haveSameJordanHolderFactors_of_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (e : H ≃* G)
    (h : HaveSameJordanHolderFactors (Rep.of (A.ρ.comp e.toMonoidHom))
      (Rep.of (B.ρ.comp e.toMonoidHom))) :
    HaveSameJordanHolderFactors A B :=
  Langlands.FiniteTensor.FactorMatchingProof.matching_of_comp e h

end Pullback

section GeneralLinear

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The topology of the canonical normed-field structure of a p-adic field. -/
abbrev canonicalTopology : TopologicalSpace F.Carrier :=
  letI := F.canonicalNormedField
  inferInstance

/-- Gelfand–Kazhdan for a field topology equal to the canonical normed topology. -/
private theorem gelfandKazhdanOfTopology (t : TopologicalSpace F.Carrier)
    (ht : t = canonicalTopology F) (k : ℕ)
    [IsTopologicalGroup (GeneralLinear (k + 1) F.Carrier)]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) W) :
    IsAdmissible τ → Representation.IsIrreducible τ →
      Nonempty (Representation.Equiv (τ.comp (inverseTranspose (k + 1) F.Carrier).toMonoidHom)
        (smoothContragredient τ)) := by
  subst ht
  intro hadm hirr
  obtain ⟨E, hE⟩ := gelfandKazhdanContragredient.{uF, uW} p inferInstance F k W τ hadm hirr
  exact ⟨Representation.Equiv.mk E (fun g => LinearMap.ext (hE g))⟩

/-- Gelfand–Kazhdan for the topology of the supplied realization: pulling an
irreducible admissible representation back by inverse transpose gives its smooth
contragredient. -/
theorem gelfandKazhdan_inverseTranspose {m : ℕ} (hm : 0 < m)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear m F.Carrier) W) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    IsAdmissible τ → Representation.IsIrreducible τ →
      Nonempty (Representation.Equiv (τ.comp (inverseTranspose m F.Carrier).toMonoidHom)
        (smoothContragredient τ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + 1)
  exact gelfandKazhdanOfTopology F T.topology T.topology_eq_canonicalNormTopology k τ

/-- Irreducible smooth representations of `GL_m` are admissible. -/
theorem isAdmissible_of_isIrreducible {m : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear m F.Carrier) W) :
    letI := T.topology
    IsSmooth τ → Representation.IsIrreducible τ → IsAdmissible τ := by
  let := T.topology
  intro hs hirr
  exact (CuspidalSupport.cuspidalEmbedding.{uF, uW} F T m (SmoothRep.of τ hs) hirr).1

/-- Smooth duality for a normalized upper block product of admissible factors:
the product of the smooth duals is the smooth dual of the product. -/
theorem productSmoothDual {n : ℕ} (B : BlockShape n) {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    (∀ i, IsAdmissible (τ i)) →
    Nonempty ((T.normalizedProductInduced B (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (T.normalizedProductInduced B τ))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  intro hτ
  let := T.leviTopologicalGroup B
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor τ)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external τ hτ
  obtain ⟨EI, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 p F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap τ) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ τ,
      FiniteTensor.smoothDualTensorMap_surjective τ hτ
      (fun i => GeneralLinear.compactOpen_cofinal F T (B.size i))⟩
  let e2 : (FiniteTensor.external (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (FiniteTensor.external τ)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner τ).isIntertwining'
  exact ⟨((EI σ hσ).trans (T.normalizedParabolicInducedEquiv B e2.symm)).symm⟩

/-- The smooth dual of a finite-length smooth representation of `GL_n` and its
inverse-transpose pullback have the same composition factors. The annihilator
series of a composition series has graded pieces the smooth duals of the
original pieces in reverse order; Gelfand–Kazhdan identifies each of them with
the inverse-transpose pullback of that piece. -/
theorem haveSameJordanHolderFactors_dual_comp {n : ℕ} (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) W) :
    letI := T.topology
    IsSmooth ρ → ∀ {m : ℕ} (s : ObjectRepFiltration (Rep.of ρ) m), s.HasSimpleFactors →
    letI := T.generalLinearTopologicalGroup n
    HaveSameJordanHolderFactors (Rep.of (smoothContragredient ρ))
      (Rep.of (ρ.comp (inverseTranspose n F.Carrier).toMonoidHom)) := by
  let := T.topology
  intro hρ m s hs
  let := T.generalLinearTopologicalGroup n
  let θ := (inverseTranspose n F.Carrier).toMonoidHom
  have hθ : Function.Surjective θ := (inverseTranspose n F.Carrier).surjective
  have hcof := GeneralLinear.compactOpen_cofinal F T n
  -- Each original piece is equivalent, after inverse transpose, to its smooth dual.
  have hgk (j : Fin m) : Nonempty (Representation.Equiv ((s.gradedRepresentation j).ρ.comp θ)
      (smoothContragredient (s.gradedRepresentation j).ρ)) := by
    have hsm : IsSmooth (s.gradedRepresentation j).ρ :=
      isSmooth_quotientRep hρ (s.subrepresentation j.castSucc) (s.subrepresentation j.succ)
    exact gelfandKazhdan_inverseTranspose F T hn _
      (isAdmissible_of_isIrreducible F T _ hsm (hs j)) (hs j)
  have hdual (j : Fin m) : Nonempty (((dualSeries s).gradedRepresentation j).ρ.Equiv
      ((s.gradedRepresentation j.rev).ρ.comp θ)) := by
    obtain ⟨a⟩ := dualSeries_graded hcof hρ s j
    obtain ⟨b⟩ := hgk j.rev
    exact ⟨a.trans b.symm⟩
  refine ⟨m, dualSeries s, s.comp θ, fun j => ?_, fun j => ?_, Fin.revPerm, fun j => ?_⟩
  · obtain ⟨a⟩ := hdual j
    exact (isIrreducible_iff_of_equiv a).mpr
      ((CuspidalSupport.isIrreducible_comp_iff _ θ hθ).mpr (hs j.rev))
  · have := (CuspidalSupport.isIrreducible_comp_iff _ θ hθ).mpr (hs j)
    exact this
  · obtain ⟨a⟩ := hdual j
    exact ⟨a.trans (s.compGradedEquiv θ j.rev).symm⟩

end GeneralLinear

end Langlands.Classification.TwoFactorCommutativity

namespace Langlands.Classification

open GeneralLinear TwoFactorCommutativity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For a two-block shape, swapping the two adjacent labels is the reversal. -/
theorem adjacentSwap_zero_eq_revPerm {n : ℕ} (B : BlockShape n) (h₂ : B.length = 2) :
    B.adjacentSwap 0 (by omega) = Fin.revPerm := by
  ext i
  rcases i with ⟨i, hi⟩
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · simp [BlockShape.adjacentSwap, Fin.rev, h₂]
  · simp [BlockShape.adjacentSwap, Fin.rev, h₂]

/-- Ze80 Theorem 1.9 for two irreducible factors, given finite length of the
normalized products of irreducible factors. -/
theorem twoFactorProductConstituentCommutativity_of_finiteLength
    (hfl : IrreducibleProductFiniteLength.{uF, uV} F T) :
    TwoFactorProductConstituentCommutativity.{uF, uV} F T := by
  let := T.topology
  intro n B h₂ A hA σ
  have hσ : σ = Fin.revPerm := adjacentSwap_zero_eq_revPerm B h₂
  clear_value σ
  subst hσ
  have hn : 0 < n := by
    rw [← B.sum_eq]
    exact Finset.sum_pos (fun i _ => B.positive i)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let := T.generalLinearTopologicalGroup n
  let θ := inverseTranspose n F.Carrier
  let X := T.normalizedProductInduced B (fun i => (A i).representation)
  let Y := T.normalizedProductInduced B.reverse (V := fun i => A i.rev)
    (fun i => (A i.rev).representation)
  let Y' := T.normalizedProductInduced (B.permute Fin.revPerm)
    (V := fun i => A (Fin.revPerm i)) (fun i => (A (Fin.revPerm i)).representation)
  change HaveSameJordanHolderFactors (Rep.of X) (Rep.of Y')
  -- `Y'` is definitionally the product over the reversed shape.
  have hYY : Representation.Equiv Y Y' := Representation.Equiv.refl Y
  have hAdm (i : Fin B.length) : IsAdmissible (A i).representation :=
    isAdmissible_of_isIrreducible F T _ (A i).isSmooth (hA i)
  -- Pull `X` back by inverse transpose: this is the smooth dual of `Y`.
  obtain ⟨E1⟩ := Parabolic.normalizedProductInverseTranspose T n hn B (fun i => ↥(A i))
    (fun i => (A i).representation) (fun i => (A i).isSmooth)
  have hgk (i : Fin B.reverse.length) := gelfandKazhdan_inverseTranspose F T
    (B.positive i.rev) (A i.rev).representation (hAdm i.rev) (hA i.rev)
  let E2 := T.normalizedProductInducedEquiv B.reverse (fun i => Classical.choice (hgk i))
  obtain ⟨E3⟩ := productSmoothDual F T B.reverse (fun i => (A i.rev).representation)
    (fun i => hAdm i.rev)
  let E : Representation.Equiv (X.comp θ.toMonoidHom) (smoothContragredient Y) :=
    E1.trans (E2.trans E3)
  -- A composition series of `Y`.
  have hY : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) Y.asModule :=
    hfl n hn B.reverse (fun i => A i.rev) (fun i => hA i.rev)
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hY
  obtain ⟨t, ht⟩ := LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries
    (A := Rep.of Y) c h₀ h₁
  have hdual := haveSameJordanHolderFactors_dual_comp F T hn Y
    (T.isSmooth_normalizedProductInduced B.reverse _) t ht
  have hcomp : HaveSameJordanHolderFactors (Rep.of (X.comp θ.toMonoidHom))
      (Rep.of (Y.comp θ.toMonoidHom)) :=
    haveSameJordanHolderFactors_transport hdual E.symm (Representation.Equiv.refl _)
  have hXY : HaveSameJordanHolderFactors (Rep.of X) (Rep.of Y) :=
    haveSameJordanHolderFactors_of_comp θ hcomp
  exact haveSameJordanHolderFactors_transport hXY (Representation.Equiv.refl _) hYY

/-- Ze80 Theorem 1.9 for two irreducible factors: `π₁ × π₂` and `π₂ × π₁` have
the same Jordan–Hölder factors. -/
theorem twoFactorProductConstituentCommutativity :
    TwoFactorProductConstituentCommutativity.{uF, uV} F T :=
  twoFactorProductConstituentCommutativity_of_finiteLength F T
    (irreducibleProductFiniteLength.{uF, uV} F T)

end Langlands.Classification
