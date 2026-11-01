import Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
import Langlands.Group.GL.CompactOpen

/-!
# The `Ψ⁻` clause of BZ77 Proposition 4.13(c)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV uW uW'

/-! ## Generic transport lemmas -/

section Generic

/-- A compact open subgroup basis at the identity transports along an isomorphism of
topological groups. -/
theorem compactOpenBasis_of_continuousMulEquiv {X Y : Type*} [Group X] [TopologicalSpace X]
    [Group Y] [TopologicalSpace Y] (e : X ≃ₜ* Y)
    (hY : ∀ O : Set Y, IsOpen O → (1 : Y) ∈ O →
      ∃ U : OpenSubgroup Y, IsCompact (U : Set Y) ∧ (U : Set Y) ⊆ O) :
    ∀ O : Set X, IsOpen O → (1 : X) ∈ O →
      ∃ U : OpenSubgroup X, IsCompact (U : Set X) ∧ (U : Set X) ⊆ O := by
  intro O hO h1
  obtain ⟨U, hU, hUO⟩ := hY (e.symm ⁻¹' O) (hO.preimage e.symm.continuous)
    (by simpa using h1)
  refine ⟨OpenSubgroup.comap e.toMonoidHom e.continuous U,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hU, ?_⟩
  intro x hx
  have h := hUO hx
  change e.symm (e x) ∈ O at h
  simpa only [e.symm_apply_apply] using h

/-- A cover by compact open subgroups transports along an isomorphism of topological
groups. -/
theorem compactOpenCover_of_continuousMulEquiv {X Y : Type*} [Group X] [TopologicalSpace X]
    [Group Y] [TopologicalSpace Y] (e : X ≃ₜ* Y)
    (hY : ∀ y : Y, ∃ U : OpenSubgroup Y, IsCompact (U : Set Y) ∧ y ∈ U) :
    ∀ x : X, ∃ U : OpenSubgroup X, IsCompact (U : Set X) ∧ x ∈ U := by
  intro x
  obtain ⟨U, hU, hx⟩ := hY (e x)
  exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous U,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hU, hx⟩

/-- Restrictions along equal homomorphisms are equivalent through the identity. -/
def compEquivOfEq {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {φ ψ : H →* G} (h : φ = ψ) :
    Representation.Equiv (ρ.comp φ) (ρ.comp ψ) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => LinearMap.ext fun v => by
    change ρ (φ g) v = ρ (ψ g) v
    rw [h])

@[simp] theorem compEquivOfEq_apply {G H V : Type*} [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) {φ ψ : H →* G} (h : φ = ψ) (v : V) :
    compEquivOfEq ρ h v = v := rfl

open Induction in
/-- Multiplication by a character commutes with compact induction of coefficient maps. -/
theorem compactInductionTwistEquiv_natural {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (H : Subgroup G) (chi : SmoothCharacter ℂ G) {σ : Representation ℂ H V}
    {τ : Representation ℂ H W} (c : σ.IntertwiningMap τ) (u : CompactFunctions H σ) :
    compactInductionTwistEquiv H chi τ (compactInducedMap H c u) =
      compactInducedMap H (twistIntertwining (chi.toMonoidHom.comp H.subtype) c)
        (compactInductionTwistEquiv H chi σ u) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (chi.toMonoidHom x : ℂ) • c (eval H σ u.1 x) = c ((chi.toMonoidHom x : ℂ) • eval H σ u.1 x)
  rw [map_smul]

/-- Naturality of a composite of four maps from the naturality of each step. -/
theorem chain_natural₄ {α₁ α₂ β₁ β₂ γ₁ γ₂ δ₁ δ₂ ε₁ ε₂ : Sort*}
    {S₁ : α₁ → β₁} {S₂ : α₂ → β₂} {T₁ : β₁ → γ₁} {T₂ : β₂ → γ₂} {C₁ : γ₁ → δ₁}
    {C₂ : γ₂ → δ₂} {R₁ : δ₁ → ε₁} {R₂ : δ₂ → ε₂} {a : α₁ → α₂} {b : β₁ → β₂}
    {c : γ₁ → γ₂} {d : δ₁ → δ₂} {e : ε₁ → ε₂} (x : α₁)
    (h₁ : S₂ (a x) = b (S₁ x)) (h₂ : T₂ (b (S₁ x)) = c (T₁ (S₁ x)))
    (h₃ : C₂ (c (T₁ (S₁ x))) = d (C₁ (T₁ (S₁ x))))
    (h₄ : R₂ (d (C₁ (T₁ (S₁ x)))) = e (R₁ (C₁ (T₁ (S₁ x))))) :
    R₂ (C₂ (T₂ (S₂ (a x)))) = e (R₁ (C₁ (T₁ (S₁ x)))) := by
  rw [h₁, h₂, h₃, h₄]

end Generic

/-! ## `Ψ⁻` as coinvariants under the kernel of the projection -/

section Localization

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `Ψ⁻A` is the coinvariant quotient of `A` by `ker projection = V_(n+1)`, with `GL_n`
acting through `diag(g, 1)` and twisted by `|det|^(-1/2)`. -/
def psiMinusCoinvariantsEquiv (T : F.TopologicalData) (n : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    ((Mirabolic.psiMinus T n).obj A).representation.Equiv
      (twist (Mirabolic.psiMinusCharacter T n)
        ((A.representation.toCoinvariants (projection (n := n) (F := F.Carrier)).ker).comp
          (levi (n := n) (F := F.Carrier)))) :=
  letI := T.topology
  Representation.Equiv.mk (Submodule.quotEquivOfEq _ _
    ((relations_congr A.representation (ker_projection (n := n) (F := F.Carrier)).symm 1 1
      fun _ => rfl).trans (Jacquet.Localization.relations_one A.representation _)))
    (fun g => LinearMap.ext fun x => by
      obtain ⟨v, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T n A x
      rfl)

/-- The identification sends the class of `v` to its class. -/
theorem psiMinusCoinvariantsEquiv_mk (T : F.TopologicalData) (n : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
    (v : letI := T.topology; A) :
    letI := T.topology
    psiMinusCoinvariantsEquiv T n A (Mirabolic.psiMinusQuotient T n A v) =
      Representation.Coinvariants.mk _ v := rfl

/-- The identification is natural, stated on the coinvariant quotient. -/
theorem psiMinusCoinvariantsEquiv_natural_quotient (T : F.TopologicalData) (n : ℕ)
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
    (f : letI := T.topology; A ⟶ A')
    (x : letI := T.topology; Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1) :
    letI := T.topology
    psiMinusCoinvariantsEquiv T n A' (SmoothRep.hom ((Mirabolic.psiMinus T n).map f) x) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (SmoothRep.hom f) (projection (n := n) (F := F.Carrier)).ker)
        (psiMinusCoinvariantsEquiv T n A x) := by
  let _ := T.topology
  exact Submodule.Quotient.induction_on _ x fun _ => rfl

/-- The identification is natural. -/
theorem psiMinusCoinvariantsEquiv_natural (T : F.TopologicalData) (n : ℕ)
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
    (f : letI := T.topology; A ⟶ A') (x : letI := T.topology; (Mirabolic.psiMinus T n).obj A) :
    letI := T.topology
    psiMinusCoinvariantsEquiv T n A' (SmoothRep.hom ((Mirabolic.psiMinus T n).map f) x) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (SmoothRep.hom f) (projection (n := n) (F := F.Carrier)).ker)
        (psiMinusCoinvariantsEquiv T n A x) :=
  psiMinusCoinvariantsEquiv_natural_quotient T n f x

end Localization

/-! ## Transport from `K` to the binary parabolic -/

section Transport

/-- The rank cast `GL_(m+r) ≃ GL_(r+m)` as an isomorphism of topological groups. -/
def rightPsiCastContinuous (m r : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] :
    GeneralLinear (m + r) R ≃ₜ* GeneralLinear (r + m) R where
  toMulEquiv := rightPsiCast m r R
  continuous_toFun := continuous_rightPsiCast
  continuous_invFun := (reindexContinuous (R := R) (finCongr (Nat.add_comm m r))).symm.continuous

theorem rightPsiCastContinuous_toMonoidHom (m r : ℕ) (R : Type*) [CommRing R]
    [TopologicalSpace R] :
    (rightPsiCastContinuous m r R).toMonoidHom = generalLinearCastHom (Nat.add_comm r m) :=
  MonoidHom.ext fun g => rightPsiCast_eq g

theorem mem_rightPsi_iff {R : Type*} [CommRing R] [TopologicalSpace R] {m r : ℕ}
    (hr : 0 < r) (hm : 0 < m) (h : GeneralLinear (m + r) R) :
    h ∈ (rightPsiStages (R := R) hr hm).comap (levi (n := m + r) (F := R)) ↔
      rightPsiCastContinuous m r R h ∈ (BlockShape.binary r m hr hm).parabolic R :=
  levi_mem_rightPsiStages_iff hr hm h

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The coefficient identification transported to the block tensor is equivariant. -/
theorem rightPsi_transport_equivariant (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (κ : Representation ℂ
      ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (l : (rightPsiStages (R := F.Carrier) hr hm).comap
        (levi (n := m + r) (F := F.Carrier))) (w : W),
      e (κ l w) = (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
          ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
        TensorProduct.map (X.1.representation (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
          (X.2.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l))) (e w)) :
    letI := T.topology
    ∀ (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
      (w : W),
      (e.trans (T.binaryPositiveTensorEquiv hr hm X).symm) (κ l w) =
        T.binaryPositiveCoefficient hr hm X
          ⟨rightPsiCastContinuous m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩
          ((e.trans (T.binaryPositiveTensorEquiv hr hm X).symm) w) := by
  let _ := T.topology
  intro l w
  apply (T.binaryPositiveTensorEquiv hr hm X).injective
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    PadicField.TopologicalData.binaryPositiveCoefficient_tensor, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, he]
  rfl

/-- Compact induction from `K = P.comap levi` of a coefficient identified with
`δ^(1/2) (A ⊠ B)` through the diagonal blocks is the binary product `A × B`,
pulled back along the rank cast. -/
def rightPsiCompactEquivOf (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (κ : Representation ℂ
      ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (l : (rightPsiStages (R := F.Carrier) hr hm).comap
        (levi (n := m + r) (F := F.Carrier))) (w : W),
      e (κ l w) = (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
          ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
        TensorProduct.map (X.1.representation (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
          (X.2.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l))) (e w)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + r)
    letI := T.generalLinearTopologicalGroup (r + m)
    (Induction.compactInduced
        ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) κ).Equiv
      (((T.binaryPositiveProductFunctor hr hm).obj X).representation.comp
        (generalLinearCastHom (Nat.add_comm r m))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + r)
  letI := T.generalLinearTopologicalGroup (r + m)
  (Induction.compactInducedTransport (rightPsiCastContinuous m r F.Carrier)
      ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
      ((BlockShape.binary r m hr hm).parabolic F.Carrier) (mem_rightPsi_iff hr hm) κ
      (T.binaryPositiveCoefficient hr hm X) (e.trans (T.binaryPositiveTensorEquiv hr hm X).symm)
      (rightPsi_transport_equivariant T hr hm X κ e he)).symm.trans
    ((Induction.restrictAlongEquiv (rightPsiCastContinuous m r F.Carrier).toMonoidHom
      (T.binaryPositiveCompactEquiv hr hm X)).trans
      (compEquivOfEq _ (rightPsiCastContinuous_toMonoidHom m r F.Carrier)))

/-- The identification is natural for a coefficient intertwiner lying over a pair of
morphisms `f = (f₁, f₂)`, i.e. carried to `f₁ ⊗ f₂`. -/
theorem rightPsiCompactEquivOf_natural (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (κ : Representation ℂ
      ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (l : (rightPsiStages (R := F.Carrier) hr hm).comap
        (levi (n := m + r) (F := F.Carrier))) (w : W),
      e (κ l w) = (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
          ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
        TensorProduct.map (X.1.representation (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
          (X.2.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l))) (e w))
    (κ' : Representation ℂ
      ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) W')
    (e' : letI := T.topology; W' ≃ₗ[ℂ] (Y.1 ⊗[ℂ] Y.2))
    (he' : letI := T.topology; ∀ (l : (rightPsiStages (R := F.Carrier) hr hm).comap
        (levi (n := m + r) (F := F.Carrier))) (w : W'),
      e' (κ' l w) = (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
          ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
        TensorProduct.map (Y.1.representation (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
          (Y.2.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l))) (e' w))
    (t : κ.IntertwiningMap κ')
    (ht : letI := T.topology; ∀ w, e' (t w) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap (e w))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (m + r)
      Induction.CompactFunctions
        ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) κ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + r)
    letI := T.generalLinearTopologicalGroup (r + m)
    rightPsiCompactEquivOf T hr hm Y κ' e' he'
        (Induction.compactInducedMap
          ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) t u) =
      SmoothRep.hom ((T.binaryPositiveProductFunctor hr hm).map f)
        (rightPsiCompactEquivOf T hr hm X κ e he u) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (m + r)
  let _ := T.generalLinearTopologicalGroup (r + m)
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (T.binaryPositiveTensorEquiv hr hm Y).symm
      (e' (t (Induction.eval
        ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) κ
        u.val ((rightPsiCastContinuous m r F.Carrier).symm x)))) =
    T.binaryPositiveCoefficientMap hr hm f ((T.binaryPositiveTensorEquiv hr hm X).symm
      (e (Induction.eval
        ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) κ
        u.val ((rightPsiCastContinuous m r F.Carrier).symm x))))
  apply (T.binaryPositiveTensorEquiv hr hm Y).injective
  rw [LinearEquiv.apply_symm_apply, PadicField.TopologicalData.binaryPositiveCoefficientMap_tensor,
    LinearEquiv.apply_symm_apply, ht]

end Transport


/-! ## The `Ψ⁻` clause at positive ranks -/

section Positive

open Induction QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The mirabolic group `P_(n+1)` has a basis of compact open subgroups at the identity. -/
theorem mirabolic_compactOpenBasis (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ O : Set (mirabolic n F.Carrier), IsOpen O → (1 : mirabolic n F.Carrier) ∈ O →
      ∃ U : OpenSubgroup (mirabolic n F.Carrier), IsCompact (U : Set (mirabolic n F.Carrier)) ∧
        (U : Set (mirabolic n F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
  have : NonarchimedeanGroup (mirabolic n F.Carrier) :=
    { is_nonarchimedean := fun U hU => by
        rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
        exact ⟨OpenSubgroup.comap (mirabolic n F.Carrier).subtype continuous_subtype_val L,
          fun x hx => hVU (hL hx)⟩ }
  intro O hO h1
  exact Langlands.compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

/-- The target functor at positive ranks, with the binary product in its positive model
and the rank cast replaced by the explicit pullback. -/
abbrev rightPsiPosTarget (T : F.TopologicalData) (k r' : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r' + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((k + 1) + (r' + 1)) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T (r' + 1)).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
    T.binaryPositiveProductFunctor (Nat.succ_pos r') (Nat.succ_pos k) ⋙
      Mirabolic.continuousPullbackFunctor (generalLinearCastHom (Nat.add_comm (r' + 1) (k + 1)))
        (continuous_generalLinearCastHom (Nat.add_comm (r' + 1) (k + 1)))

set_option maxHeartbeats 1000000 in
/-- BZ77 4.13(c), `Ψ⁻` clause, at positive ranks: `Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ` naturally,
for `τ` on `P_(r+1)`, `r ≥ 1`, and `ρ` on `GL_(k+1)`. -/
theorem rightPsiCompatibility_pos (T : F.TopologicalData) (k r' : ℕ) :
    letI := T.topology
    Nonempty
      (T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1) ⋙
          Mirabolic.psiMinus T ((k + 1) + (r' + 1)) ≅
        (Mirabolic.psiMinus T (r' + 1)).prod
            (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
          T.binaryNormalizedProductFunctor (r' + 1) (k + 1) ⋙
            generalLinearRankCast T (Nat.add_comm (r' + 1) (k + 1))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + 1 + (r' + 1) + 1)
  let := T.generalLinearLocallyCompactSpace (k + 1 + (r' + 1) + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + 1 + (r' + 1)) (F := F.Carrier)
  let := T.generalLinearTopologicalGroup (k + 1 + (r' + 1))
  have hr : 0 < r' + 1 := Nat.succ_pos r'
  have hm : 0 < k + 1 := Nat.succ_pos k
  -- The split stage data: `G = P_(n+1)`, `L = GL_n`, `P = rightPsiStages`, `H` of case (III).
  have hcp : Continuous (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) :=
    GeneralLinear.Mirabolic.continuous_projection
  have hcl : Continuous (levi (n := k + 1 + (r' + 1)) (F := F.Carrier)) := continuous_levi
  have hNr : (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)).ker =
      radical (k + 1 + (r' + 1)) F.Carrier := ker_projection
  have hN : IsClosed ((projection (n := k + 1 + (r' + 1)) (F := F.Carrier)).ker :
      Set (mirabolic (k + 1 + (r' + 1)) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  have hBasis := mirabolic_compactOpenBasis T (k + 1 + (r' + 1))
  -- Measures on the kernel `ker rP ≅ V_(n+1)`, its intersection with `H`, and the quotient.
  let eK := splitStagesKernelContinuousEquiv (projection (n := k + 1 + (r' + 1)) (F := F.Carrier))
    levi projection_levi (rightPsiStages (R := F.Carrier) hr hm)
    (ker_projection_le_rightPsiStages hr hm)
  let : LocallyCompactSpace (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)).ker :=
    hN.locallyCompactSpace
  let : LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker :=
    eK.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hIc : IsClosed (((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype : Subgroup _) :
        Set (rightPsiRetraction (R := F.Carrier) hr hm).ker) :=
    isClosed_splitKernelIntersection _ _ (isClosed_rightPsiInducing hr hm)
  let : LocallyCompactSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype) := hIc.locallyCompactSpace
  let : MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker := borel _
  have : BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker := ⟨rfl⟩
  let : MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype) := borel _
  have : BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)) := ⟨rfl⟩
  have hKernelBasis := compactOpenBasis_of_continuousMulEquiv eK
    (compactOpenBasis_congr hNr.symm (radical_compactOpenBasis T (k + 1 + r')))
  have hCover := compactOpenCover_of_continuousMulEquiv eK
    (compactOpenCover_congr hNr.symm (radical_compactOpenCover T (k + 1 + r')))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure (rightPsiRetraction (R := F.Carrier) hr hm).ker := haar
  let μI : Measure ((rightPsiInducing (R := F.Carrier) hr hm).comap
      (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The inducing coefficient is smooth.
  have hσ : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r' + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      IsSmooth (rightPsiInducingCoefficient T X.1.representation X.2.representation) :=
    fun X => (isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) (r' + 1)).isOpen_ker).mpr
      (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth)
  let ψc : SmoothCharacter ℂ (GeneralLinear (k + 1 + (r' + 1)) F.Carrier) :=
    ⟨Mirabolic.psiMinusCharacter T (k + 1 + (r' + 1)),
      Mirabolic.isOpen_ker_psiMinusCharacter T (k + 1 + (r' + 1))⟩
  -- The chain of identifications.
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r' + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      Representation.Equiv
        ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1) ⋙
          Mirabolic.psiMinus T ((k + 1) + (r' + 1))).obj X).representation
        ((rightPsiPosTarget.{uF, uV} T k r').obj X).representation := fun X =>
    (psiMinusCoinvariantsEquiv T (k + 1 + (r' + 1))
      ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1)).obj X)).trans
    ((twistEquiv (Mirabolic.psiMinusCharacter T (k + 1 + (r' + 1)))
      (splitStagesCompactEquiv (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
        projection_levi hcp hcl (rightPsiStages (R := F.Carrier) hr hm)
        (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
        (rightSubgroup_le_rightPsiStages hr hm) (isClosed_rightPsiStages hr hm)
        rightSubgroup_isClosed (rightPsiStages_section_mem hr hm)
        (rightPsiInducingCoefficient T X.1.representation X.2.representation) (hσ X)
        ν hKernelBasis μN μI hν hN hBasis)).trans
    ((compactInductionTwistEquiv _ ψc _).trans
      (rightPsiCompactEquivOf T hr hm ((Mirabolic.psiMinus T (r' + 1)).obj X.1, X.2) _
        (rightPsiCoefficientEquiv T hr hm X.1.representation X.2.representation)
        (fun l x => rightPsiCoefficientEquiv_action T hr hm X.1 X.2 l x))))
  -- Each step of the chain is natural.
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (r' + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (x : (T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1) ⋙
        Mirabolic.psiMinus T ((k + 1) + (r' + 1))).obj X),
      E Y (SmoothRep.hom ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1) ⋙
        Mirabolic.psiMinus T ((k + 1) + (r' + 1))).map φ) x) =
        SmoothRep.hom ((rightPsiPosTarget.{uF, uV} T k r').map φ) (E X x) := by
    intro X Y φ x
    let t₀ := twistIntertwining (T.rightCharacter (k + 1) (r' + 1)).toMonoidHom
      (MixedProductTensor.pullbackMap rightProjection
        (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))
    have h1 := psiMinusCoinvariantsEquiv_natural T (k + 1 + (r' + 1))
      ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1)).map φ) x
    have h2 := splitStagesCompactEquiv_natural
      (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
      projection_levi hcp hcl (rightPsiStages (R := F.Carrier) hr hm)
      (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
      (rightSubgroup_le_rightPsiStages hr hm) (isClosed_rightPsiStages hr hm)
      rightSubgroup_isClosed (rightPsiStages_section_mem hr hm)
      (rightPsiInducingCoefficient T X.1.representation X.2.representation) (hσ X)
      ν hKernelBasis μN μI hν (hσ Y) t₀ hN hBasis
      (psiMinusCoinvariantsEquiv T (k + 1 + (r' + 1))
        ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1)).obj X) x)
    have h3 := compactInductionTwistEquiv_natural _ ψc
      (splitStagesCoefficientMap (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
        projection_levi (rightPsiStages (R := F.Carrier) hr hm)
        (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
        (rightSubgroup_le_rightPsiStages hr hm) rightSubgroup_isClosed
        (rightPsiStages_section_mem hr hm)
        (rightPsiInducingCoefficient T X.1.representation X.2.representation) t₀)
      (splitStagesCompactEquiv (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
        projection_levi hcp hcl (rightPsiStages (R := F.Carrier) hr hm)
        (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
        (rightSubgroup_le_rightPsiStages hr hm) (isClosed_rightPsiStages hr hm)
        rightSubgroup_isClosed (rightPsiStages_section_mem hr hm)
        (rightPsiInducingCoefficient T X.1.representation X.2.representation) (hσ X)
        ν hKernelBasis μN μI hν hN hBasis
        (psiMinusCoinvariantsEquiv T (k + 1 + (r' + 1))
          ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1)).obj X) x))
    have h4 := rightPsiCompactEquivOf_natural T hr hm
      (((Mirabolic.psiMinus T (r' + 1)).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)))).map φ) _
      (rightPsiCoefficientEquiv T hr hm X.1.representation X.2.representation)
      (fun l x => rightPsiCoefficientEquiv_action T hr hm X.1 X.2 l x) _
      (rightPsiCoefficientEquiv T hr hm Y.1.representation Y.2.representation)
      (fun l x => rightPsiCoefficientEquiv_action T hr hm Y.1 Y.2 l x)
      (twistIntertwining _
        (splitStagesCoefficientMap (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
          projection_levi (rightPsiStages (R := F.Carrier) hr hm)
          (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
          (rightSubgroup_le_rightPsiStages hr hm) rightSubgroup_isClosed
          (rightPsiStages_section_mem hr hm)
          (rightPsiInducingCoefficient T X.1.representation X.2.representation) t₀))
      (fun w => rightPsiCoefficientEquiv_natural T hr hm φ.1 φ.2 t₀ (fun _ _ => rfl) w)
      (compactInductionTwistEquiv _ ψc _
        (splitStagesCompactEquiv (projection (n := k + 1 + (r' + 1)) (F := F.Carrier)) levi
          projection_levi hcp hcl (rightPsiStages (R := F.Carrier) hr hm)
          (rightSubgroup (k + 1) (r' + 1) F.Carrier) (ker_projection_le_rightPsiStages hr hm)
          (rightSubgroup_le_rightPsiStages hr hm) (isClosed_rightPsiStages hr hm)
          rightSubgroup_isClosed (rightPsiStages_section_mem hr hm)
          (rightPsiInducingCoefficient T X.1.representation X.2.representation) (hσ X)
          ν hKernelBasis μN μI hν hN hBasis
          (psiMinusCoinvariantsEquiv T (k + 1 + (r' + 1))
            ((T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1)).obj X) x)))
    have h := chain_natural₄ x h1 h2 h3 h4
    exact h
  -- Assemble the natural isomorphism.
  let iso0 : T.rightMixedProductFunctor.{uF, uV} (k + 1) (r' + 1) ⋙
      Mirabolic.psiMinus T ((k + 1) + (r' + 1)) ≅ rightPsiPosTarget.{uF, uV} T k r' :=
    NatIso.ofComponents (fun X => SmoothRep.mkIso (E X))
      (fun φ => MixedProductTensor.smoothRep_hom_ext (hEnat φ))
  exact ⟨iso0 ≪≫ Functor.isoWhiskerLeft
    ((Mirabolic.psiMinus T (r' + 1)).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
      T.binaryPositiveProductFunctor (Nat.succ_pos r') (Nat.succ_pos k))
    (generalLinearRankCastIso.{uF, max uF uV} T (Nat.add_comm (r' + 1) (k + 1))).symm⟩

/-- BZ77 4.13(c), `Ψ⁻` clause: `Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ` naturally, at every rank of `τ`. -/
theorem rightPsiCompatibility (T : F.TopologicalData) :
    RightPsiCompatibility.{uF, uV} F T := by
  intro k r
  cases r with
  | zero => exact rightPsiCompatibility_zero T k
  | succ r' => exact rightPsiCompatibility_pos T k r'

end Positive

end Langlands.Derivative.MirabolicProductMinus
