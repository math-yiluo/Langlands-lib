import Langlands.Representation.Filtration.InvariantBilinearSubquotientBounds
import Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement
import Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
import Langlands.Representation.Filtration.SmoothDualEvaluation
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Smooth.Contragredient.ExactProof

/-! Core of the BZ77 Theorem 4.2 argument.

If the top derivative of `π` on `GL_(N+1)` is one-dimensional and, at every
intermediate order, the derivatives of `π` and of `ν π~` have filtrations whose
graded pieces are zero or irreducible and pairwise carry no invariant forms, then
`π` is irreducible. Exactness of derivatives, detection by derivatives (BZ77 3.5)
and BZ77 Proposition 3.8 enter as hypotheses, namely the published statements
`GeneralLinearDerivativeExactnessStatement`, `MirabolicDerivativeDetection` and
`MirabolicHighestDerivativePairingStatement`; `NonadjacentLeibnizPieces` discharges
them with their published proofs. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.NonadjacentAssembly

open GeneralLinear HarmonicAnalysis Derivative InvariantBilinear

universe uF u uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section Exact

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [Group H] [TopologicalSpace H]

/-- An exact functor carries actual subrepresentations and quotients to actual
subrepresentations and quotients. -/
theorem isSubOrQuotient_map {J : SmoothRep.{0, _, uV} ℂ G ⥤ SmoothRep.{0, _, uV} ℂ H}
    (hJ : Mirabolic.MapsShortExactIntertwiners J) {A B : SmoothRep.{0, _, uV} ℂ G}
    (h : IsSubOrQuotient A.obj B.obj) : IsSubOrQuotient (J.obj A).obj (J.obj B).obj := by
  rcases h with ⟨f, hf⟩ | ⟨f, hf⟩
  · let i : A ⟶ B := SmoothRep.ofHom f
    have hrange : LinearMap.range (SmoothRep.hom i).toLinearMap =
        LinearMap.ker (SmoothRep.hom (SmoothRep.cokernelπ i)).toLinearMap :=
      (Submodule.ker_mkQ _).symm
    exact Or.inl ⟨SmoothRep.hom (J.map i),
      (hJ A B _ i (SmoothRep.cokernelπ i) hf (SmoothRep.mkQ_surjective _ _) hrange).1⟩
  · let q : B ⟶ A := SmoothRep.ofHom f
    have hrange : LinearMap.range (SmoothRep.hom (SmoothRep.kernelι q)).toLinearMap =
        LinearMap.ker (SmoothRep.hom q).toLinearMap :=
      Submodule.range_subtype _
    exact Or.inr ⟨SmoothRep.hom (J.map q),
      (hJ _ B A (SmoothRep.kernelι q) q (SmoothRep.subtype_injective _ _) hf hrange).2.2⟩

end Exact

/-- Change the covariance of a form along a pointwise equality of characters. -/
def formsCast {k : Type*} [Field k] {G : Type*} [Monoid G] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} {χ χ' : G → k}
    (h : ∀ g, χ g = χ' g) (B : forms ρ σ χ) : forms ρ σ χ' :=
  ⟨B.val, fun g v w => (B.property g v w).trans (by rw [h])⟩

/-- `ν π~`, the `|det|`-twist of the smooth contragredient on `GL_(N+1)`. -/
def dualTwistRep {N : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (N + 1)
  π.contragredient.twist (T.determinantPowerCharacter (N + 1) 1)
    (T.isOpen_ker_determinantPowerCharacter (N + 1) 1)

/-- The derivative of order `d` of the restriction to the mirabolic subgroup. -/
abbrev restrictedDerivative (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N d : ℕ) (hd : 0 < d ∧ d ≤ N + 1) :
    letI := T.topology
    SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1 - d) F.Carrier) :=
  letI := T.topology
  generalLinearRestriction T N ⋙ mirabolicDerivativeOfOrder T ψ N d hd

/-- The published exactness statement gives exactness of the restricted derivatives. -/
theorem restrictedDerivative_exact
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, u} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N d : ℕ) (hd : 0 < d ∧ d ≤ N + 1) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (restrictedDerivative.{uF, u} F T ψ N d hd) := by
  let _ := T.topology
  change Mirabolic.MapsShortExactIntertwiners
    (generalLinearRestriction T N ⋙ mirabolicDerivativeOfOrder T ψ N d hd)
  rw [← generalLinearDerivative_eq_restriction_comp T ψ N d hd.2 hd]
  exact hE ψ (N + 1) d hd.2

/-- At every intermediate order `d`, the derivatives of `π` and of `ν π~` have
filtrations with zero or irreducible graded pieces and no invariant forms between
any two pieces. -/
def PiecesWithoutForms (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (π : letI := T.topology; SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier)) :
    Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d ∧ d ≤ N + 1), d < N + 1 →
    ∃ (m n : ℕ) (s : ObjectRepFiltration ((restrictedDerivative F T ψ N d hd).obj π).obj m)
      (t : ObjectRepFiltration
        ((restrictedDerivative F T ψ N d hd).obj (dualTwistRep F T π)).obj n),
      (∀ i, ZeroOrIrreducible (s.gradedRepresentation i).ρ) ∧
      (∀ j, ZeroOrIrreducible (t.gradedRepresentation j).ρ) ∧
      ∀ i j, length (s.gradedRepresentation i).ρ (t.gradedRepresentation j).ρ
        (fun _ => (1 : ℂ)) = 0

/-- A nonzero subrepresentation or quotient `X` of `π` whose top derivative vanishes,
with `ν X~` correspondingly a subrepresentation or quotient of `ν π~`, cannot exist. -/
theorem false_of_constituent
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, u} F T)
    (hPL : MirabolicDerivativeDetection.{uF, u} F T)
    (hHP : MirabolicHighestDerivativePairingStatement.{uF, u, u} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (π X : letI := T.topology; SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier))
    (hpieces : PiecesWithoutForms F T ψ N π) [hXn : Nontrivial X]
    (htop : Subsingleton
      ((restrictedDerivative F T ψ N (N + 1) ⟨Nat.succ_pos N, le_rfl⟩).obj X))
    (hX : IsSubOrQuotient X.obj π.obj)
    (hXd : IsSubOrQuotient (dualTwistRep F T X).obj (dualTwistRep F T π).obj) : False := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (N + 1)
  let XP := (generalLinearRestriction T N).obj X
  let BP := (generalLinearRestriction T N).obj (dualTwistRep F T X)
  have hXP : Nontrivial XP := hXn
  obtain ⟨d, hdl⟩ : ∃ d, level T ψ XP = d := ⟨_, rfl⟩
  have hpos : 0 < d := hdl ▸ hPL ψ N XP hXP
  obtain ⟨hdle, ⟨hd, hnon⟩, hhigh⟩ := (level_eq_iff T ψ hpos XP).mp hdl
  have hdlt : d < N + 1 := by
    refine lt_of_le_of_ne hdle ?_
    rintro rfl
    obtain ⟨x, y, hxy⟩ := hnon.exists_pair_ne
    exact hxy (@Subsingleton.elim _ htop x y)
  let ν := T.determinantPowerCharacter (N + 1) 1
  let φ := (mirabolic N F.Carrier).subtype
  let β0 := comapGroup φ X.representation
    (Langlands.twist ν (smoothContragredient X.representation)) (fun g => (ν g : ℂ))
    (smoothDualEvaluation X.representation ν)
  have hχ : ∀ g : mirabolic N F.Carrier, ((fun g => (ν g : ℂ)) ∘ φ) g =
      ((((T.determinantNorm (N + 1)) g.val : NNReal) : ℝ) : ℂ) := by
    intro g
    change ((((T.determinantNorm (N + 1) g.val : NNReal) : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) = _
    rw [Real.rpow_one]
  let β : forms XP.representation BP.representation
      (fun g => ((((T.determinantNorm (N + 1)) g.val : NNReal) : ℝ) : ℂ)) :=
    formsCast hχ β0
  have hβ : ∀ v : XP, (∀ w : BP, β.val v w = 0) → v = 0 :=
    smoothDualEvaluation_separatingLeft (GeneralLinear.compactOpen_cofinal F T (N + 1))
      X.representation X.isSmooth ν
  obtain ⟨γ, hγ⟩ := hHP ψ N XP BP d hd hnon
    (fun j hj hdj => not_nontrivial_iff_subsingleton.mp fun h => hhigh hdj hj.2 ⟨hj, h⟩)
    β hβ
  have hγ0 : γ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : (mirabolicDerivativeOfOrder T ψ N d hd).obj XP)
    exact hv (hγ v fun w => by rw [h0]; rfl)
  obtain ⟨m, n, s, t, hs, ht, hst⟩ := hpieces d hd hdlt
  have hlen := length_eq_zero_of_isSubOrQuotient
    (isSubOrQuotient_map (restrictedDerivative_exact F T hE ψ N d hd) hX)
    (isSubOrQuotient_map (restrictedDerivative_exact F T hE ψ N d hd) hXd) s t hs ht _ hst
  exact hγ0 (@Subsingleton.elim _ (Module.length_eq_zero_iff.mp hlen) γ 0)

/-- Conditional core of BZ77 Theorem 4.2: a one-dimensional top derivative and
form-free graded pieces at all intermediate orders force irreducibility. -/
theorem irreducible_of_pieces
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, u} F T)
    (hPL : MirabolicDerivativeDetection.{uF, u} F T)
    (hHP : MirabolicHighestDerivativePairingStatement.{uF, u, u} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (π : letI := T.topology; SmoothRep.{0, uF, u} ℂ (GeneralLinear (N + 1) F.Carrier))
    (htop : Module.finrank ℂ
      ((restrictedDerivative F T ψ N (N + 1) ⟨Nat.succ_pos N, le_rfl⟩).obj π) = 1)
    (hpieces : PiecesWithoutForms F T ψ N π) :
    letI := T.topology
    π.IsIrreducible := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (N + 1)
  have hcof := GeneralLinear.compactOpen_cofinal F T (N + 1)
  let ν := T.determinantPowerCharacter (N + 1) 1
  let J := restrictedDerivative F T ψ N (N + 1) ⟨Nat.succ_pos N, le_rfl⟩
  have hJ := restrictedDerivative_exact F T hE ψ N (N + 1) ⟨Nat.succ_pos N, le_rfl⟩
  have hJπ : Nontrivial (J.obj π) :=
    Module.nontrivial_of_finrank_pos (lt_of_lt_of_eq Nat.one_pos htop.symm)
  have hπ : Nontrivial π := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact @false_of_nontrivial_of_subsingleton (J.obj π) hJπ
      (mirabolicDerivativeOfOrder_obj_subsingleton T ψ N (N + 1)
        ⟨Nat.succ_pos N, le_rfl⟩ ((generalLinearRestriction T N).obj π) h)
  have hne : (⊥ : Subrepresentation π.representation) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : π)
    have hv' : v ∈ (⊤ : Subrepresentation π.representation).toSubmodule := Submodule.mem_top
    rw [← h] at hv'
    exact hv ((Submodule.mem_bot ℂ).mp hv')
  refine { toNontrivial := ⟨⟨⊥, ⊤, hne⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_contra hS
  push Not at hS
  obtain ⟨hSb, hSt⟩ := hS
  let ω := SmoothRep.subrepresentation π S
  let Q := SmoothRep.quotient π S
  have hrange : LinearMap.range (SmoothRep.hom (SmoothRep.subtype π S)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (SmoothRep.mkQ π S)).toLinearMap :=
    (Submodule.range_subtype _).trans (Submodule.ker_mkQ _).symm
  obtain ⟨ha, hab, hb⟩ := hJ ω π Q (SmoothRep.subtype π S) (SmoothRep.mkQ π S)
    (SmoothRep.subtype_injective π S) (SmoothRep.mkQ_surjective π S) hrange
  have hωn : Nontrivial ω := Submodule.nontrivial_iff_ne_bot.mpr
    fun h => hSb (Subrepresentation.toSubmodule_injective h)
  have hQn : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr
    fun h => hSt (Subrepresentation.toSubmodule_injective h)
  by_cases hω : Subsingleton (J.obj ω)
  · exact false_of_constituent F T hE hPL hHP ψ N π ω hpieces hω
      (Or.inl ⟨_, SmoothRep.subtype_injective π S⟩)
      (Or.inr ⟨twistIntertwining ν (contragredientMap (SmoothRep.hom (SmoothRep.subtype π S))),
        contragredientMap_surjective_of_injective_of_compact_cofinal hcof ω.isSmooth π.isSmooth
          _ (SmoothRep.subtype_injective π S)⟩)
  · rw [not_subsingleton_iff_nontrivial] at hω
    obtain ⟨x, hx⟩ := exists_ne (0 : J.obj ω)
    have hax : SmoothRep.hom (J.map (SmoothRep.subtype π S)) x ≠ 0 :=
      fun h => hx (ha (h.trans (map_zero _).symm))
    have hmem : SmoothRep.hom (J.map (SmoothRep.subtype π S)) x ∈
        LinearMap.ker (SmoothRep.hom (J.map (SmoothRep.mkQ π S))).toLinearMap :=
      hab ▸ LinearMap.mem_range_self _ x
    have hzero : ∀ y : J.obj Q, y = 0 := by
      intro y
      obtain ⟨z, rfl⟩ := hb y
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hax).mp htop z
      have h0 : SmoothRep.hom (J.map (SmoothRep.mkQ π S))
          (SmoothRep.hom (J.map (SmoothRep.subtype π S)) x) = 0 := LinearMap.mem_ker.mp hmem
      rw [map_smul]
      exact (congrArg (c • ·) h0).trans (smul_zero c)
    have hQ : Subsingleton (J.obj Q) := ⟨fun y y' => (hzero y).trans (hzero y').symm⟩
    exact false_of_constituent F T hE hPL hHP ψ N π Q hpieces hQ
      (Or.inr ⟨_, SmoothRep.mkQ_surjective π S⟩)
      (Or.inl ⟨twistIntertwining ν (contragredientMap (SmoothRep.hom (SmoothRep.mkQ π S))),
        contragredientMap_injective_of_surjective _ (SmoothRep.mkQ_surjective π S)⟩)

end Langlands.Classification.NonadjacentAssembly
