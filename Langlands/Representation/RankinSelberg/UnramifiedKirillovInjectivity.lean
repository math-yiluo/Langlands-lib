import Langlands.Representation.Classification.ZelevinskySocleGenericityProof
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
import Langlands.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.CompactOpen

/-!
# Injectivity of the Kirillov map

For an irreducible representation `π` of `GL_(n+1)(F)` with a nonzero standard Whittaker
functional `ℓ` spanning its functional space, a vector `v` with `ℓ(π(p) v) = 0` for every
`p` in the mirabolic subgroup is zero. The proof embeds `π` in a Zelevinsky product, whose
mirabolic restriction is homogeneous; a nonzero kernel would therefore have a nonzero top
derivative, that is nonzero full upper coinvariants, contradicting multiplicity one.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedUnitary

open CategoryTheory GeneralLinear Derivative Jacquet.Localization

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ### Compactness of the mirabolic upper unipotent group -/

/-- The upper unipotent subgroup of the mirabolic group is a limit of compact subgroups. -/
theorem mirabolicUpperUnipotent_isLimitOfCompactSubgroups (T : F.TopologicalData) (n : ℕ) :
    let := T.topology
    IsLimitOfCompactSubgroups (Mirabolic.upperUnipotent n F.Carrier) := by
  intro _ C hC
  let e := Mirabolic.upperUnipotentContinuousEquiv (F := F.Carrier) (n := n)
  obtain ⟨K, hK, hCK⟩ := upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)
    (e '' C) (hC.image e.continuous)
  refine ⟨K.comap e.toMonoidHom, ?_, ?_⟩
  · change IsCompact (e ⁻¹' (K : Set _))
    exact e.toHomeomorph.isCompact_preimage.2 hK
  · intro c hc
    exact hCK ⟨c, hc, rfl⟩

/-! ### The top derivative and the full upper coinvariants -/

/-- Rank transport of a mirabolic representation does not change whether its full upper
coinvariants are nonzero. -/
theorem nontrivial_coinvariants_rankCast (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ)
    {N M : ℕ} (h : N = M)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) :
    let := T.topology
    Nontrivial (Coinvariants ((mirabolicRankCast T h).obj B).representation
        (Mirabolic.upperUnipotent M F.Carrier) (TopLocalization.mirabolicUpperCharacter ψ M)) ↔
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        (TopLocalization.mirabolicUpperCharacter ψ N)) := by
  let := T.topology
  subst h
  rw [mirabolicRankCast_refl]
  rfl

/-- The top derivative of a mirabolic representation is nonzero exactly when its full upper
coinvariants are nonzero. -/
theorem hasNonzeroDerivative_top_iff (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) :
    let := T.topology
    HasNonzeroDerivative T ψ B (N + 1) ↔
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        (TopLocalization.mirabolicUpperCharacter ψ.complex N)) := by
  let := T.topology
  have hk : 0 < N + 1 ∧ N + 1 ≤ N + 1 := ⟨Nat.succ_pos N, le_rfl⟩
  have h1 : HasNonzeroDerivative T ψ B (N + 1) ↔
      Nontrivial ((mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩
  have h2 : Nontrivial ((mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) ↔
      Nontrivial ((generalLinearRankCast T (Nat.sub_self (N + 1))).obj
        ((mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B)) :=
    (RestrictionBridge.nontrivial_generalLinearRankCast_iff T _ _).symm
  have h3 : (generalLinearRankCast T (Nat.sub_self (N + 1))).obj
        ((mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) =
      (mirabolicDerivative T ψ 0 N).obj
        ((mirabolicRankCast T (Nat.zero_add N).symm).obj B) :=
    congrArg (fun J => J.obj B) (mirabolicDerivativeOfOrder_top T ψ N hk)
  have h4 := LevelCalculus.nontrivial_iff_of_iso
    ((TopLocalization.mirabolicLocalizationIso T ψ N).app
      ((mirabolicRankCast T (Nat.zero_add N).symm).obj B))
  rw [h1, h2, h3, ← h4]
  exact nontrivial_coinvariants_rankCast T ψ.complex (Nat.zero_add N).symm B

/-! ### Mirabolic and general linear functionals -/

section Functionals

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem mem_mirabolicFunctionals_iff (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V) :
    let := T.topology
    ℓ ∈ Whittaker.functionals (Mirabolic.upperUnipotent n F.Carrier)
        (TopLocalization.mirabolicUpperCharacter ψ.complex n)
        (π.comp (mirabolic n F.Carrier).subtype) ↔
      ℓ ∈ Whittaker.glFunctionals ψ n π := by
  let := T.topology
  constructor
  · intro h u w
    have := h (Mirabolic.upperUnipotentEquiv.symm u) w
    change ℓ (π u.val w) = _
    simpa [TopLocalization.mirabolicUpperCharacter,
      Whittaker.entrywiseCharacter_eq_standardCharacter] using this
  · intro h u w
    have := h (Mirabolic.upperUnipotentEquiv u) w
    change ℓ (π u.val.val w) = _
    simpa [TopLocalization.mirabolicUpperCharacter,
      Whittaker.entrywiseCharacter_eq_standardCharacter] using this

end Functionals

/-! ### The character of the coinvariants -/

/-- A complex character with open kernel is locally constant. -/
theorem character_isLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' (χ.ker : Set G),
    hχ.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change χ (y * x⁻¹) = 1 at hy
    have heq : χ y = χ x := mul_inv_eq_one.mp (by
      simpa only [map_mul, map_inv] using hy)
    exact congrArg (fun z : ℂˣ => (z : ℂ)) heq

theorem mirabolicUpperCharacter_isLocallyConstant (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    IsLocallyConstant (fun u : Mirabolic.upperUnipotent n F.Carrier =>
      (TopLocalization.mirabolicUpperCharacter ψ.complex n u : ℂ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.upperUnipotentNonarchimedean (n + 1)
  have hstd : IsOpen ((Whittaker.standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character _
      (Whittaker.standardCharacterContinuous ψ n).continuous
  let e := Mirabolic.upperUnipotentContinuousEquiv (F := F.Carrier) (n := n)
  have hset : ((TopLocalization.mirabolicUpperCharacter ψ.complex n).ker :
      Set (Mirabolic.upperUnipotent n F.Carrier)) =
        e ⁻¹' ((Whittaker.standardCharacter ψ n).ker : Set _) := by
    ext u
    change (Whittaker.entrywiseCharacter ψ.complex (n + 1)) (Mirabolic.upperUnipotentEquiv u) = 1 ↔
      Whittaker.standardCharacter ψ n (e u) = 1
    rw [Whittaker.entrywiseCharacter_eq_standardCharacter]
    rfl
  have hker : IsOpen ((TopLocalization.mirabolicUpperCharacter ψ.complex n).ker :
      Set (Mirabolic.upperUnipotent n F.Carrier)) := by
    rw [hset]
    exact hstd.preimage e.continuous
  exact character_isLocallyConstant _ hker

theorem isInvariant_bot {G : Type*} [Group G] (U : Subgroup G) (θ : U →* ℂˣ) :
    IsInvariant U ⊥ bot_le θ := by
  rintro ⟨m, hm⟩ u
  rw [Subgroup.mem_bot] at hm
  subst hm
  congr 1
  apply Subtype.ext
  simp [conjugate]

/-! ### Injectivity -/

/-- Kirillov injectivity for an irreducible smooth representation with carrier in the
saturated universe: if a nonzero standard Whittaker functional spans the functional space,
a vector whose Whittaker function vanishes on the mirabolic subgroup is zero. -/
theorem kirillov_injective_saturated (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
      Representation.IsIrreducible π.representation →
      ∀ ℓ : Whittaker.glFunctionals ψ n π.representation, ℓ.val ≠ 0 →
      (∀ ℓ' : Whittaker.glFunctionals ψ n π.representation, ∃ c : ℂ, ℓ' = c • ℓ) →
      ∀ v : π, (∀ g : mirabolic n F.Carrier, ℓ.val (π.representation g v) = 0) → v = 0 := by
  classical
  let := T.topology
  have := T.generalLinearTopologicalGroup (n + 1)
  intro π hirr ℓ hℓ hmult v hv
  -- homogeneity of the mirabolic restriction, from a Zelevinsky embedding
  obtain ⟨a, -, d, -, hd⟩ := Classification.multisegmentSocleExhaustion F T (n + 1) π hirr
  obtain ⟨ho, hs, -, j, hj⟩ := hd.isZelevinskySubrepresentation
  have hsep := Classification.precedenceOrdered_endpointSeparated F T
    (Classification.cuspidalIntegralTwistFreeness F T) d.segments ho
  have hhom : IsHomogeneous T ψ ((generalLinearRestriction T n).obj d.induced) :=
    (isGeneralLinearHomogeneous_iff T ψ d.induced).mp
      (Classification.segmentSocleProductHomogeneity F T ψ n d hs hsep)
  let A := (generalLinearRestriction T n).obj π
  let X := (generalLinearRestriction T n).obj d.induced
  let jR : A ⟶ X := (generalLinearRestriction T n).map (SmoothRep.ofHom j)
  have hjR : Function.Injective (SmoothRep.hom jR) := hj
  let U := Mirabolic.upperUnipotent n F.Carrier
  let θ := TopLocalization.mirabolicUpperCharacter ψ.complex n
  let ℓA : Module.Dual ℂ A := ℓ.val
  have hℓA : ℓA ∈ Whittaker.functionals U θ A.representation :=
    (mem_mirabolicFunctionals_iff T ψ π.representation ℓ.val).2 ℓ.property
  -- the level of the restriction is the top order
  have hπnt : Nontrivial π := by
    let := hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
      π.representation.asModule
  have hAnt : Nontrivial A := hπnt
  have hAtop : HasNonzeroDerivative T ψ A (n + 1) := by
    apply (hasNonzeroDerivative_top_iff T ψ n A).2
    let f := Whittaker.functionalsLocalizationDualEquiv U θ A.representation ⟨ℓA, hℓA⟩
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    apply hℓ
    ext w
    have h1 : f (mk A.representation U θ w) = ℓA w := rfl
    rw [Subsingleton.elim (mk A.representation U θ w) 0, map_zero] at h1
    exact h1.symm
  have hlevA : level T ψ A = n + 1 :=
    (level_eq_iff T ψ (Nat.succ_pos n) A).2 ⟨le_rfl, hAtop, fun j h1 h2 => by omega⟩
  have hlevX : level T ψ X = n + 1 :=
    (LevelCalculus.level_eq_of_isHomogeneous T ψ hhom jR hjR hAnt).symm.trans hlevA
  -- the kernel of the Kirillov map
  let Y : Subrepresentation A.representation :=
    { toSubmodule :=
        { carrier := {w | ∀ g : mirabolic n F.Carrier, ℓA (A.representation g w) = 0}
          add_mem' := fun {x y} hx hy g => by
            change ℓA (A.representation g (x + y)) = 0
            rw [map_add, map_add, hx g, hy g, add_zero]
          zero_mem' := fun g => by
            change ℓA (A.representation g 0) = 0
            rw [map_zero, map_zero]
          smul_mem' := fun c x hx g => by
            change ℓA (A.representation g (c • x)) = 0
            rw [map_smul, map_smul, hx g, smul_zero] }
      apply_mem_toSubmodule := fun g w hw g' => by
        change ℓA (A.representation g' (A.representation g w)) = 0
        rw [← Module.End.mul_apply, ← map_mul]
        exact hw (g' * g) }
  by_contra hv0
  have hvY : v ∈ Y := hv
  let W := SmoothRep.subrepresentation A Y
  have hWnt : Nontrivial W :=
    ⟨⟨⟨v, hvY⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  let iW : W ⟶ A := SmoothRep.subtype A Y
  have hiW : Function.Injective (SmoothRep.hom iW) := SmoothRep.subtype_injective A Y
  have hWtop := (hasNonzeroDerivative_of_isHomogeneous T ψ (Nat.succ_pos n) hhom hlevX
    (iW ≫ jR) (hjR.comp hiW) hWnt).1
  have hWco := (hasNonzeroDerivative_top_iff T ψ n W).1 hWtop
  obtain ⟨x, hx⟩ := exists_ne (0 : Coinvariants W.representation U θ)
  obtain ⟨w, rfl⟩ := mk_surjective W.representation U θ x
  have hinj := map_injective_of_smooth U (mirabolicUpperUnipotent_isLimitOfCompactSubgroups T n)
    θ (mirabolicUpperCharacter_isLocallyConstant T ψ n) ⊥ bot_le (isInvariant_bot U θ)
    (SmoothRep.hom iW) hiW A.isSmooth
  set wA : A := SmoothRep.hom iW w with hwAdef
  have hwA : mk A.representation U θ wA ≠ 0 := by
    intro h
    apply hx
    apply hinj
    rw [map_zero]
    exact h
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (Coinvariants A.representation U θ),
      g (mk A.representation U θ wA) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hwA ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
  let lam := (Whittaker.functionalsLocalizationDualEquiv U θ A.representation).symm g
  have hlam : lam.val ∈ Whittaker.glFunctionals ψ n π.representation :=
    (mem_mirabolicFunctionals_iff T ψ π.representation lam.val).1 lam.property
  obtain ⟨c, hc⟩ := hmult ⟨lam.val, hlam⟩
  have h0 : lam.val wA = 0 := by
    have := congrArg (fun ℓ' : Whittaker.glFunctionals ψ n π.representation =>
      ℓ'.val wA) hc
    simp only at this
    refine this.trans ?_
    have hwY : ℓA (A.representation 1 wA) = 0 := w.property 1
    rw [map_one, Module.End.one_apply] at hwY
    change c * ℓA wA = 0
    rw [hwY, mul_zero]
  exact hg h0

/-- Kirillov injectivity for an irreducible smooth representation on a complex vector space in
an arbitrary universe. -/
theorem kirillov_injective (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V), IsSmooth π →
      Representation.IsIrreducible π →
      ∀ ℓ : Whittaker.glFunctionals ψ n π, ℓ.val ≠ 0 →
      (∀ ℓ' : Whittaker.glFunctionals ψ n π, ∃ c : ℂ, ℓ' = c • ℓ) →
      ∀ v : V, (∀ g : mirabolic n F.Carrier, ℓ.val (π g v) = 0) → v = 0 := by
  let := T.topology
  have := T.generalLinearTopologicalGroup (n + 1)
  intro π hπ hirr ℓ hℓ hmult v hv
  let A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) := SmoothRep.of π hπ
  let A' := SmoothRep.universeLift.{uF} A
  have hirr' : Representation.IsIrreducible A'.representation :=
    (SmoothRep.isIrreducible_universeLift_iff A).2 hirr
  let ℓ'val : Module.Dual ℂ A' :=
    { toFun := fun x => ℓ.val (ULift.down x)
      map_add' := fun x y => map_add ℓ.val x.down y.down
      map_smul' := fun c x => map_smul ℓ.val c x.down }
  have hℓ'mem : ℓ'val ∈ Whittaker.glFunctionals ψ n A'.representation := by
    intro u x
    exact ℓ.property u (ULift.down x)
  let ℓ' : Whittaker.glFunctionals ψ n A'.representation := ⟨ℓ'val, hℓ'mem⟩
  have hℓ' : ℓ'.val ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : Module.Dual ℂ A' => f (ULift.up x)) h
  have hmult' : ∀ μ : Whittaker.glFunctionals ψ n A'.representation, ∃ c : ℂ, μ = c • ℓ' := by
    intro μ
    let μval : Module.Dual ℂ V :=
      { toFun := fun x => μ.val (ULift.up x)
        map_add' := fun x y => map_add μ.val (ULift.up x) (ULift.up y)
        map_smul' := fun c x => map_smul μ.val c (ULift.up x) }
    have hμmem : μval ∈ Whittaker.glFunctionals ψ n π := by
      intro u x
      exact μ.property u (ULift.up x)
    obtain ⟨c, hc⟩ := hmult ⟨μval, hμmem⟩
    refine ⟨c, Subtype.ext ?_⟩
    ext x
    exact congrArg (fun f : Whittaker.glFunctionals ψ n π => f.val (ULift.down x)) hc
  have hv' : ∀ g : mirabolic n F.Carrier,
      ℓ'.val (A'.representation g (ULift.up v)) = 0 := fun g => hv g
  have h0 := kirillov_injective_saturated T ψ n A' hirr' ℓ' hℓ' hmult' (ULift.up v) hv'
  exact congrArg ULift.down h0

end Langlands.RankinSelberg.UnramifiedUnitary
