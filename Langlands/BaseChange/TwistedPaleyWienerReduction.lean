import Langlands.BaseChange.PaleyWienerAssembly
import Langlands.BaseChange.TwistedLeviPaleyWienerStatements
import Langlands.BaseChange.TwistedPaleyWienerStatement
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.Representation.Induction.SmoothGroupTransport
import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.OneBlockShape
import Langlands.Representation.CompactCoefficient.GroupTransport

/-!
# Reduction of the twisted trace Paley–Wiener theorem to its inputs on Levi products

`TwistedTracePaleyWienerStatement` follows from the six propositions of
`Langlands.BaseChange.TwistedLeviPaleyWienerStatements`. The induction over the Levi products of
`GL_n(E)` is `PaleyWienerAssembly.exists_eq_eval_of_good_of_discrete`; the result for the Levi
product of a block shape with at most one block is transported to `GL_n(E)`. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v z uG

namespace TwistedLeviPaleyWiener

/-! ## Changing the measure by an equality -/

section MeasureCongr

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (θ : G ≃* G) {μ μ' : Measure G}
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant]
  (Φ : Module.Dual ℂ (Distribution G))

theorem isCompactlyDominatedFunctional_congr_measure (h : μ = μ') :
    IsCompactlyDominatedFunctional.{uG, z} θ μ Φ ↔
      IsCompactlyDominatedFunctional.{uG, z} θ μ' Φ := by
  subst h
  rfl

theorem isTwistedTraceFunctional_congr_measure (h : μ = μ') :
    IsTwistedTraceFunctional.{uG, z} θ μ Φ ↔ IsTwistedTraceFunctional.{uG, z} θ μ' Φ := by
  subst h
  rfl

theorem twistedDistribution_congr_measure (h : μ = μ') {V : Type z} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) (hπ : IsAdmissible π) (A : Module.End ℂ V) :
    twistedDistribution μ π hπ A = twistedDistribution μ' π hπ A := by
  subst h
  rfl

end MeasureCongr

section LeviMeasureCongr

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E) (B : BlockShape n)
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] [T2Space (B.Levi E)]
  [LocallyCompactSpace (B.Levi E)] [TotallyDisconnectedSpace (B.Levi E)] {μ μ' : Measure (B.Levi E)}
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant]
  (Φ : Module.Dual ℂ (Distribution (B.Levi E)))

theorem isLeviSigmaInducedRegularFunctional_congr_measure (h : μ = μ') :
    IsLeviSigmaInducedRegularFunctional.{u, v, z} σ B μ Φ ↔
      IsLeviSigmaInducedRegularFunctional.{u, v, z} σ B μ' Φ := by
  subst h
  rfl

end LeviMeasureCongr

/-! ## The Paley–Wiener theorem on every Levi product -/

/-- From the six inputs, for every family of Haar measures on the Levi products of `GL_n(E)`,
every compactly dominated regular functional on a Levi product is a twisted trace functional. -/
theorem levi_isTwistedTraceFunctional_of_inputs
    (hCT : TwistedLeviInductionTransferStatement.{u, v, z})
    (hJ : TwistedLeviJacquetDescentStatement.{u, v, z})
    (hD : TwistedLeviDiscretePaleyWienerStatement.{u, v, z})
    (hA5 : TwistedLeviGoodRestrictionStatement.{u, v, z})
    (hA7 : TwistedLeviInducedSpanStatement.{u, v, z})
    (hA8 : TwistedLeviTraceGoodStatement.{u, v, z})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (d n : ℕ)
    (hE : IsCyclicAlgebra σ d) :
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (μs : ∀ C : BlockShape n, Measure (C.Levi E)) [∀ C, (μs C).IsHaarMeasure]
      (B : BlockShape n) (Φ : Module.Dual ℂ (Distribution (B.Levi E))),
      IsCompactlyDominatedFunctional.{v, z} (leviAut σ B) (μs B) Φ →
      IsLeviSigmaInducedRegularFunctional.{u, v, z} σ B (μs B) Φ →
      IsTwistedTraceFunctional.{v, z} (leviAut σ B) (μs B) Φ := by
  have : Module.Finite F E := hE.1
  let : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
  have : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
  have : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
  have : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
    levi_locallyCompactSpace_of_finite F E C
  have : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
    levi_totallyDisconnectedSpace_of_finite F E C
  intro μs _ B Φ hdom hreg
  -- The system of Levi products, indexed by block shapes of `n`.
  let r : BlockShape n → BlockShape n → Prop := fun C B => n - C.length < n - B.length
  have hwf : WellFounded r := (measure fun C : BlockShape n => n - C.length).wf
  let tgt : ∀ B : BlockShape n, ProperRefinement E B → BlockShape n := fun _ C => C.1
  have htgt : ∀ B (C : ProperRefinement E B), r (tgt B C) B := by
    intro B C
    have h1 := C.1.length_le
    have h2 := C.2.2
    change n - C.1.length < n - B.length
    omega
  let Irr : ∀ B : BlockShape n, Set (Module.Dual ℂ (SchwartzBruhat (B.Levi E))) :=
    fun B => twistedSpectrum.{z, v} (μs B) (leviAut σ B)
  let Good : ∀ B : BlockShape n,
      Set (Module.Dual ℂ (Module.Dual ℂ (SchwartzBruhat (B.Levi E)))) :=
    fun B => { Ψ | IsCompactlyDominatedFunctional.{v, z} (leviAut σ B) (μs B) Ψ ∧
      IsLeviSigmaInducedRegularFunctional.{u, v, z} σ B (μs B) Ψ }
  choose CT hCTp using fun (B : BlockShape n) (C : ProperRefinement E B) =>
    hCT F E σ d n hE B C.1 C.2.1 (μs B) (μs C.1)
  choose L c hL using fun B : BlockShape n => hJ F E σ d n hE μs B (CT B) (hCTp B)
  -- Induced twisted characters of irreducible pairs are properly induced characters, and
  -- they are spanned by irreducible twisted characters.
  have hgen : ∀ B (C : ProperRefinement E B), ∀ θ' ∈ Irr C.1,
      Module.Dual.transpose (R := ℂ) (CT B C) θ' ∈ leviProperInducedSpan.{u, v, z} σ B (μs B) ∧
        Module.Dual.transpose (R := ℂ) (CT B C) θ' ∈ Submodule.span ℂ (Irr B) := by
    rintro B C θ' ⟨W, iAdd, iMod, π, hπ, A, hirr, rfl⟩
    obtain ⟨hI, hspan⟩ := hA7 F E σ d n hE B C.1 C.2.1 (μs B) W π hπ hirr A
    have heq := hCTp B C W π hπ A hI
    rw [Module.Dual.transpose_apply, heq]
    exact ⟨twistedDistribution_mem_leviProperInducedSpan σ B (μs B) C.1 C.2.1 C.2.2 π hπ hirr
      A hI, hspan⟩
  have hind_le : ∀ B, PaleyWienerAssembly.inducedSpan tgt Irr CT B ≤
      leviProperInducedSpan.{u, v, z} σ B (μs B) := by
    intro B
    refine Submodule.span_le.2 ?_
    intro x hx
    obtain ⟨C, θ', hθ', rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun _ h => h
    exact (hgen B C θ' hθ').1
  have hprop_le : ∀ B, leviProperInducedSpan.{u, v, z} σ B (μs B) ≤
      PaleyWienerAssembly.inducedSpan tgt Irr CT B := by
    intro B
    refine Submodule.span_le.2 ?_
    rintro x ⟨C, hCB, hlen, X, iAdd, iMod, Ξ, hΞ, hirr, BΞ, hI, rfl⟩
    have heq := hCTp B ⟨C, hCB, hlen⟩ X Ξ hΞ BΞ hI
    rw [← heq]
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨⟨C, hCB, hlen⟩,
      Set.mem_image_of_mem _ (twistedDistribution_mem_twistedSpectrum _ _ hΞ hirr BΞ)⟩)
  have key := PaleyWienerAssembly.exists_eq_eval_of_good_of_discrete
    (S := fun B : BlockShape n => SchwartzBruhat (B.Levi E)) r hwf tgt htgt Irr Good CT L c
    (by
      rintro B Ψ ⟨hΨd, hΨr⟩ hΨ
      have hzero : ∀ x ∈ leviProperInducedSpan.{u, v, z} σ B (μs B), Ψ x = 0 :=
        fun x hx => hΨ x (hprop_le B hx)
      exact (isTwistedTraceFunctional_iff (μs B) (leviAut σ B) Ψ).1
        (hD F E σ d n hE B (μs B) Ψ hΨd hΨr hzero))
    (fun B x hx => (hL B).2 x (hind_le B hx))
    (fun B C Ψ hΨ => hA5 F E σ d n hE B C.1 C.2.1 (μs B) (μs C.1) (CT B C) (hCTp B C) Ψ
      hΨ.1 hΨ.2)
    (fun B C θ hθ => (hL B).1 C θ (by simpa [Irr] using hθ))
    (by
      intro B
      refine Submodule.span_le.2 ?_
      intro x hx
      obtain ⟨C, θ', hθ', rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun _ h => h
      exact (hgen B C θ' hθ').2)
    (fun B Ψ hΨ s => hA8 F E σ d n hE B (μs B) Ψ s hΨ.1 hΨ.2)
  exact (isTwistedTraceFunctional_iff (μs B) (leviAut σ B) Φ).2 (key B Φ ⟨hdom, hreg⟩)

/-! ## The Levi product of a block shape with at most one block -/

section Top

variable (E : Type v) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]

/-- Every rank has a block shape whose block-diagonal embedding is a topological group
isomorphism onto `GL_n(E)`: the one-block shape in positive rank and the empty shape in rank
zero. -/
theorem exists_levi_equiv_generalLinear (n : ℕ) :
    ∃ (T : BlockShape n) (e : T.Levi E ≃ₜ* GeneralLinear n E),
      ∀ m, e m = T.leviEmbedding E m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let T : BlockShape 0 := ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
    have hsub : Subsingleton (GeneralLinear 0 E) :=
      ⟨fun a b => Units.ext (Subsingleton.elim (a : Matrix (Fin 0) (Fin 0) E) b)⟩
    have hsubT : Subsingleton (T.Levi E) := ⟨fun a b => funext fun i => i.elim0⟩
    let eM : T.Levi E ≃* GeneralLinear 0 E :=
      { toFun := T.leviEmbedding E
        invFun := fun _ => 1
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_mul' := map_mul _ }
    let e : T.Levi E ≃ₜ* GeneralLinear 0 E :=
      ⟨eM, (T.leviEmbeddingContinuous E).continuous, continuous_const⟩
    exact ⟨T, e, fun _ => rfl⟩
  · let T := CuspidalSupport.LeviAdmissibility.oneBlock n hn
    exact ⟨T, T.singleBlockLeviEquivContinuous rfl E, fun _ => rfl⟩

variable {F : Type u} [CommRing F] [Algebra F E] {E} {n : ℕ}

omit [IsTopologicalRing E] in
theorem levi_equiv_leviAut {T : BlockShape n} (e : T.Levi E ≃ₜ* GeneralLinear n E)
    (he : ∀ m, e m = T.leviEmbedding E m) (σ : E ≃ₐ[F] E) (m : T.Levi E) :
    e (leviAut σ T m) = entrywiseAut σ n (e m) := by
  rw [he, he, entrywiseAut_leviEmbedding]

omit [IsTopologicalRing E] in
theorem levi_equiv_symm_entrywiseAut {T : BlockShape n} (e : T.Levi E ≃ₜ* GeneralLinear n E)
    (he : ∀ m, e m = T.leviEmbedding E m) (σ : E ≃ₐ[F] E) (g : GeneralLinear n E) :
    e.symm (entrywiseAut σ n g) = leviAut σ T (e.symm g) := by
  apply e.injective
  rw [e.apply_symm_apply, levi_equiv_leviAut e he σ, e.apply_symm_apply]

/-- The subgroup `relParabolic E T C` corresponds to the standard parabolic of `C` under the
isomorphism `e`. -/
def relParabolicEquiv {T : BlockShape n} (e : T.Levi E ≃ₜ* GeneralLinear n E)
    (he : ∀ m, e m = T.leviEmbedding E m) (C : BlockShape n) :
    relParabolic E T C ≃* C.parabolic E where
  toFun := relEmbedding E T C
  invFun p := ⟨e.symm p, by
    rw [mem_relParabolic, ← he, e.apply_symm_apply]
    exact p.2⟩
  left_inv q := by
    apply Subtype.ext
    apply e.injective
    change e (e.symm (T.leviEmbedding E q)) = e q
    rw [e.apply_symm_apply, he]
  right_inv p := by
    apply Subtype.ext
    change T.leviEmbedding E (e.symm p) = p
    rw [← he, e.apply_symm_apply]
  map_mul' := map_mul _

end Top

/-! ## Transport of twisted characters along the isomorphism -/

section Transport

variable {G : Type uG} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
  (e : G ≃ₜ* H) (μ₁ : Measure G) [μ₁.IsHaarMeasure] (μ : Measure H) [μ.IsHaarMeasure]
  (hμ : μ₁.map e = μ)

include hμ

/-- Pushing forward the twisted character of the pulled-back representation gives the original
twisted character. -/
theorem pushforward_twistedDistribution_comp {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ H V) (hπ : IsAdmissible π) (hπ₁ : IsAdmissible (π.comp e.toMonoidHom))
    (A : Module.End ℂ V) :
    Distribution.pushforward e.toHomeomorph (twistedDistribution μ₁ (π.comp e.toMonoidHom) hπ₁ A) =
      twistedDistribution μ π hπ A := by
  ext f
  rw [Distribution.pushforward_apply, twistedDistribution_comp_equiv e μ₁ π hπ hπ₁ A]
  have hf : Hecke.TestFunction.pullback e.symm.toHomeomorph
      (Hecke.TestFunction.pullback e.toHomeomorph f) = f := by
    ext x
    exact congrArg (fun y => f y) (e.apply_symm_apply x)
  rw [hf]
  let := e.isHaarMeasure_map μ₁
  exact congrArg (fun D : Distribution H => D f)
    (twistedDistribution_congr_measure (μ := μ₁.map e) (μ' := μ) hμ π hπ A)

/-- The same identity for a representation of `G`, compared with its pushforward along `e`. -/
theorem pushforward_twistedDistribution {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π₁ : Representation ℂ G V) (hπ₁ : IsAdmissible π₁)
    (hπ : IsAdmissible (π₁.comp e.symm.toMonoidHom)) (A : Module.End ℂ V) :
    Distribution.pushforward e.toHomeomorph (twistedDistribution μ₁ π₁ hπ₁ A) =
      twistedDistribution μ (π₁.comp e.symm.toMonoidHom) hπ A := by
  have hπ₁' : IsAdmissible ((π₁.comp e.symm.toMonoidHom).comp e.toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv _ e hπ
  have heq : twistedDistribution μ₁ π₁ hπ₁ A =
      twistedDistribution μ₁ ((π₁.comp e.symm.toMonoidHom).comp e.toMonoidHom) hπ₁' A :=
    twistedDistribution_eq_of_equivariant μ₁ π₁ hπ₁ _ hπ₁' A A (LinearEquiv.refl ℂ V)
      (fun g v => by
        change π₁ g v = π₁ (e.symm (e g)) v
        rw [e.symm_apply_apply]) (fun _ => rfl)
  rw [heq, pushforward_twistedDistribution_comp e μ₁ μ hμ]

end Transport

/-! ## The reduction -/

/-- The twisted trace Paley–Wiener theorem for `GL_n(E)` follows from the six inputs on the Levi
products of `GL_n(E)`. -/
theorem twistedTracePaleyWiener_of_inputs
    (hCT : TwistedLeviInductionTransferStatement.{u, v, z})
    (hJ : TwistedLeviJacquetDescentStatement.{u, v, z})
    (hD : TwistedLeviDiscretePaleyWienerStatement.{u, v, z})
    (hA5 : TwistedLeviGoodRestrictionStatement.{u, v, z})
    (hA7 : TwistedLeviInducedSpanStatement.{u, v, z})
    (hA8 : TwistedLeviTraceGoodStatement.{u, v, z}) :
    TwistedTracePaleyWienerStatement.{u, v, z} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ σ d n hE
  have : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
  have : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
  have : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
  have : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
    levi_locallyCompactSpace_of_finite F E C
  have : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
    levi_totallyDisconnectedSpace_of_finite F E C
  intro μ _ Φ hdom hreg
  obtain ⟨T, e, he⟩ := exists_levi_equiv_generalLinear E n
  let μ₁ : Measure (T.Levi E) := μ.map e.symm
  have : μ₁.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  have hμ : μ₁.map e = μ := by
    have hm1 : Measurable (e : T.Levi E → GeneralLinear n E) := e.continuous.measurable
    have hm2 : Measurable (e.symm : GeneralLinear n E → T.Levi E) := e.symm.continuous.measurable
    change (μ.map e.symm).map e = μ
    rw [Measure.map_map hm1 hm2]
    have : (e : T.Levi E → GeneralLinear n E) ∘ e.symm = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  let μs : ∀ C : BlockShape n, Measure (C.Levi E) :=
    Function.update (fun C => (Measure.haar : Measure (C.Levi E))) T μ₁
  have hμsT : μs T = μ₁ := Function.update_self _ _ _
  have : ∀ C, (μs C).IsHaarMeasure := by
    intro C
    rcases eq_or_ne C T with rfl | h
    · rw [hμsT]
      infer_instance
    · rw [show μs C = Measure.haar from Function.update_of_ne h _ _]
      infer_instance
  let Φ₁ : Module.Dual ℂ (Distribution (T.Levi E)) :=
    Φ ∘ₗ (Distribution.pushforward e.toHomeomorph).toLinearMap
  have hΦ₁ : ∀ D, Φ₁ D = Φ (Distribution.pushforward e.toHomeomorph D) := fun _ => rfl
  -- Compact domination of the transported functional.
  have hdom₁ : IsCompactlyDominatedFunctional.{v, z} (leviAut σ T) μ₁ Φ₁ := by
    obtain ⟨J, hJc, hJ⟩ := hdom
    refine ⟨J.comap e.toMonoidHom e.continuous, (e.toHomeomorph.isCompact_preimage).2 hJc, ?_⟩
    intro W _ _ π₁ hπ₁ hirr hfix A₁
    let π : Representation ℂ (GeneralLinear n E) W := π₁.comp e.symm.toMonoidHom
    have hπ : IsAdmissible π := isAdmissible_comp_continuousMulEquiv π₁ e.symm hπ₁
    have hπirr : Representation.IsIrreducible π :=
      (isIrreducible_comp_continuousMulEquiv_iff π₁ e.symm).2 hirr
    have hπfix : fixedVectors π J.toSubgroup = ⊥ := by
      rw [fixedVectors_comp_eq_map]
      convert hfix using 2
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change e (e.symm y) ∈ J
        rwa [e.apply_symm_apply]
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
    let A : Representation.Equiv π (π.comp (entrywiseAut σ n).toMonoidHom) :=
      Representation.Equiv.mk A₁.toLinearEquiv (fun g => by
        change A₁.toLinearMap ∘ₗ π₁ (e.symm g) = π₁ (e.symm (entrywiseAut σ n g)) ∘ₗ
          A₁.toLinearMap
        rw [levi_equiv_symm_entrywiseAut e he σ]
        exact A₁.isIntertwining' (e.symm g))
    rw [hΦ₁, pushforward_twistedDistribution e μ₁ μ hμ π₁ hπ₁ hπ]
    exact hJ W π hπ hπirr hπfix A
  -- Regularity of the transported functional.
  have hreg₁ : IsLeviSigmaInducedRegularFunctional.{u, v, z} σ T μ₁ Φ₁ := by
    intro C _ X _ _ Ξ hΞ hirr BΞ
    obtain ⟨s, c, hsc⟩ := hreg C X Ξ hΞ hirr BΞ
    refine ⟨s, c, fun ψ hψ hψσ h₁ => ?_⟩
    let eQP := relParabolicEquiv e he C
    have heQP : ∀ q : relParabolic E T C, (eQP q : GeneralLinear n E) = e (q : T.Levi E) :=
      fun q => (he q).symm
    let Ψ := Induction.precomposeSmoothInducedGroupEquiv e eQP heQP
      (σ := (twist ψ Ξ).comp (C.leviProjection E))
      (τ := (twist ψ Ξ).comp (relProjection E T C)) (fun _ => rfl)
    have hIe := isAdmissible_of_equiv Ψ.symm h₁
    have hI := (isAdmissible_comp_continuousMulEquiv_iff _ e).1 hIe
    rw [hΦ₁]
    have hcompat := twistedDistribution_eq_of_equivariant μ₁ _ hIe _ h₁
      (TwistedPaleyWiener.inducedSigmaIntertwiner σ C (twist ψ Ξ)
        (twistTwistedIntertwiner (leviAut σ C) ψ hψσ BΞ)).toLinearMap
      (relInducedSigmaIntertwiner σ T C (twist ψ Ξ)
        (twistTwistedIntertwiner (leviAut σ C) ψ hψσ BΞ)).toLinearMap Ψ.toLinearEquiv
      (fun g f => Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g f)
      (fun f => by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change Induction.eval _ _ (TwistedPaleyWiener.inducedSigmaIntertwiner σ C (twist ψ Ξ)
            (twistTwistedIntertwiner (leviAut σ C) ψ hψσ BΞ) f) (e x) =
          BΞ (Induction.eval _ _ f (e ((leviAut σ T).symm x)))
        rw [TwistedPaleyWiener.eval_inducedSigmaIntertwiner, twistTwistedIntertwiner_apply]
        congr 2
        apply (entrywiseAut σ n).injective
        rw [MulEquiv.apply_symm_apply, ← levi_equiv_leviAut e he σ, MulEquiv.apply_symm_apply])
    rw [← hcompat, pushforward_twistedDistribution_comp e μ₁ μ hμ _ hI hIe]
    exact hsc ψ hψ hψσ hI
  -- Apply the Paley–Wiener theorem on the Levi product of `T`.
  have htr := levi_isTwistedTraceFunctional_of_inputs hCT hJ hD hA5 hA7 hA8 F E σ d n hE μs T Φ₁
    ((isCompactlyDominatedFunctional_congr_measure _ _ hμsT).2 hdom₁)
    ((isLeviSigmaInducedRegularFunctional_congr_measure σ T _ hμsT).2 hreg₁)
  obtain ⟨φ₁, hφ₁⟩ := (isTwistedTraceFunctional_congr_measure _ _ hμsT).1 htr
  refine ⟨Hecke.TestFunction.pullback e.symm.toHomeomorph φ₁, ?_⟩
  intro V _ _ π hπ hirr A
  let π₁ : Representation ℂ (T.Levi E) V := π.comp e.toMonoidHom
  have hπ₁ : IsAdmissible π₁ := isAdmissible_comp_continuousMulEquiv π e hπ
  have hπ₁irr : Representation.IsIrreducible π₁ :=
    (isIrreducible_comp_continuousMulEquiv_iff π e).2 hirr
  let A₁ : Representation.Equiv π₁ (π₁.comp (leviAut σ T).toMonoidHom) :=
    Representation.Equiv.mk A.toLinearEquiv (fun m => by
      change A.toLinearMap ∘ₗ π (e m) = π (e (leviAut σ T m)) ∘ₗ A.toLinearMap
      rw [levi_equiv_leviAut e he σ]
      exact A.isIntertwining' (e m))
  have hK := pushforward_twistedDistribution_comp e μ₁ μ hμ π hπ hπ₁ A.toLinearMap
  have h := hφ₁ V π₁ hπ₁ hπ₁irr A₁
  rw [← hK, Distribution.pushforward_apply]
  have hpb : Hecke.TestFunction.pullback e.toHomeomorph
      (Hecke.TestFunction.pullback e.symm.toHomeomorph φ₁) = φ₁ := by
    ext x
    exact congrArg (fun y => φ₁ y) (e.symm_apply_apply x)
  rw [hpb]
  exact h

/-- The reduction as a proposition: the six inputs on the Levi products of `GL_n(E)` imply the
twisted trace Paley–Wiener theorem for `GL_n(E)`. -/
def TwistedTracePaleyWienerOfLeviInputsStatement.{u', v', z'} : Prop :=
  TwistedLeviPaleyWienerInputsStatement.{u', v', z'} →
    TwistedTracePaleyWienerStatement.{u', v', z'}

theorem twistedTracePaleyWienerOfLeviInputs :
    TwistedTracePaleyWienerOfLeviInputsStatement.{u, v, z} :=
  fun ⟨hCT, hJ, hD, hA5, hA7, hA8⟩ => twistedTracePaleyWiener_of_inputs hCT hJ hD hA5 hA7 hA8

end TwistedLeviPaleyWiener

end Langlands.BaseChange
