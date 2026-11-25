import Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesStatement
import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement
import Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeStatement
import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyStatement
import Langlands.AlgebraicGeometry.Modules.ProjectiveRelativeDivisorFibreHilbertStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

/-! # Proof of the reduction of the Hilbert-polynomial pieces to cohomology and base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Picard.HilbertPolynomialPieces

open Langlands.AlgebraicGeometry.Modules

section FibreIso

variable {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T)

/-- Fibre cohomology is functorial in isomorphisms of the coefficient module. -/
def fibreCohomologyIso {F F' : Y.Modules} (e : F ≅ F') (p : ℕ) :
    fibreCohomology g t F p ≅ fibreCohomology g t F' p :=
  (DerivedSections.relativeCohomology (fibreMap g t) p).mapIso
    ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).mapIso e)

lemma fibreCohomologyDim_congr {F F' : Y.Modules} (e : F ≅ F') (p : ℕ) :
    fibreCohomologyDim g t F p = fibreCohomologyDim g t F' p :=
  (fibreCohomologyIso g t e p).toLinearEquiv.finrank_eq

lemma isZero_fibreCohomology_congr {F F' : Y.Modules} (e : F ≅ F') (p : ℕ) :
    IsZero (fibreCohomology g t F p) ↔ IsZero (fibreCohomology g t F' p) :=
  ⟨fun h ↦ h.of_iso (fibreCohomologyIso g t e p).symm,
    fun h ↦ h.of_iso (fibreCohomologyIso g t e p)⟩

lemma fibreEulerCharacteristic_congr {F F' : Y.Modules} (e : F ≅ F') :
    fibreEulerCharacteristic g t F = fibreEulerCharacteristic g t F' := by
  unfold fibreEulerCharacteristic
  simp_rw [fibreCohomologyDim_congr g t e]

end FibreIso

section Twist

variable {X : Scheme.{u}} (𝓛 : X.Modules)

/-- Twisting respects isomorphisms of the module. -/
def twistIso {F F' : X.Modules} (e : F ≅ F') : (n : ℕ) → twist 𝓛 F n ≅ twist 𝓛 F' n
  | 0 => e
  | n + 1 => whiskerRightIso (twistIso e n) 𝓛

/-- Twisting commutes with tensoring by a second module. -/
def twistTensorIso (F M : X.Modules) : (n : ℕ) → twist 𝓛 (F ⊗ M) n ≅ twist 𝓛 F n ⊗ M
  | 0 => Iso.refl _
  | n + 1 => whiskerRightIso (twistTensorIso F M n) 𝓛 ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (β_ M 𝓛) ≪≫ (α_ _ _ _).symm

/-- Twisting twice adds the exponents. -/
def twistAddIso (F : X.Modules) (a : ℕ) : (b : ℕ) → twist 𝓛 (twist 𝓛 F a) b ≅ twist 𝓛 F (a + b)
  | 0 => Iso.refl _
  | b + 1 => whiskerRightIso (twistAddIso F a b) 𝓛

/-- Inverses in the monoidal category of modules are unique up to isomorphism. -/
def inverseUniqueIso {L M M' : X.Modules} (h : M ⊗ L ≅ 𝟙_ X.Modules)
    (h' : M' ⊗ L ≅ 𝟙_ X.Modules) : M ≅ M' :=
  (ρ_ M).symm ≪≫ whiskerLeftIso M ((β_ L M') ≪≫ h').symm ≪≫ (α_ M L M').symm ≪≫
    whiskerRightIso h M' ≪≫ λ_ M'

/-- Pullback commutes with twisting. -/
def pullbackTwistIso {Y : Scheme.{u}} (φ : Y ⟶ X) {𝓛' : Y.Modules}
    (e : (Scheme.Modules.pullback φ).obj 𝓛 ≅ 𝓛') (F : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback φ).obj (twist 𝓛 F n) ≅
      twist 𝓛' ((Scheme.Modules.pullback φ).obj F) n
  | 0 => Iso.refl _
  | n + 1 => Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫ tensorIso (pullbackTwistIso φ e F n) e

end Twist

section Trivial

/-- An invertible module on a scheme with exactly one point is trivial. -/
lemma nonempty_iso_unit_of_subsingleton {X : Scheme.{u}} [Subsingleton X] (x : X)
    {M : X.Modules} (hM : Scheme.Modules.IsInvertibleFLT M) : Nonempty (M ≅ 𝟙_ X.Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  have hU : U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rwa [Subsingleton.elim y x]
  subst hU
  exact ⟨(Scheme.Modules.pullbackId X).symm.app M ≪≫
    (Scheme.Modules.pullbackCongr X.topIso.inv_hom_id).symm.app M ≪≫
    ((Scheme.Modules.pullbackComp X.topIso.inv X.topIso.hom).app M).symm ≪≫
    (Scheme.Modules.pullback X.topIso.inv).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso X.topIso.inv⟩

instance (T : Scheme.{u}) (t : T) : Subsingleton (Spec (T.residueField t)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (T.residueField t)))

variable {Y T : Scheme.{u}}

/-- On every fibre, the pullback of an invertible module from the base is trivial. -/
lemma nonempty_fibreModule_pullback_iso_unit (g : Y ⟶ T) (t : T) {N : T.Modules}
    (hN : Scheme.Modules.IsInvertibleFLT N) :
    Nonempty (fibreModule g t ((Scheme.Modules.pullback g).obj N) ≅
      𝟙_ (pullback g (T.fromSpecResidueField t)).Modules) := by
  obtain ⟨e⟩ := nonempty_iso_unit_of_subsingleton
    (X := Spec (T.residueField t)) (default : PrimeSpectrum (T.residueField t))
    (Scheme.Modules.IsInvertible.pullbackFLT (hL := hN) (T.fromSpecResidueField t))
  exact ⟨(Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr pullback.condition).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

end Trivial

section Misc

/-- Rational polynomials of degree at most `N` that agree at `0, …, N` are equal. -/
lemma polynomial_eq_of_eval_eq {N : ℕ} {P Q : Polynomial ℚ} (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N) (h : ∀ n : ℕ, n ≤ N → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q :=
  Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q (f := fun i : Fin (N + 1) ↦ ((i : ℕ) : ℚ))
    (fun i j hij ↦ Fin.ext (by simpa using hij)) (fun i ↦ h i (Nat.lt_succ_iff.mp i.2))
    (by simp only [Fintype.card_fin]; omega)

variable {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T)

/-- A finite-dimensional fibre cohomology space is zero iff its dimension is zero. -/
lemma isZero_fibreCohomology_iff {F : Y.Modules} {p : ℕ}
    [Module.Finite (T.residueField t) (fibreCohomology g t F p)] :
    IsZero (fibreCohomology g t F p) ↔ fibreCohomologyDim g t F p = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton, fibreCohomologyDim, Module.finrank_zero_iff]

/-- If all higher fibre cohomology vanishes, the Euler characteristic is `dim H⁰`. -/
lemma fibreEulerCharacteristic_eq_of_isZero {F : Y.Modules}
    (h : ∀ p : ℕ, 0 < p → IsZero (fibreCohomology g t F p)) :
    fibreEulerCharacteristic g t F = fibreCohomologyDim g t F 0 := by
  unfold fibreEulerCharacteristic
  rw [finsum_eq_single _ 0]
  · simp
  · intro p hp
    have hz := h p (Nat.pos_of_ne_zero hp)
    have : Subsingleton (fibreCohomology g t F p) := ModuleCat.isZero_iff_subsingleton.mp hz
    simp [fibreCohomologyDim, Module.finrank_zero_of_subsingleton]

/-- Fibre cohomology only depends on the restriction of the module to the fibre. -/
def fibreCohomologyIsoOfFibreModule {F F' : Y.Modules}
    (e : fibreModule g t F ≅ fibreModule g t F') (p : ℕ) :
    fibreCohomology g t F p ≅ fibreCohomology g t F' p :=
  (DerivedSections.relativeCohomology (fibreMap g t) p).mapIso e

/-- The restriction to a fibre is monoidal. -/
def fibreModuleTensorIso (F M : Y.Modules) :
    fibreModule g t (F ⊗ M) ≅ fibreModule g t F ⊗ fibreModule g t M :=
  Scheme.Modules.pullbackTensorObjIso _ F M

/-- Tensoring with the pullback of an invertible module on the base does not change fibres. -/
lemma nonempty_fibreModule_tensor_pullback_iso (F : Y.Modules) {N : T.Modules}
    (hN : Scheme.Modules.IsInvertibleFLT N) :
    Nonempty (fibreModule g t (F ⊗ (Scheme.Modules.pullback g).obj N) ≅ fibreModule g t F) := by
  obtain ⟨e⟩ := nonempty_fibreModule_pullback_iso_unit g t hN
  exact ⟨fibreModuleTensorIso g t _ _ ≪≫ whiskerLeftIso _ e ≪≫ ρ_ _⟩

/-- Rational polynomials agreeing at all natural numbers are equal. -/
lemma polynomial_eq_of_forall_nat {P Q : Polynomial ℚ}
    (h : ∀ n : ℕ, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q :=
  Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (n : ℚ)) Nat.cast_injective h)

/-- Fibre restriction of an isomorphism of modules. -/
def fibreModuleIso {F F' : Y.Modules} (e : F ≅ F') : fibreModule g t F ≅ fibreModule g t F' :=
  (Scheme.Modules.pullback _).mapIso e

lemma fibreEulerCharacteristic_congr_fibre {F F' : Y.Modules}
    (e : fibreModule g t F ≅ fibreModule g t F') :
    fibreEulerCharacteristic g t F = fibreEulerCharacteristic g t F' := by
  unfold fibreEulerCharacteristic
  simp_rw [fibreCohomologyDim, (fibreCohomologyIsoOfFibreModule g t e _).toLinearEquiv.finrank_eq]

lemma isZero_fibreCohomology_congr_fibre {F F' : Y.Modules}
    (e : fibreModule g t F ≅ fibreModule g t F') (p : ℕ) :
    IsZero (fibreCohomology g t F p) ↔ IsZero (fibreCohomology g t F' p) :=
  ⟨fun h ↦ h.of_iso (fibreCohomologyIsoOfFibreModule g t e p).symm,
    fun h ↦ h.of_iso (fibreCohomologyIsoOfFibreModule g t e p)⟩

end Misc

section Invertible

variable {X : Scheme.{u}}

lemma isInvertible_twist {𝓛 F : X.Modules} (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛)
    (hF : Scheme.Modules.IsInvertibleFLT F) : ∀ n : ℕ, Scheme.Modules.IsInvertibleFLT (twist 𝓛 F n)
  | 0 => hF
  | n + 1 => Scheme.Modules.IsInvertible.tensor_monoidalV2 (isInvertible_twist h𝓛 hF n) h𝓛

end Invertible

section Witness

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (𝓛X : X.Modules)

/-- The pullback `𝓛` of `𝓛X` to `X_T`. -/
abbrev twistSheaf (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A)) :
    (pullback f s).Modules :=
  (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X

/-- The piece of the decomposition, as a set of points of `T`. -/
def pieceSet (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (L : (pullback f s).Modules) (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) : Set T :=
  {t | (∃ M : (pullback f s).Modules, Scheme.Modules.IsInvertibleFLT M ∧
        Nonempty (M ⊗ L ≅ 𝟙_ (pullback f s).Modules) ∧
        ∀ n : ℕ, ((fibreEulerCharacteristic (pullback.snd f s) t
          (twist (twistSheaf f 𝓛X T s) M n) : ℤ) : ℚ) = c.1.eval (n : ℚ)) ∧
      (∀ n : ℕ, ((fibreEulerCharacteristic (pullback.snd f s) t
          (twist (twistSheaf f 𝓛X T s) (𝟙_ (pullback f s).Modules) n) : ℤ) : ℚ) =
            c.2.eval (n : ℚ)) ∧
      ∀ n : ℕ, m ≤ n →
        (∀ p : ℕ, 0 < p → IsZero (fibreCohomology (pullback.snd f s) t
          (twist (twistSheaf f 𝓛X T s) L n) p)) ∧
        ¬ IsZero (fibreCohomology (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) L n) 0)}

/-- The piece of the decomposition, an open of `T`. -/
def piece (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (L : (pullback f s).Modules) (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) : T.Opens :=
  TopologicalSpace.Opens.interior (pieceSet f 𝓛X T s L c m)

/-- The Hilbert polynomial of the divisors attached to the piece `(c, m)`. -/
def hilbertPolynomial (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) : Polynomial ℚ :=
  c.2 - c.1.comp (Polynomial.X - Polynomial.C (m : ℚ))

lemma pieceSet_mono (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (L : (pullback f s).Modules) (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) :
    pieceSet f 𝓛X T s L c m ⊆ pieceSet f 𝓛X T s L c (m + 1) :=
  fun _ ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, fun n hn ↦ h3 n (Nat.le_of_succ_le hn)⟩

end Witness

section Openness

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of A)} {𝓛X : X.Modules} {N : ℕ} {𝔓 : 𝓛X.ProjPresentation f N}

/-- Near every point, the whole sequence of fibre Euler characteristics of the twists of an
invertible module is constant. -/
lemma exists_isOpen_eulerCharacteristic_eq
    (hSC : ProperFlatFibreCohomologySemicontinuityStatement.{u})
    (hPT : ProjectiveFibreTwistCohomologyStatement.{u})
    (hprop : IsProper f) (hflat : Flat f) (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X)
    (h𝔓 : IsClosedImmersion 𝔓.toProj)
    (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
    {F : (pullback f s).Modules} (hF : Scheme.Modules.IsInvertibleFLT F) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ n : ℕ,
      fibreEulerCharacteristic (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) F n) =
        fibreEulerCharacteristic (pullback.snd f s) t₀ (twist (twistSheaf f 𝓛X T s) F n) := by
  have hPT3 := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s F hF).2.2
  choose P hPdeg hP using hPT3
  have h𝓛T : Scheme.Modules.IsInvertibleFLT (twistSheaf f 𝓛X T s) := Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _
  have hSCn : ∀ n : ℕ, ∃ V : T.Opens, t₀ ∈ V ∧ ∀ t ∈ V,
      fibreEulerCharacteristic (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) F n) =
        fibreEulerCharacteristic (pullback.snd f s) t₀ (twist (twistSheaf f 𝓛X T s) F n) :=
    fun n ↦ (hSC T (pullback f s) (pullback.snd f s) inferInstance inferInstance _
      (isInvertible_twist h𝓛T hF n)).2.2.2 t₀
  choose V hV₀ hV using hSCn
  refine ⟨⋂ n ∈ Finset.range (N + 1), (V n : Set T),
    isOpen_biInter_finset (fun n _ ↦ (V n).isOpen), ?_, ?_⟩
  · simp only [Set.mem_iInter]
    exact fun n _ ↦ hV₀ n
  · intro t ht n
    simp only [Set.mem_iInter] at ht
    have hPeq : P t = P t₀ := polynomial_eq_of_eval_eq (hPdeg t) (hPdeg t₀) (fun k hk ↦ by
      rw [← hP t k, ← hP t₀ k, hV k t (ht k (Finset.mem_range.mpr (by omega)))])
    have h1 := hP t n
    rw [hPeq, ← hP t₀ n] at h1
    exact_mod_cast h1

/-- If the higher fibre cohomology of all twists `L(n)`, `n ≥ m`, vanishes at `t₀`, it vanishes
near `t₀`. -/
lemma exists_isOpen_vanishing
    (hSC : ProperFlatFibreCohomologySemicontinuityStatement.{u})
    (hPT : ProjectiveFibreTwistCohomologyStatement.{u})
    (hprop : IsProper f) (hflat : Flat f) (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X)
    (h𝔓 : IsClosedImmersion 𝔓.toProj)
    (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
    {L : (pullback f s).Modules} (hL : Scheme.Modules.IsInvertibleFLT L) (m : ℕ) (t₀ : T)
    (h₀ : ∀ n : ℕ, m ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (fibreCohomology (pullback.snd f s) t₀ (twist (twistSheaf f 𝓛X T s) L n) p)) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ n : ℕ, m ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (fibreCohomology (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) L n) p) := by
  have h𝓛T : Scheme.Modules.IsInvertibleFLT (twistSheaf f 𝓛X T s) := Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _
  obtain ⟨V₁, hV₁t, n₀, hV₁⟩ := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s L hL).1 t₀
  have hSCn := fun n : ℕ ↦ hSC T (pullback f s) (pullback.snd f s) inferInstance inferInstance _
    (isInvertible_twist h𝓛T hL n)
  choose V₂ hV₂t b hV₂ using fun n : ℕ ↦ (hSCn n).2.1 t₀
  refine ⟨(V₁ : Set T) ∩ ⋂ n ∈ Finset.Ico m n₀, ((V₂ n : Set T) ∩
      ⋂ p ∈ Finset.Ico 1 (b n),
        {t | fibreCohomologyDim (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) L n) p < 1}),
    V₁.isOpen.inter (isOpen_biInter_finset fun n _ ↦ (V₂ n).isOpen.inter
      (isOpen_biInter_finset fun p _ ↦ (hSCn n).2.2.1 p 1)), ?_, ?_⟩
  · refine ⟨hV₁t, ?_⟩
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    intro n hn
    refine ⟨hV₂t n, fun p hp ↦ ?_⟩
    rw [Finset.mem_Ico] at hn hp
    have : Module.Finite _ (fibreCohomology (pullback.snd f s) t₀
        (twist (twistSheaf f 𝓛X T s) L n) p) := (hSCn n).1 t₀ p
    rw [(isZero_fibreCohomology_iff _ _).mp (h₀ n hn.1 p hp.1)]
    exact Nat.one_pos
  · rintro t ⟨ht₁, ht⟩ n hmn p hp
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
    by_cases hn : n₀ ≤ n
    · exact hV₁ t ht₁ n p hn hp
    · have hnI : n ∈ Finset.Ico m n₀ := Finset.mem_Ico.mpr ⟨hmn, by omega⟩
      obtain ⟨htV₂, htp⟩ := ht n hnI
      by_cases hb : b n ≤ p
      · exact hV₂ n t htV₂ p hb
      · have : Module.Finite _ (fibreCohomology (pullback.snd f s) t
            (twist (twistSheaf f 𝓛X T s) L n) p) := (hSCn n).1 t p
        rw [isZero_fibreCohomology_iff]
        have := htp p (Finset.mem_Ico.mpr ⟨hp, by omega⟩)
        omega

/-- The pieces are open. -/
lemma isOpen_pieceSet
    (hSC : ProperFlatFibreCohomologySemicontinuityStatement.{u})
    (hPT : ProjectiveFibreTwistCohomologyStatement.{u})
    (hprop : IsProper f) (hflat : Flat f) (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X)
    (h𝔓 : IsClosedImmersion 𝔓.toProj)
    (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
    {L : (pullback f s).Modules} (hL : Scheme.Modules.IsInvertibleFLT L)
    (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) :
    IsOpen (pieceSet f 𝓛X T s L c m) := by
  have h𝓛T : Scheme.Modules.IsInvertibleFLT (twistSheaf f 𝓛X T s) := Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _
  have hSCn := fun n : ℕ ↦ hSC T (pullback f s) (pullback.snd f s) inferInstance inferInstance _
    (isInvertible_twist h𝓛T hL n)
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ⟨⟨M, hM, hML, hMφ⟩, hψ, hvan⟩
  obtain ⟨V₁, hV₁o, hV₁t, hV₁⟩ :=
    exists_isOpen_eulerCharacteristic_eq hSC hPT hprop hflat h𝓛 h𝔓 T s hM t₀
  obtain ⟨V₂, hV₂o, hV₂t, hV₂⟩ := exists_isOpen_eulerCharacteristic_eq hSC hPT hprop hflat h𝓛
    h𝔓 T s (F := 𝟙_ (pullback f s).Modules) (Scheme.Modules.isInvertible_unit _) t₀
  obtain ⟨V₃, hV₃o, hV₃t, hV₃⟩ :=
    exists_isOpen_eulerCharacteristic_eq hSC hPT hprop hflat h𝓛 h𝔓 T s hL t₀
  obtain ⟨V₄, hV₄o, hV₄t, hV₄⟩ := exists_isOpen_vanishing hSC hPT hprop hflat h𝓛 h𝔓 T s hL m
    t₀ (fun n hn ↦ (hvan n hn).1)
  refine ⟨V₁ ∩ V₂ ∩ V₃ ∩ V₄, ?_, ((hV₁o.inter hV₂o).inter hV₃o).inter hV₄o,
    ⟨⟨⟨hV₁t, hV₂t⟩, hV₃t⟩, hV₄t⟩⟩
  rintro t ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
  refine ⟨⟨M, hM, hML, fun n ↦ by rw [hV₁ t h₁ n]; exact hMφ n⟩,
    fun n ↦ by rw [hV₂ t h₂ n]; exact hψ n, fun n hn ↦ ⟨hV₄ t h₄ n hn, fun hz ↦ ?_⟩⟩
  have : Module.Finite _ (fibreCohomology (pullback.snd f s) t
      (twist (twistSheaf f 𝓛X T s) L n) 0) := (hSCn n).1 t 0
  have : Module.Finite _ (fibreCohomology (pullback.snd f s) t₀
      (twist (twistSheaf f 𝓛X T s) L n) 0) := (hSCn n).1 t₀ 0
  have e₁ := fibreEulerCharacteristic_eq_of_isZero _ t (hV₄ t h₄ n hn)
  have e₀ := fibreEulerCharacteristic_eq_of_isZero _ t₀ (fun p hp ↦ (hvan n hn).1 p hp)
  have hχ := hV₃ t h₃ n
  rw [e₁, e₀] at hχ
  have hd : fibreCohomologyDim (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) L n) 0 = 0 :=
    (isZero_fibreCohomology_iff _ _).mp hz
  apply (hvan n hn).2
  rw [isZero_fibreCohomology_iff]
  omega

/-- Every point lies in some piece. -/
lemma exists_mem_pieceSet
    (hPT : ProjectiveFibreTwistCohomologyStatement.{u})
    (hprop : IsProper f) (hflat : Flat f) [GeometricallyIntegral f]
    (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X) (h𝔓 : IsClosedImmersion 𝔓.toProj)
    (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of A))
    {L : (pullback f s).Modules} (hL : Scheme.Modules.IsInvertibleFLT L) (t : T) :
    ∃ (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ), t ∈ pieceSet f 𝓛X T s L c m := by
  obtain ⟨hD, ⟨eD⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hL
  have hPTD := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s _ hD).2.2 t
  have hPT1 := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s _
    (Scheme.Modules.isInvertible_unit (pullback f s))).2.2 t
  obtain ⟨φ, -, hφ⟩ := hPTD
  obtain ⟨ψ, -, hψ⟩ := hPT1
  obtain ⟨V, hVt, n₀, hn₀⟩ := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s L hL).1 t
  have hne : Nonempty (pullback (C := Scheme.{u}) (pullback.snd f s)
      (T.fromSpecResidueField t)) :=
    inferInstanceAs (Nonempty ((pullback.snd f s).fiber t))
  obtain ⟨n₁, hn₁⟩ := (hPT A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 T s L hL).2.1 t hne
  refine ⟨(φ, ψ), max n₀ n₁, ⟨L.dualFLT, hD, ⟨β_ _ _ ≪≫ eD⟩, hφ⟩, hψ,
    fun n hn ↦ ⟨fun p hp ↦ hn₀ t hVt n p (le_of_max_le_left hn) hp,
      hn₁ n (le_of_max_le_right hn)⟩⟩

omit [IsNoetherianRing A] in
/-- Pieces with different indices are disjoint. -/
lemma pieceSet_disjoint (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (L : (pullback f s).Modules) {c c' : Polynomial ℚ × Polynomial ℚ} (hcc' : c ≠ c')
    (m m' : ℕ) : Disjoint (pieceSet f 𝓛X T s L c m) (pieceSet f 𝓛X T s L c' m') := by
  rw [Set.disjoint_left]
  rintro t ⟨⟨M, -, ⟨eM⟩, hM⟩, hψ, -⟩ ⟨⟨M', -, ⟨eM'⟩, hM'⟩, hψ', -⟩
  apply hcc'
  have e := inverseUniqueIso eM eM'
  refine Prod.ext (polynomial_eq_of_forall_nat fun n ↦ ?_)
    (polynomial_eq_of_forall_nat fun n ↦ by rw [← hψ n, ← hψ' n])
  rw [← hM n, ← hM' n, fibreEulerCharacteristic_congr _ _ (twistIso _ e n)]

omit [IsNoetherianRing A] in
/-- Twisting by the pullback of an invertible module on the base can only enlarge the pieces. -/
lemma pieceSet_subset_of_iso (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    {L L' : (pullback f s).Modules} {N : T.Modules} (hN : Scheme.Modules.IsInvertibleFLT N)
    (e : L ≅ L' ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N)
    (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) :
    pieceSet f 𝓛X T s L c m ⊆ pieceSet f 𝓛X T s L' c m := by
  rintro t ⟨⟨M, hM, ⟨eM⟩, hMφ⟩, hψ, hvan⟩
  have hfib : ∀ (F : (pullback f s).Modules) (n : ℕ),
      Nonempty (fibreModule (pullback.snd f s) t
        (twist (twistSheaf f 𝓛X T s) (F ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N) n) ≅
        fibreModule (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) F n)) := fun F n ↦ by
    obtain ⟨e'⟩ := nonempty_fibreModule_tensor_pullback_iso (pullback.snd f s) t
      (twist (twistSheaf f 𝓛X T s) F n) hN
    exact ⟨fibreModuleIso _ _ (twistTensorIso _ _ _ n) ≪≫ e'⟩
  have hL : ∀ n : ℕ, Nonempty (fibreModule (pullback.snd f s) t
      (twist (twistSheaf f 𝓛X T s) L n) ≅
      fibreModule (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) L' n)) := fun n ↦ by
    obtain ⟨e'⟩ := hfib L' n
    exact ⟨fibreModuleIso _ _ (twistIso _ e n) ≪≫ e'⟩
  refine ⟨⟨M ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N,
    Scheme.Modules.IsInvertible.tensor_monoidalV2 hM (Scheme.Modules.IsInvertible.pullbackFLT (hL := hN) _),
    ⟨α_ _ _ _ ≪≫ whiskerLeftIso M (β_ _ _ ≪≫ e.symm) ≪≫ eM⟩, fun n ↦ ?_⟩, hψ,
    fun n hn ↦ ⟨fun p hp ↦ ?_, ?_⟩⟩
  · obtain ⟨e'⟩ := hfib M n
    rw [fibreEulerCharacteristic_congr_fibre _ _ e']
    exact hMφ n
  · obtain ⟨e'⟩ := hL n
    exact (isZero_fibreCohomology_congr_fibre _ _ e' p).mp ((hvan n hn).1 p hp)
  · obtain ⟨e'⟩ := hL n
    rw [← isZero_fibreCohomology_congr_fibre _ _ e' 0]
    exact (hvan n hn).2

omit [IsNoetherianRing A] in
/-- The pieces only depend on the class of `L` modulo pullbacks of invertible modules on the
base. -/
lemma pieceSet_eq_of_iso (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    {L L' : (pullback f s).Modules} {N : T.Modules} (hN : Scheme.Modules.IsInvertibleFLT N)
    (e : L ≅ L' ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N)
    (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) :
    pieceSet f 𝓛X T s L c m = pieceSet f 𝓛X T s L' c m := by
  obtain ⟨hND, ⟨eN⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hN
  refine (pieceSet_subset_of_iso (f := f) (𝓛X := 𝓛X) T s hN e c m).antisymm
    (pieceSet_subset_of_iso (f := f) (𝓛X := 𝓛X) T s hND ?_ c m)
  exact (whiskerRightIso e _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso L' ((Scheme.Modules.pullbackTensorObjIso _ N N.dualFLT).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eN ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
    ρ_ L').symm

omit [IsNoetherianRing A] in
/-- The base-change square of the family along `h : T' ⟶ T` is cartesian. -/
lemma isPullback_baseChange {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A))
    (h : T' ⟶ T) :
    IsPullback (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))
      (pullback.snd f (h ≫ s)) (pullback.snd f s) h := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f s) (v₁₃ := f) (h₂₂ := s) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f s)
  have : pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp) ≫ pullback.fst f s =
      pullback.fst f (h ≫ s) := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [this]
  exact IsPullback.of_hasPullback f (h ≫ s)

omit [IsNoetherianRing A] in
/-- The twisting sheaf is compatible with base change. -/
def twistSheafBaseChangeIso {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) :
    (Scheme.Modules.pullback (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj
        (twistSheaf f 𝓛X T s) ≅ twistSheaf f 𝓛X T' (h ≫ s) :=
  (Scheme.Modules.pullbackComp _ _).app 𝓛X ≪≫
    (Scheme.Modules.pullbackCongr ((pullback.lift_fst _ _ _).trans (Category.comp_id _))).app 𝓛X

omit [IsNoetherianRing A] in
/-- Fibre cohomology dimensions of twists are compatible with base change. -/
lemma fibreCohomologyDim_twist_baseChange
    (hFE : ProperFibreCohomologyDimBaseChangeStatement.{u}) (hprop : IsProper f)
    (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X) {T T' : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) {F : (pullback f s).Modules}
    (hF : Scheme.Modules.IsInvertibleFLT F) (n : ℕ) (t' : T') (p : ℕ) :
    fibreCohomologyDim (pullback.snd f (h ≫ s)) t' (twist (twistSheaf f 𝓛X T' (h ≫ s))
        ((Scheme.Modules.pullback
          (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj F) n) p =
      fibreCohomologyDim (pullback.snd f s) (h t') (twist (twistSheaf f 𝓛X T s) F n) p := by
  rw [← fibreCohomologyDim_congr _ _
    (pullbackTwistIso _ _ (twistSheafBaseChangeIso (f := f) (𝓛X := 𝓛X) s h) F n)]
  exact hFE T T' (pullback f s) (pullback f (h ≫ s)) (pullback.snd f s) h
    (pullback.snd f (h ≫ s)) _ (isPullback_baseChange s h) inferInstance _
    (isInvertible_twist (Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _) hF n) t' p

omit [IsNoetherianRing A] in
lemma fibreEulerCharacteristic_twist_baseChange
    (hFE : ProperFibreCohomologyDimBaseChangeStatement.{u}) (hprop : IsProper f)
    (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X) {T T' : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) {F : (pullback f s).Modules}
    (hF : Scheme.Modules.IsInvertibleFLT F) (n : ℕ) (t' : T') :
    fibreEulerCharacteristic (pullback.snd f (h ≫ s)) t' (twist (twistSheaf f 𝓛X T' (h ≫ s))
        ((Scheme.Modules.pullback
          (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj F) n) =
      fibreEulerCharacteristic (pullback.snd f s) (h t') (twist (twistSheaf f 𝓛X T s) F n) := by
  unfold fibreEulerCharacteristic
  simp_rw [fibreCohomologyDim_twist_baseChange hFE hprop h𝓛 s h hF n t']

omit [IsNoetherianRing A] in
lemma isZero_fibreCohomology_twist_baseChange
    (hSC : ProperFlatFibreCohomologySemicontinuityStatement.{u})
    (hFE : ProperFibreCohomologyDimBaseChangeStatement.{u}) (hprop : IsProper f)
    (hflat : Flat f) (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X) {T T' : Scheme.{u}}
    [IsLocallyNoetherian T] [IsLocallyNoetherian T']
    (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) {F : (pullback f s).Modules}
    (hF : Scheme.Modules.IsInvertibleFLT F) (n : ℕ) (t' : T') (p : ℕ) :
    IsZero (fibreCohomology (pullback.snd f (h ≫ s)) t' (twist (twistSheaf f 𝓛X T' (h ≫ s))
        ((Scheme.Modules.pullback
          (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj F) n) p) ↔
      IsZero (fibreCohomology (pullback.snd f s) (h t') (twist (twistSheaf f 𝓛X T s) F n) p) := by
  have := (hSC T (pullback f s) (pullback.snd f s) inferInstance inferInstance
    (twist (twistSheaf f 𝓛X T s) F n)
    (isInvertible_twist (Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) (pullback.fst f s)) hF n)).1 (h t') p
  have := (hSC T' (pullback f (h ≫ s)) (pullback.snd f (h ≫ s)) inferInstance inferInstance
    (twist (twistSheaf f 𝓛X T' (h ≫ s)) ((Scheme.Modules.pullback
      (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj F) n)
    (isInvertible_twist (Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) (pullback.fst f (h ≫ s))) (Scheme.Modules.IsInvertible.pullbackFLT (hL := hF) _) n)).1 t' p
  rw [isZero_fibreCohomology_iff, isZero_fibreCohomology_iff,
    fibreCohomologyDim_twist_baseChange hFE hprop h𝓛 s h hF n t' p]

omit [IsNoetherianRing A] in
/-- The pieces are compatible with base change between locally noetherian schemes. -/
lemma pieceSet_baseChange
    (hSC : ProperFlatFibreCohomologySemicontinuityStatement.{u})
    (hFE : ProperFibreCohomologyDimBaseChangeStatement.{u}) (hprop : IsProper f)
    (hflat : Flat f) (h𝓛 : Scheme.Modules.IsInvertibleFLT 𝓛X) {T T' : Scheme.{u}}
    [IsLocallyNoetherian T] [IsLocallyNoetherian T']
    (s : T ⟶ Spec (CommRingCat.of A)) (h : T' ⟶ T) {L : (pullback f s).Modules}
    (hL : Scheme.Modules.IsInvertibleFLT L) (c : Polynomial ℚ × Polynomial ℚ) (m : ℕ) :
    pieceSet f 𝓛X T' (h ≫ s) ((Scheme.Modules.pullback
        (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj L) c m =
      h.base ⁻¹' pieceSet f 𝓛X T s L c m := by
  ext t'
  simp only [Set.mem_preimage]
  obtain ⟨hD, ⟨eD⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hL
  have hψ_eq : ∀ n : ℕ,
      fibreEulerCharacteristic (pullback.snd f (h ≫ s)) t'
        (twist (twistSheaf f 𝓛X T' (h ≫ s)) (𝟙_ (pullback f (h ≫ s)).Modules) n) =
      fibreEulerCharacteristic (pullback.snd f s) (h t')
        (twist (twistSheaf f 𝓛X T s) (𝟙_ (pullback f s).Modules) n) := fun n ↦ by
    rw [← fibreEulerCharacteristic_twist_baseChange hFE hprop h𝓛 s h
      (F := 𝟙_ (pullback f s).Modules) (Scheme.Modules.isInvertible_unit _) n t']
    exact fibreEulerCharacteristic_congr _ _
      (twistIso _ (Scheme.Modules.pullbackTensorUnitObjIso _).symm n)
  constructor
  · rintro ⟨⟨M', hM', ⟨eM'⟩, hφ'⟩, hψ', hvan'⟩
    have einv : (Scheme.Modules.pullback
        (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj L.dualFLT ⊗
        (Scheme.Modules.pullback
          (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj L ≅
          𝟙_ (pullback f (h ≫ s)).Modules :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso (β_ _ _ ≪≫ eD) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    refine ⟨⟨L.dualFLT, hD, ⟨β_ _ _ ≪≫ eD⟩, fun n ↦ ?_⟩, fun n ↦ ?_,
      fun n hn ↦ ⟨fun p hp ↦ ?_, ?_⟩⟩
    · rw [← fibreEulerCharacteristic_twist_baseChange hFE hprop h𝓛 s h hD n t',
        fibreEulerCharacteristic_congr _ _ (twistIso _ (inverseUniqueIso einv eM') n)]
      exact hφ' n
    · rw [← hψ_eq n]
      exact hψ' n
    · exact (isZero_fibreCohomology_twist_baseChange hSC hFE hprop hflat h𝓛 s h hL n t' p).mp
        ((hvan' n hn).1 p hp)
    · rw [← isZero_fibreCohomology_twist_baseChange hSC hFE hprop hflat h𝓛 s h hL n t' 0]
      exact (hvan' n hn).2
  · rintro ⟨⟨M, hM, ⟨eM⟩, hφ⟩, hψ, hvan⟩
    refine ⟨⟨_, Scheme.Modules.IsInvertible.pullbackFLT (hL := hM) _, ⟨(Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso eM ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _⟩,
      fun n ↦ ?_⟩, fun n ↦ ?_, fun n hn ↦ ⟨fun p hp ↦ ?_, ?_⟩⟩
    · rw [fibreEulerCharacteristic_twist_baseChange hFE hprop h𝓛 s h hM n t']
      exact hφ n
    · rw [hψ_eq n]
      exact hψ n
    · exact (isZero_fibreCohomology_twist_baseChange hSC hFE hprop hflat h𝓛 s h hL n t' p).mpr
        ((hvan n hn).1 p hp)
    · rw [isZero_fibreCohomology_twist_baseChange hSC hFE hprop hflat h𝓛 s h hL n t' 0]
      exact (hvan n hn).2

omit [IsNoetherianRing A] in
/-- If `K ⊗ (L(m) ⊗ g^*N) ≅ 𝒪` and `M` is an inverse of `L`, then on every fibre the twists
`K(j + m)` and `M(j)` have the same Euler characteristic. -/
lemma fibreEulerCharacteristic_twist_of_inverse (T : Scheme.{u})
    (s : T ⟶ Spec (CommRingCat.of A)) {L M K : (pullback f s).Modules} {N : T.Modules}
    (hN : Scheme.Modules.IsInvertibleFLT N) (eM : M ⊗ L ≅ 𝟙_ (pullback f s).Modules) (m : ℕ)
    (eK : K ⊗ (twist (twistSheaf f 𝓛X T s) L m ⊗
      (Scheme.Modules.pullback (pullback.snd f s)).obj N) ≅ 𝟙_ (pullback f s).Modules)
    (t : T) (j : ℕ) :
    fibreEulerCharacteristic (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) K (j + m)) =
      fibreEulerCharacteristic (pullback.snd f s) t (twist (twistSheaf f 𝓛X T s) M j) := by
  set 𝓛 := twistSheaf f 𝓛X T s
  set G := (Scheme.Modules.pullback (pullback.snd f s)).obj N
  set P := twist 𝓛 (𝟙_ (pullback f s).Modules) m
  have eP : ∀ F : (pullback f s).Modules, twist 𝓛 F m ≅ P ⊗ F := fun F ↦
    twistIso 𝓛 (λ_ F).symm m ≪≫ twistTensorIso 𝓛 _ F m
  let eM₁ : ((K ⊗ G) ⊗ P) ⊗ L ≅ 𝟙_ (pullback f s).Modules :=
    α_ _ _ _ ≪≫ whiskerLeftIso _ (eP L).symm ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso K (β_ G _) ≪≫ eK
  let eTw : twist 𝓛 ((K ⊗ G) ⊗ P) j ≅ twist 𝓛 K (j + m) ⊗ G :=
    twistTensorIso 𝓛 _ P j ≪≫ β_ _ _ ≪≫ (eP _).symm ≪≫ twistAddIso 𝓛 _ j m ≪≫
      twistTensorIso 𝓛 K G (j + m)
  obtain ⟨eG⟩ := nonempty_fibreModule_tensor_pullback_iso (pullback.snd f s) t
    (twist 𝓛 K (j + m)) hN
  rw [fibreEulerCharacteristic_congr _ _ (twistIso 𝓛 (inverseUniqueIso eM eM₁) j),
    fibreEulerCharacteristic_congr_fibre _ _ (fibreModuleIso _ _ eTw ≪≫ eG)]

/-- A locally free module of rank one is inverse to its (Library) dual. -/
def tensorDualIso {Z : Scheme.{u}} (M : Z.Modules) (hM : IsLocallyFreeRankOne M) :
    M ⊗ Langlands.Scheme.Modules.dual M ≅ 𝟙_ Z.Modules :=
  (Scheme.Modules.tensorIsoSheafify M (Langlands.Scheme.Modules.dual M)).symm ≪≫
    @asIso _ _ _ _ (Langlands.Scheme.Modules.dualTensorEval M)
      (Langlands.Scheme.Modules.isIso_dualTensorEval hM)

end Openness

end Langlands.AlgebraicGeometry.Picard.HilbertPolynomialPieces

namespace Langlands.AlgebraicGeometry.Picard

open HilbertPolynomialPieces Langlands.AlgebraicGeometry.Modules in
/-- The Hilbert-polynomial pieces follow from semicontinuity (SC), base-change invariance of fibre
dimensions (FE), cohomology of large twists on projective fibres (PT) and the fibre Hilbert
function of relative divisors (DH). -/
theorem picardHilbertPolynomialPiecesReduction :
    ProperFlatFibreCohomologySemicontinuityStatement.{u} →
      ProperFibreCohomologyDimBaseChangeStatement.{u} →
        ProjectiveFibreTwistCohomologyStatement.{u} →
          ProjectiveRelativeDivisorFibreHilbertStatement.{u} →
            PicardHilbertPolynomialPiecesStatement.{u} := by
  intro hSC hFE hPT hDH A _ _ X f 𝓛X hprop hflat hgi h𝓛 ⟨N, 𝔓, h𝔓⟩
  refine ⟨Polynomial ℚ × Polynomial ℚ, hilbertPolynomial, piece f 𝓛X, ?_, ?_, ?_, ?_, ?_⟩
  · -- twist invariance
    intro T _ s L L' M hL hL' hM ⟨e⟩ c m
    simp only [piece]
    rw [pieceSet_eq_of_iso (f := f) (𝓛X := 𝓛X) T s hM e c m]
  · -- base change
    intro T T' _ _ s h L hL c m
    have hS := isOpen_pieceSet hSC hPT hprop hflat h𝓛 h𝔓 T s hL c m
    have hS' := isOpen_pieceSet hSC hPT hprop hflat h𝓛 h𝔓 T' (h ≫ s) (Scheme.Modules.IsInvertible.pullbackFLT (hL := hL)
      (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))) c m
    ext x
    change x ∈ interior _ ↔ h x ∈ interior _
    rw [hS'.interior_eq, hS.interior_eq, pieceSet_baseChange hSC hFE hprop hflat h𝓛 s h hL c m]
    rfl
  · -- monotone, disjoint, covering
    intro T _ s L hL
    refine ⟨fun c m x hx ↦ interior_mono (pieceSet_mono f 𝓛X T s L c m) hx,
      fun c c' m m' hcc' ↦ ?_, ?_⟩
    · rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
        TopologicalSpace.Opens.coe_bot, ← Set.disjoint_iff_inter_eq_empty]
      exact Disjoint.mono interior_subset interior_subset
        (pieceSet_disjoint (f := f) (𝓛X := 𝓛X) T s L hcc' m m')
    · rw [eq_top_iff]
      intro t _
      obtain ⟨c, m, ht⟩ := exists_mem_pieceSet hPT hprop hflat h𝓛 h𝔓 T s hL t
      have hS := isOpen_pieceSet hSC hPT hprop hflat h𝓛 h𝔓 T s hL c m
      simp only [TopologicalSpace.Opens.mem_iSup]
      refine ⟨c, m, ?_⟩
      change t ∈ interior _
      rw [hS.interior_eq]
      exact ht
  · -- fibre cohomology on a whole piece
    intro T _ s L hL c m hU t
    have ht : t ∈ piece f 𝓛X T s L c m := by rw [hU]; trivial
    obtain ⟨-, -, hvan⟩ := interior_subset ht
    exact ⟨(hvan m le_rfl).1 1 Nat.one_pos, (hvan m le_rfl).2⟩
  · -- Hilbert polynomials of the divisors
    intro B _ _ s L hL c m hU I hI M hM ⟨eE⟩ k _ _ sk
    have ht : (Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k) ∈
        piece f 𝓛X _ s L c m := by rw [hU]; trivial
    obtain ⟨⟨M', -, ⟨eM'⟩, hφ⟩, hψ, -⟩ := interior_subset ht
    obtain ⟨n₀, hn₀⟩ := hDH A f 𝓛X N 𝔓 hprop hflat h𝓛 h𝔓 B s I hI k sk
    refine ⟨max n₀ m, fun n hn ↦ ?_⟩
    have hmn : m ≤ n := le_of_max_le_right hn
    let D : EffectiveCartierDivisor (pullback f s) := ⟨I, hI.1⟩
    have eK : StructureKernelModule.kernelModule I.subschemeι ⊗
        (twist (twistSheaf f 𝓛X _ s) L m ⊗
          (Scheme.Modules.pullback (pullback.snd f s)).obj M) ≅
          𝟙_ (pullback f s).Modules :=
      whiskerLeftIso _ eE.symm ≪≫ tensorDualIso D.idealLineBundle.obj D.idealLineBundle.property
    have hK := fibreEulerCharacteristic_twist_of_inverse (𝓛X := 𝓛X) _ s hM eM' m eK
      ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k)) (n - m)
    rw [Nat.sub_add_cancel hmn] at hK
    have hKn : ((fibreEulerCharacteristic (pullback.snd f s)
        ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
        (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X)
          (StructureKernelModule.kernelModule I.subschemeι) n) : ℤ) : ℚ) =
        c.1.eval ((n - m : ℕ) : ℚ) := by
      rw [← hφ (n - m)]
      exact congrArg (fun z : ℤ ↦ (z : ℚ)) hK
    have hψn : ((fibreEulerCharacteristic (pullback.snd f s)
        ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
        (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X)
          (𝟙_ (pullback f s).Modules) n) : ℤ) : ℚ) = c.2.eval (n : ℚ) := hψ n
    have hD := congrArg (fun z : ℤ ↦ (z : ℚ)) (hn₀ n (le_of_max_le_left hn))
    push_cast at hD
    refine hD.trans ((congrArg₂ (· - ·) hψn hKn).trans ?_)
    rw [hilbertPolynomial, Polynomial.eval_sub, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_sub hmn]

end Langlands.AlgebraicGeometry.Picard
