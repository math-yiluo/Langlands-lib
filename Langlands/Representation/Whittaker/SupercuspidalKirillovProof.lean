import Langlands.Representation.Whittaker.KirillovStatement
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof
import Langlands.Representation.Whittaker.MirabolicKirillovAdapters
import Langlands.Analysis.Local.QuotientTopology

/-!
# The supercuspidal Kirillov model

Prove the published `SupercuspidalKirillovStatement` by derivative detection,
irreducibility of the mirabolic restriction, and compact minimality.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Whittaker.SupercuspidalKirillovProof

open GeneralLinear HarmonicAnalysis Derivative

universe uF uV

private theorem subsingleton_subquotient
    {G : Type*} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0,_,uV} ℂ G} (h : SmoothRep.IsSubquotient B A)
    (hz : Subsingleton A) : Subsingleton B := by
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  have hX : Subsingleton X := ⟨fun x y => hi (hz.elim _ _)⟩
  exact ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hq b
    exact congrArg (SmoothRep.hom q) (hX.elim x y)⟩

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

private theorem cast_mapsShortExact {a b : ℕ} (h : a = b) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (mirabolicRankCast.{uF,uV} T h) := by
  let := T.topology
  subst h
  exact LevelCalculus.mapsShortExact_id

private theorem restriction_rankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      (mirabolicRankCast T h).obj ((generalLinearRestriction T a).obj A) =
        (generalLinearRestriction T b).obj
          ((generalLinearRankCast T (congrArg (· + 1) h)).obj A) := by
  subst h
  intro A
  rfl

/-- A lower derivative of the mirabolic restriction of a supercuspidal module vanishes. -/
theorem lower_restriction {N m j : ℕ} (h : N = m + j) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      IsSupercuspidal A.representation →
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ m j).obj
        ((generalLinearRestriction T N).obj A)) := by
  subst h
  intro A hA
  exact Classification.SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivativePositive
    T ψ m j hm A hA

/-- If lower derivatives vanish on `X`, the top derivative detects zero on all
actual subquotients of `X`. -/
theorem detect_subquotient (N : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0,uF,uV} ℂ (mirabolic N F.Carrier),
      (∀ m j (h : N = m + j), 0 < m →
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ m j).obj X)) →
      ∀ B : SmoothRep.{0,uF,uV} ℂ (mirabolic N F.Carrier),
        SmoothRep.IsSubquotient B X →
        Subsingleton ((mirabolicRankCast T (Nat.zero_add N).symm ⋙
          mirabolicDerivative T ψ 0 N).obj B) → Subsingleton B := by
  let := T.topology
  intro X hX B hBX htop
  apply Mirabolic.subsingleton_of_forall_mirabolicDerivative T ψ N B
  intro m j h
  by_cases hm : m = 0
  · subst m
    have hj : j = N := by omega
    subst j
    exact htop
  · let D := mirabolicRankCast.{uF,uV} T h ⋙ mirabolicDerivative T ψ m j
    have hD : Mirabolic.MapsShortExactIntertwiners D :=
      LevelCalculus.mapsShortExact_comp (cast_mapsShortExact T h)
        (mirabolicDerivative_mapsShortExact F T ψ m j)
    exact subsingleton_subquotient (ExactSmoothTransport.map_isSubquotient D hD hBX)
      (hX m j h (Nat.pos_of_ne_zero hm))

/-- A one-dimensional top derivative and vanishing lower derivatives force
irreducibility, without a finite-length assumption. -/
theorem irreducible_of_derivatives (N : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0,uF,uV} ℂ (mirabolic N F.Carrier),
      (∀ m j (h : N = m + j), 0 < m →
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ m j).obj X)) →
      Module.finrank ℂ ((mirabolicRankCast T (Nat.zero_add N).symm ⋙
        mirabolicDerivative T ψ 0 N).obj X) = 1 → X.IsIrreducible := by
  let := T.topology
  intro X hlower hdim
  let J := mirabolicRankCast.{uF,uV} T (Nat.zero_add N).symm ⋙ mirabolicDerivative T ψ 0 N
  have hJ : Mirabolic.MapsShortExactIntertwiners J :=
    LevelCalculus.mapsShortExact_comp (cast_mapsShortExact T _)
      (mirabolicDerivative_mapsShortExact F T ψ 0 N)
  have : (J.obj X).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one (J.obj X) hdim
  have hJne : Nontrivial (J.obj X) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear 0 F.Carrier))
      (J.obj X).representation.asModule
  have hne : (⊥ : Subrepresentation X.representation) ≠ ⊤ := by
    intro h
    have : Subsingleton X := ⟨fun a b => by
      have hz (v : X) : v = 0 := by
        have hv : v ∈ (⊥ : Subrepresentation X.representation) := by rw [h]; trivial
        exact hv
      exact (hz a).trans (hz b).symm⟩
    exact (not_nontrivial_iff_subsingleton.mpr
      (ExactFunctorIrreducibility.obj_subsingleton J hJ X)) hJne
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  let K := X.subrepresentation S
  let Q := X.quotient S
  have hKX : SmoothRep.IsSubquotient K X :=
    (X.subrepresentation_isSubrepresentation S).isSubquotient
  have hQX : SmoothRep.IsSubquotient Q X := (X.quotient_isQuotient S).isSubquotient
  have he := hJ K X Q (X.subtype S) (X.mkQ S)
    (X.subtype_injective S) (X.mkQ_surjective S)
    (by
      change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
  by_cases hz : Subsingleton (J.obj K)
  · left
    have hzero := detect_subquotient T ψ N X hlower K hKX hz
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    exact congrArg Subtype.val (hzero.elim (⟨a, ha⟩ : K) 0)
  · right
    have hi0 : SmoothRep.hom (J.map (X.subtype S)) ≠ 0 := by
      intro hi
      apply hz
      exact ⟨fun a b => he.1 (by simp [hi])⟩
    have hi := (Representation.IsIrreducible.surjective_or_eq_zero
      (SmoothRep.hom (J.map (X.subtype S)))).resolve_right hi0
    have hq0 (a : J.obj X) : SmoothRep.hom (J.map (X.mkQ S)) a = 0 := by
      have ha : a ∈ LinearMap.range (SmoothRep.hom (J.map (X.subtype S))).toLinearMap := hi a
      rw [he.2.1] at ha
      exact ha
    have hzeroJ : Subsingleton (J.obj Q) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := he.2.2 a
      obtain ⟨b, rfl⟩ := he.2.2 b
      rw [hq0 a, hq0 b]⟩
    have hzero := detect_subquotient T ψ N X hlower Q hQX hzeroJ
    apply le_antisymm le_top
    intro a _
    exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
      (hzero.elim (SmoothRep.hom (X.mkQ S) a) 0)

include ψ in
/-- The restriction of an irreducible supercuspidal representation to the actual
mirabolic subgroup is irreducible (BZ76, Theorem 5.18). -/
theorem irreducible_restriction (N : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
      ((generalLinearRestriction T N).obj A).IsIrreducible := by
  let := T.topology
  intro A hirr hsc
  apply irreducible_of_derivatives T ψ N _ (fun m j h hm => lower_restriction T ψ h hm A hsc)
  rw [Functor.comp_obj, restriction_rankCast T (Nat.zero_add N).symm]
  exact Classification.SupercuspidalDerivativesProof.finrank_generalLinearDerivativePositive_top
    T ψ N _
    (Classification.SupercuspidalTopDerivative.isIrreducible_rankCast T _ A hirr)
    (Classification.SupercuspidalDerivativeVanishing.isSupercuspidal_rankCast T _ A hsc)

/-- Pull back a nonzero dual vector along the surjective top derivative quotient. -/
theorem exists_functional_zero (N : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (0 + N + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
      ∃ ℓ : glFunctionals ψ (0 + N) A.representation, ℓ.val ≠ 0 := by
  let := T.topology
  intro A hirr hsc
  have hD := Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivativePositive_top
    T ψ N A hsc
    (Classification.SupercuspidalTopDerivative.nontrivial_of_isIrreducible A.representation hirr)
  obtain ⟨x, hx⟩ := exists_ne (0 : (generalLinearDerivativePositive T ψ 0 N).obj A)
  obtain ⟨f, hf⟩ := not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff ℂ x).mp hx)
  refine ⟨⟨f ∘ₗ Classification.SupercuspidalTopDerivative.topQuotient T ψ N A,
    Classification.SupercuspidalTopDerivative.comp_topQuotient_mem_glFunctionals T ψ N A f⟩, ?_⟩
  intro hz
  obtain ⟨v, hv⟩ := Classification.SupercuspidalTopDerivative.topQuotient_surjective T ψ N A x
  exact hf (by
    rw [← hv]
    exact LinearMap.congr_fun hz v)

/-- Genericity is preserved when an equality transports the matrix rank. -/
private theorem exists_functional_rankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      (∃ ℓ : glFunctionals ψ b
        ((generalLinearRankCast T (congrArg (· + 1) h)).obj A).representation, ℓ.val ≠ 0) →
      ∃ ℓ : glFunctionals ψ a A.representation, ℓ.val ≠ 0 := by
  subst h
  exact fun _ h => h

/-- Every irreducible supercuspidal smooth representation is generic. -/
theorem exists_functional (N : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
      ∃ ℓ : glFunctionals ψ N A.representation, ℓ.val ≠ 0 := by
  let := T.topology
  intro A hirr hsc
  apply exists_functional_rankCast T ψ (Nat.zero_add N).symm A
  exact exists_functional_zero T ψ N _
    (Classification.SupercuspidalTopDerivative.isIrreducible_rankCast T _ A hirr)
    (Classification.SupercuspidalDerivativeVanishing.isSupercuspidal_rankCast T _ A hsc)

/-- Compact projected support has a compact witness in the ambient matrix group. -/
theorem ambient_compact_support
    {E : Type uF} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    {n : ℕ} [LocallyCompactSpace (mirabolic n E)]
    (Ψ : UnitaryAdditiveCharacter E) (f : MirabolicSmoothFunctions Ψ n)
    (hf : f ∈ mirabolicCompactSubrepresentation Ψ n) :
    ∃ C : Set (GeneralLinear (n + 1) E), IsCompact C ∧
      ∀ q : mirabolic n E, mirabolicEval Ψ n f q ≠ 0 →
        ∃ (u : upperUnipotent (n + 1) E) (c : GeneralLinear (n + 1) E),
          c ∈ C ∧ q.val = u.val * c := by
  obtain ⟨C, hC, himage⟩ :=
    QuotientIntegration.leftQuotient_exists_isCompact_image
      (Mirabolic.upperUnipotent n E) Mirabolic.upperUnipotent_isClosed hf
  change Induction.quotientMap (Mirabolic.upperUnipotent n E) '' C =
    Induction.quotientSupport (Mirabolic.upperUnipotent n E) (mirabolicEval Ψ n f) at himage
  refine ⟨Subtype.val '' C, hC.image continuous_subtype_val, ?_⟩
  intro q hq
  have hqx : Induction.quotientMap (Mirabolic.upperUnipotent n E) q ∈
      Induction.quotientSupport (Mirabolic.upperUnipotent n E) (mirabolicEval Ψ n f) :=
    ⟨q, hq, rfl⟩
  rw [← himage] at hqx
  obtain ⟨c, hc, he⟩ := hqx
  have hu := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  change q.val * c.val⁻¹ ∈ upperUnipotent (n + 1) E at hu
  exact ⟨⟨q.val * c.val⁻¹, hu⟩, c.val, ⟨c, hc, rfl⟩, by simp⟩

end Langlands.Whittaker.SupercuspidalKirillovProof

namespace Langlands

open GeneralLinear HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV

/-- The supercuspidal Kirillov model, including genericity, compact support, and
uniqueness of the vector realizing every smooth compact mirabolic function. -/
theorem supercuspidalKirillov : SupercuspidalKirillovStatement.{uF,uV} := by
  intro p hp F
  let := hp
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro n V _ _ ρ ψ hc hne hu hsc hirr
  let : NonarchimedeanGroup (GeneralLinear (n + 1) F.Carrier) :=
    Langlands.valuativeGeneralLinearNonarchimedean F.Carrier (n + 1)
  let : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (n + 1)
  let : LocallyCompactSpace (mirabolic n F.Carrier) := Mirabolic.locallyCompactSpace
  let Ψ := UnitaryAdditiveCharacter.ofComplex ψ hc hne hu
  let A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier) := SmoothRep.of ρ hsc.1.1
  dsimp only
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := Whittaker.SupercuspidalKirillovProof.exists_functional T Ψ n A hirr hsc
    refine ⟨L.val, hL, ?_⟩
    intro g hg v
    have h := (mem_glFunctionals_iff_entrywise Ψ ρ L.val).mp L.property
      g (fun _ _ hij => hg.1 _ _ hij) hg.2 v
    exact h
  · intro ℓ hℓ hcov
    have hL : ℓ ∈ glFunctionals Ψ n ρ := by
      apply (mem_glFunctionals_iff_entrywise Ψ ρ ℓ).mpr
      intro g hlow hdiag v
      exact hcov g ⟨hlow, hdiag⟩ v
    let L : glFunctionals Ψ n ρ := ⟨ℓ, hL⟩
    have : Representation.IsIrreducible (ρ.comp (mirabolic n F.Carrier).subtype) :=
      Whittaker.SupercuspidalKirillovProof.irreducible_restriction T Ψ n A hirr hsc
    let B := mirabolicCoefficientMap Ψ ρ hsc.1.1 L
    have hB : B.range ≠ ⊥ := mirabolicCoefficientImage_ne_bot Ψ ρ hsc.1.1 L hℓ
    have hcompactne : ∃ f : MirabolicCompactFunctions Ψ n, f ≠ 0 := by
      obtain ⟨f, hf⟩ := exists_mirabolicCompactEval_one_ne_zero Ψ (n := n)
      exact ⟨f, fun hz => hf (by rw [hz]; rfl)⟩
    have hBrange : B.range = mirabolicCompactSubrepresentation Ψ n :=
      range_eq_mirabolicCompact Ψ (mirabolicCompactMinimality p hp F n Ψ) hcompactne B hB
    have hB0 : B ≠ 0 := by
      intro hz
      apply hℓ
      ext v
      have hv := congrArg (fun f => mirabolicEval Ψ n f 1) (congrArg (fun f => f v) hz)
      change ℓ (ρ 1 v) = 0 at hv
      simpa only [map_one, Module.End.one_apply, LinearMap.zero_apply] using hv
    have hBinj : Function.Injective B :=
      (Representation.IsIrreducible.injective_or_eq_zero B).resolve_right hB0
    refine ⟨?_, ?_⟩
    · intro v
      refine ⟨?_, ?_, ?_⟩
      · intro u q hu _hq
        rw [map_mul, Module.End.mul_apply]
        exact hcov u hu (ρ q v)
      · obtain ⟨K, hK⟩ := hsc.1.1 v
        refine ⟨K, ?_⟩
        intro q k _hq _hk hk
        rw [map_mul, Module.End.mul_apply]
        have hkfix : ρ k v = v := hK ⟨k, hk⟩
        rw [hkfix]
      · have hv : B v ∈ mirabolicCompactSubrepresentation Ψ n := by
          rw [← hBrange]
          exact ⟨v, rfl⟩
        obtain ⟨C, hC, hsupport⟩ :=
          Whittaker.SupercuspidalKirillovProof.ambient_compact_support Ψ (B v) hv
        refine ⟨C, hC, ?_⟩
        intro q hq hnq
        obtain ⟨u, c, hcC, he⟩ := hsupport ⟨q, hq⟩ hnq
        exact ⟨u.val, c, ⟨fun _ _ hij => u.property.1 hij, u.property.2⟩, hcC, he⟩
    · intro φ hφ
      obtain ⟨hφcov, ⟨K, hK⟩, ⟨C, hC, hsupp⟩⟩ := hφ
      have hφcov' : ∀ (u : upperUnipotent (n + 1) F.Carrier)
          (q : mirabolic n F.Carrier),
          φ (u.val * q.val) = (standardCharacter Ψ n u : ℂ) * φ q.val := by
        intro u q
        rw [standardCharacter_eq_product]
        exact hφcov u.val q.val
          ⟨fun _ _ hij => u.property.1 hij, u.property.2⟩ q.property
      have hK' : ∀ (q k : mirabolic n F.Carrier),
          k.val ∈ K → φ (q.val * k.val) = φ q.val := by
        intro q k hk
        exact hK q.val k.val q.property k.property hk
      have hsupp' : ∀ q : mirabolic n F.Carrier, φ q.val ≠ 0 →
          ∃ (u : upperUnipotent (n + 1) F.Carrier)
            (c : GeneralLinear (n + 1) F.Carrier),
            c ∈ C ∧ q.val = u.val * c := by
        intro q hq
        obtain ⟨u, c, hu, hc, he⟩ := hsupp q.val q.property hq
        exact ⟨⟨u, ⟨fun _ _ hij => hu.1 _ _ hij, hu.2⟩⟩, c, hc, he⟩
      let f := mirabolicCompactRestriction Ψ n φ hφcov' K hK' C hC hsupp'
      obtain ⟨v, hv⟩ := (show f.val ∈ B.range by rw [hBrange]; exact f.property)
      have hvφ : ∀ q, q ∈ mirabolic n F.Carrier → ℓ (ρ q v) = φ q := by
        intro q hq
        exact congrArg (fun g => mirabolicEval Ψ n g ⟨q, hq⟩) hv
      refine ⟨v, hvφ, ?_⟩
      intro w hw
      apply hBinj
      apply Subtype.ext
      apply Subtype.ext
      funext q
      exact (hw q.val q.property).trans (hvφ q.val q.property).symm

end Langlands
