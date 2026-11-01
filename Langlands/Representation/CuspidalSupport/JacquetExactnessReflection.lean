import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Exactness reflection by an actual detecting family of normalized Jacquet functors. -/

noncomputable section

namespace Langlands.CuspidalSupport.JacquetReflection

open CategoryTheory GeneralLinear Representation SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ}

/-- The family detects every nonzero actual smooth subquotient of `A`. -/
def DetectsSubquotients (P : BlockShape n → Prop) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun A => ∀ D, IsSubquotient D A → Nontrivial D →
    ∃ C, P C ∧ Nontrivial (C.JacquetModule D.representation)

/-- Detection passes to an actual subquotient, by actual subquotient transitivity. -/
theorem detects_subquotient (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ {A D : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)},
      DetectsSubquotients F T P A → IsSubquotient D A →
      DetectsSubquotients F T P D := by
  let := T.topology
  intro A D hA hDA E hED hE
  exact hA E (smoothSubquotientTransitivity ℂ _ A D E hED hDA) hE

/-- The associated-Levi family concretely detects all subquotients of actual
quasicuspidal induction. No irreducibility hypothesis is needed here. -/
theorem detects_cuspidalInduction (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      DetectsSubquotients.{uF,max uF uV} F T
        (LevisAssociated (F := F.Carrier) B)
        ((T.normalizedParabolicInductionFunctor B).obj σ) := by
  let := T.topology
  intro σ hσ D hD hne
  obtain ⟨C, hBC, hJ, _⟩ :=
    cuspidalInductionSubquotientJacquet F T n B σ hσ D hD hne
  exact ⟨C, hBC, hJ⟩

/-- A detected actual subquotient whose Jacquet modules in the family all
vanish has a zero carrier. -/
theorem subsingleton_of_vanishing (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ {A D : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)},
      DetectsSubquotients F T P A → IsSubquotient D A →
      (∀ C, P C → Subsingleton (C.JacquetModule D.representation)) →
      Subsingleton D := by
  let := T.topology
  intro A D hA hD hzero
  by_contra h
  have hne : Nontrivial D := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨C, hC, hJC⟩ := hA D hD hne
  exact not_nontrivial_iff_subsingleton.mpr (hzero C hC) hJC

/-- An injection into a smooth representation descends injectively to every
actual normalized Jacquet quotient. -/
private theorem jacquet_injective :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ B), Function.Injective (hom f) →
      ∀ C, Function.Injective (T.normalizedJacquetMap C (hom f)) := by
  let := T.topology
  intro A B f hf C
  exact JacquetDetectingFamilyLengthProof.jacquet_injective T C (hom f) hf

/-- Injectivity on a detecting Jacquet family reflects injectivity of the
actual smooth intertwiner. -/
theorem injective_of_jacquet (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ B),
      DetectsSubquotients F T P A →
      (∀ C, P C → Function.Injective (T.normalizedJacquetMap C (hom f))) →
      Function.Injective (hom f) := by
  let := T.topology
  intro A B f hA hf
  have hK : IsSubquotient (kernel f) A :=
    (subrepresentation_isSubrepresentation (hom f).ker).isSubquotient
  have hzero : ∀ C, P C → Subsingleton (C.JacquetModule (kernel f).representation) := by
    intro C hC
    have hi := jacquet_injective F T (kernelι f) (subtype_injective _ _) C
    have hz (x : C.JacquetModule (kernel f).representation) : x = 0 := by
      apply hi
      apply hf C hC
      obtain ⟨v, rfl⟩ := C.jacquetMk_surjective (kernel f).representation x
      change C.jacquetMk B.representation (hom f v.val) =
        T.normalizedJacquetMap C (hom f)
          (T.normalizedJacquetMap C (hom (kernelι f)) 0)
      have hv : hom f v.val = 0 := v.property
      rw [hv, map_zero, map_zero, map_zero]
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  have hsub : Subsingleton (kernel f) :=
    subsingleton_of_vanishing F T P hA hK hzero
  let : Subsingleton (hom f).ker.toSubmodule := hsub
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : (hom f).ker.toSubmodule) 0)

/-- The actual map out of the quotient by the preceding range. -/
def cokernelDesc :
    letI := T.topology
    ∀ {A B D : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ B) (g : B ⟶ D)
      (_hfg : (hom g).comp (hom f) = 0), cokernel f ⟶ D :=
  letI := T.topology
  fun f g hfg => ofHom {
    toLinearMap := (hom f).range.toSubmodule.liftQ (hom g).toLinearMap (by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun h => h v) hfg)
    isIntertwining' a := by
      apply Submodule.linearMap_qext
      ext v
      exact IntertwiningMap.isIntertwining _ _ (hom g) a v }

/-- The descended map composed with the actual quotient projection is the
original outgoing map. -/
theorem cokernelDesc_mk :
    letI := T.topology
    ∀ {A B D : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ B) (g : B ⟶ D) (hfg : (hom g).comp (hom f) = 0) (v : B),
      hom (cokernelDesc F T f g hfg) (hom (cokernelπ f) v) = hom g v := by
  intros
  rfl

/-- Exactness on a detecting Jacquet family reflects range-kernel exactness
of the actual smooth short complex. -/
theorem exact_of_jacquet (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ {A B D : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : A ⟶ B) (g : B ⟶ D) (_hfg : (hom g).comp (hom f) = 0),
      DetectsSubquotients F T P B →
      (∀ C, P C →
        LinearMap.range (T.normalizedJacquetMap C (hom f)).toLinearMap =
          LinearMap.ker (T.normalizedJacquetMap C (hom g)).toLinearMap) →
      LinearMap.range (hom f).toLinearMap = LinearMap.ker (hom g).toLinearMap := by
  let := T.topology
  intro A B D f g hfg hB hex
  let q := cokernelπ f
  let t := cokernelDesc F T f g hfg
  have hQ : DetectsSubquotients F T P (cokernel f) :=
    detects_subquotient F T P hB
      (quotient_isQuotient (hom f).range).isSubquotient
  have ht : Function.Injective (hom t) := by
    apply injective_of_jacquet F T P t hQ
    intro C hC
    have hq : Function.Surjective (T.normalizedJacquetMap C (hom q)) := by
      change Function.Surjective (T.normalizedJacquetMap C (hom q)).toLinearMap
      rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
      exact coinvariants_map_surjective _ (mkQ_surjective _ _)
    have hqker :
        LinearMap.range (T.normalizedJacquetMap C (hom f)).toLinearMap =
          LinearMap.ker (T.normalizedJacquetMap C (hom q)).toLinearMap := by
      rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap,
        T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
      have he : LinearMap.range (hom f).toLinearMap =
          LinearMap.ker (hom q).toLinearMap := (Submodule.ker_mkQ _).symm
      exact coinvariants_map_range_eq_ker
        (Jacquet.restrictMap (Jacquet.restrictMap (hom f) (C.parabolic F.Carrier))
          (C.unipotentRadical F.Carrier))
        (Jacquet.restrictMap (Jacquet.restrictMap (hom q) (C.parabolic F.Carrier))
          (C.unipotentRadical F.Carrier))
        (mkQ_surjective B (hom f).range) he
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hq x
    have hcomm :
        T.normalizedJacquetMap C (hom t) (T.normalizedJacquetMap C (hom q) y) =
          T.normalizedJacquetMap C (hom g) y := by
      obtain ⟨v, rfl⟩ := C.jacquetMk_surjective B.representation y
      rfl
    change T.normalizedJacquetMap C (hom t)
      (T.normalizedJacquetMap C (hom q) y) = 0 at hx
    rw [hcomm] at hx
    have hy : y ∈ LinearMap.range (T.normalizedJacquetMap C (hom f)).toLinearMap := by
      rw [hex C hC]
      exact hx
    rw [hqker] at hy
    exact hy
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact congrArg (fun h => h x) hfg
  · intro hv
    have hqv : hom q v = 0 := ht (by
      rw [cokernelDesc_mk F T f g hfg, map_zero]
      exact hv)
    exact (Submodule.Quotient.mk_eq_zero (hom f).range.toSubmodule).mp hqv

end Langlands.CuspidalSupport.JacquetReflection
