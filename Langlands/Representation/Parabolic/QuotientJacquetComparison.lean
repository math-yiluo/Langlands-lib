import Langlands.Representation.Parabolic.LeviModelTransport
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Aubert.AlternatingOperator

/-! The existing GL Jacquet action as an action of the actual parabolic quotient. -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The supplied positive Levi character on the actual quotient `P/U`. -/
def quotientModulus (δ : B.Levi F →* ℝ≥0ˣ) :
    B.parabolic F ⧸ B.unipotentRadical F →* ℝ≥0ˣ :=
  δ.comp (B.parabolicQuotientLevi F).toMonoidHom

@[simp] theorem quotientModulus_mk (δ : B.Levi F →* ℝ≥0ˣ) (g : B.parabolic F) :
    B.quotientModulus δ (QuotientGroup.mk g) = δ (B.leviProjection F g) := rfl

/-- Mathlib's genuine quotient action, normalized by the inverse positive half. -/
def normalizedQuotientJacquetOf (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) (B.JacquetModule ρ) :=
  twist (Jacquet.inverseHalfCharacter (B.quotientModulus δ))
    (Representation.quotientToCoinvariants (ρ.comp (B.parabolic F).subtype)
      (B.unipotentRadical F))

@[simp] theorem normalizedQuotientJacquetOf_mk (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) (g : B.parabolic F) (v : V) :
    B.normalizedQuotientJacquetOf δ ρ (QuotientGroup.mk g) (B.jacquetMk ρ v) =
      (Jacquet.inverseHalfCharacter δ (B.leviProjection F g) : ℂ) •
        B.jacquetMk ρ (ρ g v) := rfl

/-- The quotient action agrees with the unchanged product-Levi action on every
quotient vector, not merely on virtual classes. -/
theorem normalizedQuotientJacquetOf_eq (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    B.normalizedQuotientJacquetOf δ ρ =
      (B.normalizedJacquetOf δ ρ).comp (B.parabolicQuotientLevi F).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro x
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
    rw [normalizedQuotientJacquetOf_mk]
    change _ = B.normalizedJacquetOf δ ρ (B.leviProjection F g) (B.jacquetMk ρ v)
    rw [normalizedJacquetOf_mk, ← Jacquet.inverseHalfCharacter_apply]
    exact congrArg (fun x => (Jacquet.inverseHalfCharacter δ
      (B.leviProjection F g) : ℂ) • x)
      (Langlands.Parabolic.mk_action_eq_levi B (ρ.comp (B.parabolic F).subtype) g v)

/-- An actual ambient intertwiner descends through the actual radical quotient. -/
def normalizedQuotientJacquetOfMap (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (B.normalizedQuotientJacquetOf δ ρ).IntertwiningMap
      (B.normalizedQuotientJacquetOf δ τ) where
  toLinearMap := (B.normalizedJacquetOfMap δ f).toLinearMap
  isIntertwining' q := by
    rw [normalizedQuotientJacquetOf_eq, normalizedQuotientJacquetOf_eq]
    exact (B.normalizedJacquetOfMap δ f).isIntertwining'
      (B.parabolicQuotientLevi F q)

@[simp] theorem normalizedQuotientJacquetOfMap_mk (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) (v : V) :
    B.normalizedQuotientJacquetOfMap δ f (B.jacquetMk ρ v) =
      B.jacquetMk τ (f v) := rfl

@[simp] theorem normalizedQuotientJacquetOfMap_toLinearMap
    (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (B.normalizedQuotientJacquetOfMap δ f).toLinearMap =
      (B.normalizedJacquetOfMap δ f).toLinearMap := rfl

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem isSmooth_normalizedQuotientJacquetOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    {ρ : Representation ℂ (GeneralLinear n F) V} (hρ : IsSmooth ρ) :
    IsSmooth (B.normalizedQuotientJacquetOf δ ρ) := by
  rw [normalizedQuotientJacquetOf_eq]
  exact isSmooth_comp _ (B.parabolicQuotientLeviContinuous F).continuous
    (B.isSmooth_normalizedJacquetOf δ hδ hρ)

/-- The actual normalized quotient action, bundled with its proved smoothness. -/
abbrev normalizedQuotientJacquetObjectOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) :
    SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.of (B.normalizedQuotientJacquetOf δ A.representation)
    (B.isSmooth_normalizedQuotientJacquetOf δ hδ A.isSmooth)

/-- The quotient-Levi functor uses the genuine quotient action and descended maps. -/
def normalizedQuotientJacquetFunctorOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) :
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) where
  obj A := B.normalizedQuotientJacquetObjectOf δ hδ A
  map f := SmoothRep.ofHom (B.normalizedQuotientJacquetOfMap δ (SmoothRep.hom f))
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Representation.Coinvariants.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Representation.Coinvariants.hom_ext
    rfl

/-- The comparison is the identity on the actual quotient vector space. -/
def normalizedQuotientJacquetEquivOf (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    (B.normalizedQuotientJacquetOf δ ρ).Equiv
      ((B.normalizedJacquetOf δ ρ).comp (B.parabolicQuotientLevi F).toMonoidHom) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun q => by
    change B.normalizedQuotientJacquetOf δ ρ q =
      ((B.normalizedJacquetOf δ ρ).comp (B.parabolicQuotientLevi F).toMonoidHom) q
    rw [normalizedQuotientJacquetOf_eq]

/-- Natural comparison with the unchanged product-Levi functor and model transport. -/
def normalizedQuotientJacquetIsoOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) :
    B.normalizedQuotientJacquetFunctorOf δ hδ ≅
      B.normalizedJacquetFunctorOf δ hδ ⋙ Langlands.Parabolic.productToQuotientLevi B :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (B.normalizedQuotientJacquetEquivOf δ A.representation))
    fun f => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      rfl

@[simp] theorem normalizedQuotientJacquetIsoOf_hom_apply
    (δ : B.Levi F →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) (x : B.JacquetModule A.representation) :
    SmoothRep.hom ((B.normalizedQuotientJacquetIsoOf δ hδ).hom.app A) x = x := rfl

/-- Finite length of the product-Levi Jacquet functor transfers to the quotient. -/
theorem normalizedQuotientJacquetFunctorOf_preservesFiniteLength
    (δ : B.Levi F →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (hl : SmoothRep.PreservesFiniteLength
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ)) :
    SmoothRep.PreservesFiniteLength
      (B.normalizedQuotientJacquetFunctorOf.{uF, uV} δ hδ) := by
  intro A hA
  have h := (hl.comp (SmoothRep.pullbackFunctor_preservesFiniteLength
    (B.parabolicQuotientLeviContinuous F))) A hA
  change IsFiniteLength _
    (Representation.asModule ((B.normalizedJacquetOf δ A.representation).comp
      (B.parabolicQuotientLevi F).toMonoidHom)) at h
  exact (congrArg (fun ρ : Representation ℂ
    (B.parabolic F ⧸ B.unipotentRadical F) (B.JacquetModule A.representation) =>
      IsFiniteLength (MonoidAlgebra ℂ (B.parabolic F ⧸ B.unipotentRadical F))
        ρ.asModule) (B.normalizedQuotientJacquetOf_eq δ A.representation)).mpr h

/-- Exactness transfers because the quotient functor retains the linear maps. -/
theorem normalizedQuotientJacquetFunctorOf_preservesShortExact
    (δ : B.Levi F →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (hx : SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ)) :
    SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedQuotientJacquetFunctorOf.{uF, uV} δ hδ) := by
  intro A C D f g hA hC hD h
  obtain ⟨hi, hs, he⟩ := hx f g hA hC hD h
  exact ⟨hi, hs, he⟩

/-- The quotient Jacquet map on the existing exact finite-length K0. -/
def normalizedQuotientJacquetK0Of
    (δ : B.Levi F →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (hl : SmoothRep.PreservesFiniteLength
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ))
    (hx : SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ)) :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ (GeneralLinear n F) →ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ
        (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.FiniteLengthGrothendieckGroup.map
    (B.normalizedQuotientJacquetFunctorOf δ hδ)
    (B.normalizedQuotientJacquetFunctorOf_preservesFiniteLength δ hδ hl)
    (B.normalizedQuotientJacquetFunctorOf_preservesShortExact δ hδ hx)

/-- The full exact-K0 comparison follows from the actual natural isomorphism. -/
theorem normalizedQuotientJacquetK0Of_eq
    (δ : B.Levi F →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (hl : SmoothRep.PreservesFiniteLength
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ))
    (hx : SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ)) :
    B.normalizedQuotientJacquetK0Of δ hδ hl hx =
      (Langlands.Parabolic.quotientLeviK0Equiv B).toLinearMap.comp
        (SmoothRep.FiniteLengthGrothendieckGroup.map
          (B.normalizedJacquetFunctorOf δ hδ) hl hx) := by
  let e := B.parabolicQuotientLeviContinuous F
  have hpl := SmoothRep.pullbackFunctor_preservesFiniteLength.{uF, uF, uV} e
  have hpx := SmoothRep.pullbackFunctor_preservesShortExact.{uF, uF, uV} e
  unfold normalizedQuotientJacquetK0Of
  rw [SmoothRep.FiniteLengthGrothendieckGroup.map_eq_of_iso
    (B.normalizedQuotientJacquetIsoOf δ hδ) _ _ (hl.comp hpl)
    (SmoothRep.PreservesFiniteLengthShortExact.comp hl hx hpx)]
  exact SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _ hl hx hpl hpx _ _

end Topology

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem quotientJacquet_isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The actual p-adic quotient Jacquet functor with the existing block modulus. -/
def normalizedQuotientJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ
        (B.parabolic F.Carrier ⧸ B.unipotentRadical F.Carrier) :=
  letI := T.topology
  letI := quotientJacquet_isTopologicalRing F T
  B.normalizedQuotientJacquetFunctorOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

/-- The p-adic comparison is natural on every actual smooth representation. -/
def normalizedQuotientJacquetIso :
    letI := T.topology
    letI := quotientJacquet_isTopologicalRing F T
    normalizedQuotientJacquetFunctor.{uF, uV} F T B ≅
      T.normalizedJacquetFunctor B ⋙ productToQuotientLevi B :=
  letI := T.topology
  letI := quotientJacquet_isTopologicalRing F T
  B.normalizedQuotientJacquetIsoOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

/-- Finite length of the actual p-adic quotient Jacquet module is proved. -/
theorem normalizedQuotientJacquetK0_hasFiniteLength :
    letI := T.topology
    SmoothRep.PreservesFiniteLength
      (normalizedQuotientJacquetFunctor.{uF, max uF uV} F T B) := by
  let := T.topology
  let := quotientJacquet_isTopologicalRing F T
  exact B.normalizedQuotientJacquetFunctorOf_preservesFiniteLength
    (T.leviModulus B) (T.isOpen_ker_leviModulus B)
    (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B)

/-- The actual quotient Jacquet map, on the unchanged full exact GL K0. -/
def normalizedQuotientJacquetK0 :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (B.parabolic F.Carrier ⧸ B.unipotentRadical F.Carrier) :=
  letI := T.topology
  letI := quotientJacquet_isTopologicalRing F T
  B.normalizedQuotientJacquetK0Of (T.leviModulus B) (T.isOpen_ker_leviModulus B)
    (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B)
    (FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact F T B)

/-- The p-adic comparison holds as equality of maps on every exact class. -/
theorem normalizedQuotientJacquetK0_eq :
    letI := T.topology
    letI := quotientJacquet_isTopologicalRing F T
    normalizedQuotientJacquetK0.{uF, uV} F T B =
      (quotientLeviK0Equiv B).toLinearMap.comp
        (normalizedJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  let := quotientJacquet_isTopologicalRing F T
  exact B.normalizedQuotientJacquetK0Of_eq (T.leviModulus B)
    (T.isOpen_ker_leviModulus B)
    (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B)
    (FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact F T B)

/-- The quotient map sends every actual class to its actual quotient module. -/
theorem normalizedQuotientJacquetK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength)
      (hOut : ((normalizedQuotientJacquetFunctor F T B).obj A).HasFiniteLength),
      normalizedQuotientJacquetK0.{uF, uV} F T B
        (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
          SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
            ((normalizedQuotientJacquetFunctor F T B).obj A) hOut := by
  let := T.topology
  let := quotientJacquet_isTopologicalRing F T
  intro A hA hOut
  exact SmoothRep.FiniteLengthGrothendieckGroup.map_ofRepresentation
    (B.normalizedQuotientJacquetFunctorOf (T.leviModulus B)
      (T.isOpen_ker_leviModulus B))
    (B.normalizedQuotientJacquetFunctorOf_preservesFiniteLength
      (T.leviModulus B) (T.isOpen_ker_leviModulus B)
      (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B))
    (B.normalizedQuotientJacquetFunctorOf_preservesShortExact
      (T.leviModulus B) (T.isOpen_ker_leviModulus B)
      (FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact F T B))
    A hA

end Langlands.Parabolic
